from binaryninja import LowLevelILOperation
from binaryninja import MediumLevelILOperation
from binaryninja import log_debug, log_info
from binaryninja import function, variable, mediumlevelil, lowlevelil

from collections import deque

from .utils import debug_print, DEBUG

# The following functions won't be added to the callgraph while building in `G.build_graph()`
GRAPH_SKIP_FUNCTION = [
    'malloc', 'free', 'calloc', 'realloc', 'snprintf', 'sscanf',
    '__stack_chk_fail', '__stack_chk_fail_local', '__libc_fatal', '__assert_fail', '__chk_fail', 
    '__libc_message', 'abort', 'raise', '_IO_vtable_check'
]
GRAPH_SKIP_FUNCTION += list(map(lambda x : "__GI_" + x, GRAPH_SKIP_FUNCTION)) # alias name in debug symbol

# This dict maps LowLevelILOperation type to the name of a method in `LowLevelILFunction` object
#   which can be used to create expression with the inverted operation
# (See `_resolve_branch_condition()` method in `LibIOFuncTaintTracker` class)
COND_INVERT_FUNC_MAP = {
    LowLevelILOperation.LLIL_CMP_E   : 'compare_not_equal',
    LowLevelILOperation.LLIL_CMP_NE  : 'compare_equal',
    LowLevelILOperation.LLIL_CMP_SGE : 'compare_signed_less_than',
    LowLevelILOperation.LLIL_CMP_SGT : 'compare_signed_less_equal',
    LowLevelILOperation.LLIL_CMP_SLE : 'compare_signed_greater_than',
    LowLevelILOperation.LLIL_CMP_SLT : 'compare_signed_greater_equal',
    LowLevelILOperation.LLIL_CMP_UGE : 'compare_unsigned_less_than',
    LowLevelILOperation.LLIL_CMP_UGT : 'compare_unsigned_less_equal',
    LowLevelILOperation.LLIL_CMP_ULE : 'compare_unsigned_greater_than',
    LowLevelILOperation.LLIL_CMP_ULT : 'compare_unsigned_greater_equal',
    LowLevelILOperation.LLIL_FCMP_E  : 'float_compare_not_equal',
    LowLevelILOperation.LLIL_FCMP_NE : 'float_compare_equal',
    LowLevelILOperation.LLIL_FCMP_GE : 'float_compare_signed_less_than',
    LowLevelILOperation.LLIL_FCMP_GT : 'float_compare_signed_less_equal',
    LowLevelILOperation.LLIL_FCMP_LE : 'float_compare_signed_greater_than',
    LowLevelILOperation.LLIL_FCMP_LT : 'float_compare_signed_greater_equal',
    LowLevelILOperation.LLIL_FCMP_O  : 'float_compare_unordered',
    LowLevelILOperation.LLIL_FCMP_UO : 'float_compare_ordered',
}

#### Global Options for `LibIOFuncTaintTracker` ###
##  1) TRACK_RBP: Enable RBP/EBP dataflow tracking (Default: True)
##    Note that this functionlity is only available on i386/x64, 
##    so this option will be ignored on other architectures.
TRACK_RBP = True
##  2) ALLOW_CALL_BLOCKS: Allow basic blocks with call/jmp instructions to be used in taint tracking 
##    (Default: False)
##    Enable it if you are looking for FSOP code paths 
##      that can trigger some function calls like malloc()/free()/memcpy().
ALLOW_CALL_BLOCKS = False
##  3) DEFAULT_TAINT_ARG_IDX: The index of function arguments used as taint source (Default: [0])
##    In other words, these arguments are controllable during FSOP attack.
##    If the pointer of an indirect call inside the function (or sink instruction) is 
##      tainted by one of taint source, the taint tracking process will be marked as succeed, 
##      which means we found a RIP-hijackable code path.
##    Some examples (x64):
##       [0]      : Only first argument is controllable, 
##                    which is `rdi` register and also `fp` argument in the most of libio functions.
##       [0, 1, 3]: First, second and fourth argument are controllable (`rdi`, `rsi` and `rcx`).
##    The indexes greater than the number of function arguments will be ignored.
DEFAULT_TAINT_ARG_IDX = [0]
##  4) DEFAULT_SINK_CALLARG_IDX: The index of sink instruction arguments used as taint sink 
##     (Default: same as `DEFAULT_TAINT_ARG_IDX`)
##     If call chain contains more than one functions, 
##       sink instruction may be the call to next hop function rather than an indirect call.
##     In this case, we must make sure that some of sink call arguments are tainted
##       so taint source can be passed to next hop.
DEFAULT_SINK_CALLARG_IDX = DEFAULT_TAINT_ARG_IDX

### Global Options for `LibIOVtableFuncCallGraph` ###
##  1) MAX_CHAIN_LEN: The maxmiun length of call chain (Default: 10)
##    It's also maxmiun DFS depth can be reached while generating call chains in `_visit_graph()`.
MAX_CHAIN_LEN = 10

class LibIOFunc:
    def __init__(self, bv, func: function.Function, taint_arg_idx=DEFAULT_TAINT_ARG_IDX):
        '''' `LibIOFunc` class represents a GLIBC LibIO function (`_IO_*`)
        
            bv  : Binaryview
            func: The `function.Function` object of the function to be represented
                    Everything we need to know will be learned via this object.
            taint_arg_idx: Used by `find_indirect_call` method to find hijackable indirect calls
                    inside represeting function using taint analysis        
        '''
        
        self.bv = bv
        
        self.func = func
        self.addr = self.func.start
        self.name = f"{func.name}@{hex(self.addr)}"
        
        # A "root node" refers to a LibIO function in callgraph that belongs to
        #   one of vtables inside the `__libc_IO_vtables` section. 
        # For example: `_IO_str_overflow`, which is one of members in `_IO_str_jump` vtable.
        # (I'm not sure whether it's proper to use the term "root" in a graph, anyway XD)
        self.is_root_node = False
        
        # The edges in callgraph (`function.Function` => `LibIOFunc`)
        self.callers = {}
        self.callees = {}
        
        self.taint_arg_idx = taint_arg_idx
        self.taint_arg = [
            self.func.parameter_vars[idx] 
                for idx in filter(lambda x : x < len(self.func.parameter_vars), self.taint_arg_idx)
        ]
        
        if self.func.medium_level_il:
            self.mlil_func = self.func.medium_level_il.ssa_form
        else:
            # MIIL unavailable, possibly the function is too huge or broken.
            self.mlil_func = None

        # For root node, the list of pointers to represeting LibIO function
        #   in `__libc_IO_vtables` section.
        self.vtable_locations = []
        
        # This list stores `LibIOFuncTaintTracker` objects with succeed state 
        #  which contains the information (i.e. code path) of a hijackable indirect call.
        # Used by `_visited_var()` (call by `process()`) 
        self.succeed_trackers = []
        
        # The list of basic blocks which won't be visited during taint tracking
        #  `find_protection()` will add protection-enabled blocks to this list.
        self.avoid_blocks = []
        
        self._var_visited = []

    def add_caller(self, caller):
        self.callers[caller.func] = caller

    def add_callee(self, callee):
        self.callees[callee.func] = callee

    def set_as_root(self):
        self.is_root_node = True
    
    def is_root(self):
        return self.is_root_node
        
    def has_indirect_calls(self):
        return len(self.succeed_trackers) > 0

    def find_protection(self, vtable_validate_func: function.Function = None):
        ''' Find basic blocks with protection (IO_validate_vtable and PointerEncryption) enabled, 
              then add them to `self.avoid_blocks` list
        
            vtable_validate_func: A `function.Function` object of `_IO_vtable_check()`. 
              If None, IO_validate_vtable blocks won't be detected.
        '''
        bv = self.bv
        if len(self.avoid_blocks) > 0 or not self.mlil_func:
            return
        # 1. Find IO_validate_vtable blocks
        # IO_validate_vtable is the vtable pointer validation mostly used in LibIO, 
        #    works by checking `fp->vtable` whether it's within `__libc_IO_vtables` section
        # (See https://code.woboq.org/userspace/glibc/libio/libioP.h.html#IO_validate_vtable)
        if vtable_validate_func:
            for refs in bv.get_code_refs(vtable_validate_func.start):
                # Find the blocks that calls `_IO_vtable_check()` in current function 
                if refs.function == self.func:
                    call_check_func = self.func.get_low_level_il_at(refs.address).medium_level_il.ssa_form
                    # Also add the block where vtable pointer check is performed
                    check_vtable_range = call_check_func.il_basic_block.incoming_edges[0].source
                    self.avoid_blocks.extend([check_vtable_range, call_check_func])
        # 2. Find PointerEncryption blocks
        # PointerEncryption is another security feature used by few IO vtable functions such as `_IO_cookie_*`.
        #   It works by XORing the function pointer with a secret key called `__pointer_chk_guard`
        # (See https://sourceware.org/glibc/wiki/PointerEncryption)
        for block in self.mlil_func:
            for instr in block:
                if instr.operation != MediumLevelILOperation.MLIL_SET_VAR_SSA:
                    continue
                # non-i386/x64: XOR `__pointer_chk_guard` directly
                if bv.arch.name not in ['x86', 'x86_64']:
                    #  00069514  int64_t _IO_cookie_close(void* arg1)
                    #     [...]
                    #     1 @ 00069520  x1#1 = [__pointer_chk_guard].q @ mem#0
                    #     2 @ 00069524  x3#1 = x1#1 ^ x2#1
                    #     [...]
                    #     7 @ 00069534  x16#1 = x3#1
                    #     8 @ 00069538  jump(x16#1)
                    if instr.instruction_operands[0].operation == MediumLevelILOperation.MLIL_LOAD_SSA and \
                       any(['__pointer_chk_guard' in tkn.text for tkn in instr.instruction_operands[0].tokens]):
                            self.avoid_blocks.append(block)
                            break
                # i386/x64: ROR then XOR `__pointer_chk_guard` pointed by `fs/gs` register
                else:
                    reg_offset = 0x30   if bv.arch.name == 'x86_64' else 0x18
                    ror_bits = 0x11     if bv.arch.name == 'x86_64' else 0x9
                    reg_name = 'fsbase' if bv.arch.name == 'x86_64' else 'gsbase'
                    #  0007f8c0  int64_t _IO_cookie_close(void* arg1)
                    #     [...]
                    #     1 @ 0007f8cb  rax_1#2 = ror.q(rax#1, 0x11)
                    #     2 @ 0007f8cf  rax_2#3 = rax_1#2 ^ [fsbase#0 + 0x30].q @ mem#0
                    #     [...]
                    #     7 @ 0007f8e4  jump(rax_2#3)
                    if instr.instruction_operands[0].operation == MediumLevelILOperation.MLIL_ROR and \
                       instr.instruction_operands[0].instruction_operands[1].constant == ror_bits:
                            next_instr = self.mlil_func[instr.instr_index + 1]
                            if next_instr.operation == MediumLevelILOperation.MLIL_SET_VAR_SSA                 and \
                               next_instr.instruction_operands[0].operation == MediumLevelILOperation.MLIL_XOR and \
                               any([reg_name in tkn.text for tkn in next_instr.instruction_operands[0].tokens]):
                                    self.avoid_blocks.append(block)
                                    break

    def _get_var_uses(self, var):
        if isinstance(var, variable.Variable):
            return self.mlil_func.get_var_uses(var)
        elif isinstance(var, mediumlevelil.SSAVariable):
            return self.mlil_func.get_ssa_var_uses(var)
        return []

    def _visit_var(self, var, Q = deque()):
        if var in self._var_visited:
            return
        self._var_visited.append(var)
        for instr in self._get_var_uses(var):
            if instr in Q or instr.il_basic_block in self.avoid_blocks:
                # Prevent cycle and skip instructions in avoid blocks
                continue
            # Check for variable-define instruction
            if instr.operation in [
                    MediumLevelILOperation.MLIL_VAR_PHI, 
                    MediumLevelILOperation.MLIL_SET_VAR_SSA
                ]:
                Q.append(instr)
                self._visit_var(instr.dest, Q) # Visit new variable
                Q.pop()
            # Check for call instruction
            elif instr.operation in [
                    MediumLevelILOperation.MLIL_CALL_SSA, 
                    MediumLevelILOperation.MLIL_CALL_UNTYPED_SSA
                ]:
                funcptr = instr.instruction_operands[0]
                # Is it an indirect call?
                is_indirect = False
                ## Type 1:
                ##  00086c00  uint64_t __libio_codecvt_out()
                ##    31 @ 00086c93  [...] = rbp#4([...]) @ mem#4  <---
                if funcptr.operation == MediumLevelILOperation.MLIL_VAR_SSA and \
                   var == funcptr.operands[0]:
                        is_indirect = True
                ## Type 2: 
                ##  00083be0  void* _IO_wdoallocbuf()
                ##    10 @ 00083c0b  rax#3, mem#1 = [rax_1#2 + 0x68].q @ mem#0([...])  <---
                elif funcptr.operation == MediumLevelILOperation.MLIL_LOAD_SSA and \
                     var in funcptr.instruction_operands[0].vars_read:
                        is_indirect = True
                if not is_indirect:
                    continue
                # Run `LibIOFuncTaintTracker` to check if branch conditions are tainted
                t = LibIOFuncTaintTracker(
                    self.bv, instr, avoid_blocks=self.avoid_blocks,
                    taint_arg_idx=self.taint_arg_idx,
                    sink_callarg_idx=[] # Disable callarg tracking
                )
                t.process()
                if t.is_success():
                    # Sweet! We just found a hijackable indirect call.
                    # Now save the tracker to `self.succeed_trackers` list for later use
                    t.call_dataflow = list(Q) + [instr]
                    self.succeed_trackers.append(t)

    def find_indirect_call(self):
        ''' Find hijackable indirect calls
        
           Note: `find_protection()` should be called before calling this
        
        '''
        if len(self.succeed_trackers) > 0 or not self.mlil_func or len(self.taint_arg) == 0:
            return

        # Perform taint analysis on each taint arguments
        for var in self.taint_arg:
            self._visit_var(var)
        
        if len(self.succeed_trackers) > 1:
            # Sort by dataflow length
            self.succeed_trackers.sort(key = lambda x : len(x.call_dataflow))

class LibIOFuncTaintTracker:
    def __init__(self, bv, sink_instr, avoid_blocks=[],
                taint_arg_idx=DEFAULT_TAINT_ARG_IDX, 
                sink_callarg_idx=DEFAULT_SINK_CALLARG_IDX, 
                track_rbp=TRACK_RBP,
                allow_call_blocks=ALLOW_CALL_BLOCKS):
                    
        ''' `LibIOFuncTaintTracker` class implements a simple taint tracker
               used to find function-scope code paths to specified call instruction (`sink_instr`),
               whose branch conditions are tainted by function arguments indicated by `taint_arg_idx`.
               `sink_callarg_idx` indicates the function arguments of `sink_instr` that also should be tainted.
            
            `sink_instr` should be an address or a BNIL instruction object.
            
            If an eligible code path is found, the tracker will return a succeed state 
              (which can be checked with `is_success()` method) and yield results to the following members:
                * `code_path`: a list of MLIL instructions that are executed before `sink_instr` being reached.
                * `block_path`: a list of basic block that are passed by before `sink_instr` being reached,
                     similar with `code_path`.
                * `branch_condition`: a dict that maps MLIL_IF instructions in `code_path` to a MLIL instruction
                     representing the condition that must be satisfied to move on to next instruction in code path.
                * `call_dataflow`: the dataflow for function arguments indicated by `sink_callarg_idx` in code path.
                * `rbp_dataflow`: the dataflow for RBP/ESP register in code path,
                     available only in i386/x64 and when `track_rbp` == True.
        '''
        
        self.bv = bv
        
        # Tracker status
        #  True  - The process was completed successfully
        #  False - The process was completed but failed
        #  None  - The process is not started yet
        self.status = None

        # Tracker options
        self.track_rbp         = track_rbp
        self.avoid_blocks      = avoid_blocks
        self.allow_call_blocks = allow_call_blocks

        # Tracker results
        self.code_path  = []
        self.block_path = []
        self.branch_condition = {}
        self.call_dataflow = []
        self.rbp_dataflow  = []

        if isinstance(sink_instr, int):
            f = bv.get_functions_containing(sink_instr)[0]
            self.sink_instr = f.get_low_level_il_at(sink_instr).medium_level_il.ssa_form
        elif hasattr(sink_instr, 'operation'):
            if isinstance(sink_instr.operation, MediumLevelILOperation):
                self.sink_instr = sink_instr.ssa_form
            else:
                self.sink_instr = sink_instr.medium_level_il.ssa_form
        else:
            debug_print(f"Unexpected sink_instr type {type(sink_instr)}")
            self._mark_failed()
            return
        self.sink_block = self.sink_instr.il_basic_block
        self.mlil_func  = self.sink_instr.function
        
        f = self.mlil_func.source_function
        self.taint_arg = [
            f.parameter_vars[idx] 
                for idx in filter(lambda x : x < len(f.parameter_vars), taint_arg_idx)
        ]
        self.sink_callarg = [
            self.sink_instr.params[idx]
                for idx in filter(lambda x : x < len(self.sink_instr.params), sink_callarg_idx)
        ]
        
        # For internal use
        self._var_visited   = []
        self._instr_visited = []
        self._var_visited_saved   = []
        self._instr_visited_saved = []
        
    def is_success(self):
        return self.status == True
    
    def is_failed(self):
        return self.status == False
    
    def is_done(self):
        return self.status != None
    
    def _mark_success(self):
        self.status = True
    
    def _mark_failed(self):
        self.status = False
    
    def _mark_unfinished(self):
        self.status = None
    
    def _save_visited_status(self):
        self._var_visited_saved   = self._var_visited[:]
        self._instr_visited_saved = self._instr_visited[:]
        self._var_visited   = []
        self._instr_visited = []
    
    def _restore_visited_status(self):
        self._var_visited   = self._var_visited_saved[:]
        self._instr_visited = self._instr_visited_saved[:]
        self._var_visited_saved = self._instr_visited_saved = []

    def _get_var_def(self, var):
        if isinstance(var, variable.Variable):
            instr = self.mlil_func.get_var_definitions(var)
            if instr: return instr[0].ssa_form
        elif isinstance(var, mediumlevelil.SSAVariable):
            return self.mlil_func.get_ssa_var_definition(var)
        return None

    def _get_var_name(self, var):
        if isinstance(var, variable.Variable):
            return var.name
        elif isinstance(var, mediumlevelil.SSAVariable):
            return f"{var.name}_{var.version}"
        else:
            return str(type(var))
    
    def _get_blk_addr(self, block: mediumlevelil.MediumLevelILBasicBlock):
        return block[0].address
    
    def _resolve_branch_condition(self, next_block, cond_instr):
        if cond_instr.true == next_block.start:
            # Return non-ssa form condition ILInstruction
            return cond_instr.condition.low_level_il.non_ssa_form
        elif cond_instr.false == next_block.start:
            cond = cond_instr.condition.low_level_il.non_ssa_form
            # Create expression with inverted condition
            if cond.operation in [LowLevelILOperation.LLIL_FLAG, LowLevelILOperation.LLIL_NOT]:
                # For LLIL_FLAG and LLIL_NOT, simply create a NOT expression
                expr_idx = cond.function.not_expr(cond.size, cond.expr_index)
            else:
                func = getattr(cond.function, COND_INVERT_FUNC_MAP[cond.operation])
                expr_idx = func(cond.size, cond.operands[0].expr_index, cond.operands[1].expr_index)
            # Return the corresponding ILInstruction with new expression
            return lowlevelil.LowLevelILInstruction(cond.function, expr_idx, cond, cond.function)
        else:
            return None

    def _check_tainted_arg(self, var):
        # If definition does't exist, check if the variable is belonging to one of taint source
        if isinstance(var, variable.Variable):
            src = var
        elif isinstance(var, mediumlevelil.SSAVariable):
            src = var.var
        else:
            # Unexpected variable type
            return False
        if src in self.taint_arg:
            debug_print(f"    *Taint source reached*")
            return True
        else:
            debug_print(f"    ERROR: unexpected taint source {src.name}")
            return False

    def _check_block(self, block: mediumlevelil.MediumLevelILBasicBlock):
        bv = self.bv
        if block in self.avoid_blocks:
            return False
        elif not self.allow_call_blocks:
            # Block shoud not contain a call/jmp instruction
            # preventing branch conditions depending on the result of these calls
            # (This check can be disabled by setting `allow_call_blocks=True`)
            for instr in block:
                if instr.operation in [
                    MediumLevelILOperation.MLIL_CALL_SSA, 
                    MediumLevelILOperation.MLIL_CALL_UNTYPED_SSA, 
                    MediumLevelILOperation.MLIL_JUMP
                ]:
                    if bv.arch.name == 'x86':
                        # i386: Allow harmless __x86.get_pc_thunk.* calls
                        #
                        # 00147b0d  void* const __x86.get_pc_thunk.ax()
                        #   0 @ 00147b0d  eax#1 = __return_addr#0
                        #   1 @ 00147b10  return eax#1
                        target = instr.instruction_operands[0]
                        if target.operation == MediumLevelILOperation.MLIL_CONST_PTR:
                            f = bv.get_function_at(target.constant).mlil
                            if len(f) == 2: # Contains only two instructions
                                vaule = f[0].instruction_operands[0].value
                                if isinstance(vaule, variable.ReturnAddressRegisterValue):
                                    continue
                    return False
        return True
        
    def _visit_subpath(self, src, dst, subpaths, Q = deque()):
        if src in Q:
            # Prevent cycle
            return
        
        if DEBUG: 
            deque_blk = ', '.join([hex(self._get_blk_addr(b)) for b in list(Q)[::-1]])
            edge_blk  = ', '.join([hex(self._get_blk_addr(e.source)) for e in src.incoming_edges])
            debug_print(f"  Visiting block at {hex(src.source_block.start)}...")
            debug_print(f"    Current deque : [{deque_blk}]...")
            debug_print(f"    Incoming edge : [{edge_blk}]...")
        
        # Note that incoming edges will be visited, not outgoing ones
        # for we are walking from bottom to top in callgraph
        Q.appendleft(src)
        for b in [edge.source for edge in src.incoming_edges]:
            if b == dst:
                debug_print("    *Target block reached*")
                subpaths.append(list(Q)[:-1])
            elif self._check_block(b):
                self._visit_subpath(b, dst, subpaths, Q)
        Q.popleft()

    def _visit_var(self, var, idx, check_taint_src_func = _check_tainted_arg):
        if self.is_failed() or var in self._var_visited:
            return
        # Get variable definition
        def_instr = self._get_var_def(var)
        if not def_instr:
            if not check_taint_src_func(self, var):
                self._mark_failed()
            return
        self._var_visited.append(var)
        
        if DEBUG: 
            vars_read = ', '.join([self._get_var_name(v) for v in def_instr.vars_read])
            debug_print(f"  Visiting {self._get_var_name(var)}...")
            debug_print(f"    definition : '{str(def_instr)}' (@{hex(def_instr.address)})...")
            debug_print(f"    vars_read : [{vars_read}]...")

        # Visit variables used in definition
        if def_instr.operation == MediumLevelILOperation.MLIL_VAR_PHI:
            # For PHI function, visit the *only one* variable used in previous blocks in block_path
            if any([pv in self._var_visited for pv in def_instr.vars_read]):
                return
            for pv in def_instr.vars_read:
                pv_def_instr = self.mlil_func.get_ssa_var_definition(pv)
                # Check if it was referenced in previous blocks
                if pv_def_instr and pv_def_instr.il_basic_block in self.block_path[:idx+1]:
                    self._visit_var(pv, idx)
                    break
        else:
            self._instr_visited.append(def_instr)
            for v in def_instr.vars_read:
                self._visit_var(v, idx)    

    def process(self):
        ''' Perform taint analysis'''
        if DEBUG:
            debug_print(
                "Running LibIOFuncTaintTracker on "               + 
                f"func={self.mlil_func.source_function.name} " + 
                f"sink_instr={hex(self.sink_instr.address)} "  + 
                f"taint_source={','.join([v.name for v in self.taint_arg])}"
            )

        if self.is_done():
            debug_print("*The process is already finished, exiting peacefully*")
            return
        if len(self.taint_arg) == 0:
            debug_print("*No taint source provided, abort*")
            self._mark_failed()
            return
        
        bv = self.bv

        dominators = self.sink_block.dominators
        # Rearrange dominator block list returned from Binary ninja if it has a wrong order
        if dominators[0] != self.mlil_func.basic_blocks[0]: # Entry block should be the first one
            debug_print("Warning : sink_block.dominators has wrong order")
            dominators.sort(key = lambda x : x.start) # Sort by starting address, rough but acceptable in most cases
        dominators = dominators[:dominators.index(self.sink_block)+1]
        if DEBUG:
            blocks = ', '.join([hex(self._get_blk_addr(b)) for b in dominators])
            debug_print(f"Dominator blocks=[{blocks}]")
        
        # Check all dominator blocks if suitable for taint tracking
        if not all(self._check_block(b) for b in dominators[:-1]):
            debug_print("*Invaild dominator block detected, abort*")
            self._mark_failed()
            return
        
        # Find path between every dominator blocks
        debug_print("Step 1: Tracking tainted rip dataflow...")
        for idx, block in enumerate(dominators):
            self.block_path.append(block)
            if block == self.sink_block:
                debug_print(f"[BLK#{idx}] Sink block reached.")
                break
            if len(block.outgoing_edges) == 0 or idx + 1 >= len(dominators):
                debug_print(f"[BLK#{idx}] ERR: Broken CFG?")
                self._mark_failed()
                return
            # Check if one of outgoing edges can reach next block
            next_block = dominators[idx + 1]
            debug_print(f"[BLK#{idx}] Looking for outgoing edge to {hex(self._get_blk_addr(next_block))}...")
            for b in [edge.target for edge in block.outgoing_edges]:
                # Fast forward if block has only one outgoing edge
                debug_print(f"  Edge block at {hex(b.source_block.start)}")
                subpath = []
                while b != next_block and len(b.outgoing_edges) == 1:
                    subpath.append(b)
                    b = b.outgoing_edges[0].target
                    debug_print(f"    jump block skipped, next block is at {hex(self._get_blk_addr(b))}")
                if b == next_block:
                    debug_print(f"    *Next block reached*")
                    self.block_path.extend(subpath)
                    break
                else:
                    debug_print(f"    (unreachable)")
                    continue
            else:
            # Do depth-first search to find subpaths from current block to next block
                debug_print(f"[BLK#{idx}] Searching subpath from {hex(self._get_blk_addr(block))} to {hex(self._get_blk_addr(next_block))}...")
                subpath_list = []
                self._visit_subpath(next_block, block, subpath_list)
                debug_print(f"[BLK#{idx}] {len(subpath_list)} subpaths found")
                if len(subpath_list) == 0:
                    debug_print(f"*No subpath found, abort*")
                    self._mark_failed()
                    return
                if len(subpath_list) > 1:
                    # Sort by instruction count
                    subpath_list.sort(key = lambda subpath : sum([b.instruction_count for b in subpath]))
                # Add shortest subpath to call_path
                subpath = subpath_list[0]
                self.block_path.extend(subpath)
                if DEBUG:
                    path = ' -> '.join([hex(self._get_blk_addr(b)) for b in subpath])
                    debug_print(f"[BLK#{idx}] Selected subpath : [{path}]")
        debug_print("[*] Dataflow tracking done.")

        debug_print("Step 2: Tracking tainted branch condition...")
        # Process branch conditions in block_path
        for idx, block in enumerate(self.block_path[:-1]):
            if len(block.outgoing_edges) == 1:
                debug_print(f"[BLK#{idx}] Skipped")
                continue
            cond_instr = block[-1]
            debug_print(f"[BLK#{idx}] Condition instruction : '{str(cond_instr.low_level_il.non_ssa_form)}'")
            # Perform taint analysis on variables used in branch conditions
            self._instr_visited.append(cond_instr)
            for v in cond_instr.vars_read:
                self._visit_var(v, idx)
                if self.is_failed():
                    debug_print("*Branch condition tracking failed, abort*")
                    return
            # Record branch dependency
            if idx + 1 < len(self.block_path):
                cond = self._resolve_branch_condition(self.block_path[idx + 1], cond_instr)
                if cond:
                    debug_print(f"[BLK#{idx}] Resolved condition : '{str(cond)}'")
                else:
                    debug_print(f"[BLK#{idx}] Unable to resolve condition!")
                self.branch_condition[cond_instr] = cond

        # (Optional) Trace rdi dataflow
        if len(self.sink_callarg) > 0:
            debug_print("Step 3.1: Tracking tainted rdi dataflow...")
            # Save state
            self._save_visited_status()
            # Perform taint analysis
            for v in self.sink_callarg:
                if isinstance(v, mediumlevelil.MediumLevelILVarSsa):
                    v = v.operands[0]
                self._visit_var(v, len(self.block_path))
                if self.is_failed():
                    debug_print("*rdi dataflow tracking failed, abort*")
                    return
            # Save rdi dataflow
            for v in self._var_visited:
                self.call_dataflow.insert(0, self._get_var_def(v))
            self.call_dataflow.append(self.sink_instr)
            # Reset state
            self._restore_visited_status()
            debug_print("[*] Call dataflow tracking done.") 

        if self.track_rbp and bv.arch.name in ['x86', 'x86_64']:
            debug_print("Step 3.2: Tracking tainted rbp dataflow...")
            # Save state
            self._save_visited_status()
            # Find 
            vars_list = list(filter(lambda v : 'rbp' in v.name or 'ebp' in v.name, self.mlil_func.ssa_vars))
            vars_list.sort(key = lambda v : v.version, reverse = True)
            if DEBUG:
                tainted_vars = ', '.join([f'{v.name}_{v.version}' for v in vars_list])
                debug_print(f"Possible tainted vars: {tainted_vars}")
            rbp_var = None
            for v in vars_list:
                def_instr = self._get_var_def(v)
                if not def_instr:
                    continue
                block = def_instr.il_basic_block
                if block in self.block_path:
                    if block == self.sink_block and def_instr.address > self.sink_instr.address:
                        continue
                    rbp_var = v
                    break
            # Perform taint analysis
            if rbp_var:
                self._visit_var(v, len(self.block_path))
                if self.is_failed():
                    self._mark_unfinished()
                else:
                    for v in self._var_visited:
                        self.rbp_dataflow.insert(0, self._get_var_def(v))
            # Reset state
            self._restore_visited_status()
            debug_print("[*] rbp dataflow tracking done.") 

        # Save code path
        for b in dominators:
            dataflow = list(filter(lambda x : x.il_basic_block == b, self._instr_visited))
            dataflow.sort(key = lambda x : x.address)
            self.code_path.extend(dataflow)
        
        # Mark the process is successful
        self._mark_success()
        
        debug_print("*The process completed successfully*")
        
    def report_result(self, indent=4):
        if not self.is_success():
            return

        bv = self.bv

        ljust = indent * ' '
        
        # 1. Display header
        log_info(ljust + f"{hex(self.sink_instr.address)}: {str(self.sink_instr.low_level_il.non_ssa_form)}")
        # 2. Display rip/rdi dataflow
        log_info(ljust + '  RIP/RDI DATAFLOW:')
        callflow = []
        for instr in self.call_dataflow:
            if instr.low_level_il: callflow.append(str(instr.low_level_il.non_ssa_form))
        if len(callflow) > 0:
            log_info(ljust + '   ' + " -> ".join(callflow))
        else:
            log_info(ljust + '   (N/A)')
        # 3. Display rbp dataflow
        if self.track_rbp and bv.arch.name in ['x86', 'x86_64']:
            log_info(ljust + '  RBP DATAFLOW:')
            rbpflow = []
            for instr in self.rbp_dataflow:
                if instr.low_level_il: rbpflow.append(str(instr.low_level_il.non_ssa_form))
            if len(rbpflow) > 0:
                log_info(ljust + '   ' + " -> ".join(rbpflow))
            else:
                log_info(ljust + '   (N/A)')
        # 4. Display code path
        log_info(ljust + '  CODE PATH:')
        if len(self.code_path) > 0:
            for instr in self.code_path:
                if instr.operation == MediumLevelILOperation.MLIL_IF:
                    log_info(ljust + f'    => [condition] {str(self.branch_condition[instr])}')
                else:
                    log_info(ljust + '   ' + str(instr.low_level_il.non_ssa_form))
        else:
            log_info(ljust + '   (none)')

class LibIOVtableFuncCallGraph:
    def __init__(self, bv):
        self.bv = bv
        
        self.roots = {}
        self.nodes = {}
        self.unsafe_call_nodes = []
        self.unsafe_call_chains = {}
        
        self.vtable_start = None
        self.vtable_stop  = None
        self.vtable_validate_func = None
    
    def set_vtable_range(self, vtable_start, vtable_stop):
        self.vtable_start = vtable_start
        self.vtable_stop  = vtable_stop
    
    def set_vtable_check_func(self, vtable_validate_func):
        if isinstance(vtable_validate_func, int):
            self.vtable_validate_func = self.bv.get_function_at(vtable_validate_func)
        else:
            self.vtable_validate_func = vtable_validate_func
    
    def get_node(self, func):
        if func in self.nodes.keys():
            return self.nodes[func]
        else:
            return None
    
    def add_new_node(self, func: function.Function, is_root=False):
        if func not in self.nodes:
            node = LibIOFunc(self.bv, func)
            self.nodes[func] = node
            if is_root:
                node.set_as_root()
                self.roots[func] = node
                debug_print(f"New root: {node.name}")
            else:
                debug_print(f"New node: {node.name}")
            return node
    
    def parse_vtable(self):
        bv = self.bv
        if None in [self.vtable_start, self.vtable_stop]:
            return
        log_info(f"[*] Parsing vtable from {hex(self.vtable_start)} to {hex(self.vtable_stop)}...")
        for addr in range(self.vtable_start, self.vtable_stop, bv.arch.address_size):
            faddr = bv.read_pointer(addr)
            if not faddr:
                continue
            # Do not use `bv.get_functions_at()` here
            #   In ARM, pointers in `__libc_IO_vtables` do not point to the beginning of IO functions
            f = bv.get_functions_containing(faddr)
            if len(f) > 0:
                f = f[0]
                if f not in self.nodes:
                    node = self.add_new_node(f, True)
                else:
                    node = self.get_node(f)
                node.vtable_locations.append(addr)
        log_info(f"[*] Done. {len(self.roots)} unique root(s) processed.")

    def build_graph(self):
        log_info("[*] Building call graph...")
        Q = deque(self.roots.values())
        cnt = 0
        while len(Q) > 0:
            root = Q.pop()
            for f in root.func.callees:
                if f == self.vtable_validate_func or f.name in GRAPH_SKIP_FUNCTION:
                    continue
                if f in self.nodes:
                    node = self.nodes[f]
                else:
                    node = self.add_new_node(f)
                    Q.append(node)
                node.add_caller(root)
                root.add_callee(node)
                cnt += 1
        log_info(f"[*] Done. {cnt} unique node(s) processed.")

    def find_indirect_call(self):
        log_info("[*] Searching indirect call in graph nodes...")
        cnt = 0
        for node in self.nodes.values():
            node.find_protection(self.vtable_validate_func)
            node.find_indirect_call()
            if node.has_indirect_calls():
                log_info(f"{str(cnt).rjust(2)}. {node.name}")
                for tracker in node.succeed_trackers:
                    tracker.report_result()
                    cnt += 1
                self.unsafe_call_nodes.append(node)
        log_info(f"[*] Done. {cnt} unprotected indirect call(s) found.")

    def _visit_graph(self, node, Q = deque()):
        # Stop if depth length exceeds MAX_CHAIN_LEN
        if len(Q) + 1 > MAX_CHAIN_LEN:
            return
        Q.appendleft(node)
        if not node.is_root():
            # Visit node's callers
            for n in node.callers.values():
                self._visit_graph(n, Q)
        else:
            call_chain = []
            for idx, n in enumerate(Q):
                if idx + 1 == len(Q):
                    call_chain.append(n.succeed_trackers[0])
                    break
                trackers = []
                for ref in self.bv.get_code_refs(Q[idx + 1].addr):
                    if ref.function == n.func:
                        t = LibIOFuncTaintTracker(self.bv, ref.address)
                        t.process()
                        if t.is_success():
                            trackers.append(t)
                if len(trackers) == 0:
                    Q.popleft()
                    return
                if len(trackers) > 0:
                    trackers.sort(key = lambda x : len(x.call_dataflow))
                call_chain.append(trackers[0])
            func = node.func
            if func not in self.unsafe_call_chains:
                self.unsafe_call_chains[func] = []
            self.unsafe_call_chains[func].append(call_chain)
        Q.popleft()

    def generate_call_chain(self):
        log_info("[*] Generating call chain...")
        for node in self.unsafe_call_nodes:
            self._visit_graph(node)
        cnt = 0
        for func, chain_list in self.unsafe_call_chains.items():
            node = self.get_node(func)
            for call_chain in chain_list:
                funcs = ' -> '.join(map(lambda x : self.get_node(x.mlil_func.source_function).name, call_chain))
                log_info(f"{str(cnt).rjust(2)}. {funcs}")
                for tracker in call_chain:
                    tracker.report_result()
                cnt += 1
            log_info(f"  ([{', '.join(map(hex, node.vtable_locations))}] is the location of {func.name} in __libc_IO_vtables)")
        log_info(f"[*] Done. {cnt} exploitable call chain(s) found.") 

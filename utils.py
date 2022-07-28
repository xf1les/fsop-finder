from binaryninja import MediumLevelILOperation
from binaryninja import Endianness
from binaryninja import log_warn, log_info

import struct

DEBUG = False

def debug_print(msg):
    if DEBUG:
        log_info(f'[DBG] {msg}')

def get_ptr_data_at(bv, addr):
    ''' Read a uintptr-size data from given pointer address
    
    Equivalent to this C statement:
        return *(uintptr_t)(addr)
    '''
    # https://docs.python.org/3/library/struct.html#byte-order-size-and-alignment
    if bv.arch.endianness == Endianness.LittleEndian:
        fmt  = '<' # little-endian
    else:
        fmt  = '>' # big-endian
    if bv.arch.address_size == 8:
        fmt += 'Q' # 8-bytes
    else:
        fmt += 'L' # 4-bytes
    return struct.unpack(fmt, bv.read(addr, bv.arch.address_size))[0]

def get_glibc_version(bv):
    f = bv.get_functions_by_name('gnu_get_libc_version')[0]
    for instr in f.medium_level_il.instructions:
        #  00020950  int64_t gnu_get_libc_version()
        #     0 @ 00020950  rax = "2.27"  <----
        #     1 @ 00020957  return "2.27"
        if instr.operation == MediumLevelILOperation.MLIL_SET_VAR and \
           instr.instruction_operands[0].operation == MediumLevelILOperation.MLIL_CONST_PTR:
                str_addr = instr.instruction_operands[0].constant
                bv_str = bv.get_string_at(str_addr)
                if str_addr > bv_str.start:
                    # "NPTL 2.27" -> "2.27"
                    return float(bv_str.value[str_addr-bv_str.start:])
                else:
                    return float(bv_str.value)

def _find_vtable_border(bv, addresses):
    last_nullptr = addresses[0]
    for addr in addresses:
        ptr = get_ptr_data_at(bv, addr)
        if ptr:
            f = bv.get_function_at(ptr)
            # Check if we encounter a libio function
            if f and f.name.startswith("_IO_"):
                # Skip _IO_obstack_jumps in 2.23 which is too far away from the border
                if get_glibc_version(bv) == 2.23 and f.name.startswith('_IO_obstack'):
                    continue
                # Return the nearest address that contains a NULL pointer 
                return last_nullptr
        else:
            last_nullptr = addr
    return None

def get_vtable_range(bv):
    if get_glibc_version(bv) >= 2.24:
        section = bv.get_section_by_name("__libc_IO_vtables")  
        vtable_start, vtable_end =  section.start, section.end
    else:
        # Before GLIBC 2.24, there is no `__libc_IO_vtables` section. 
        # Instead, we use `_find_vtable_border()` to find a memory area in `.data.rel.ro` section 
        #   as many IO vtables (`_IO_*_jumps`) as possible nested in. 
        # This approach is very buggy, so it's recommended to avoid using `G.set_vtable_range()` 
        #   and add IO vtable functions one by one by directly calling `G.add_new_node()` if GLIBC version < 2.24.
        log_warn(f"[!] __libc_IO_vtables section is not available in this glibc.")
        log_info("[*] Searching vtable borders in .data.rel.ro section...")
        section = bv.get_section_by_name(".data.rel.ro")
        addresses = list(range(section.start, section.end, bv.arch.address_size))
        vtable_start = _find_vtable_border(bv, addresses)
        vtable_end   = _find_vtable_border(bv, addresses[::-1])
    return vtable_start, vtable_end

def get_vtable_check_func(bv):
    # Try _IO_vtable_check symbol
    funcs = bv.get_functions_by_name('_IO_vtable_check')
    if len(funcs) > 0:
        address = funcs[0].start
    else:
        # _IO_vtable_check references this string
        s = "Fatal error: glibc detected an invalid stdio handle"
        for str_refs in bv.strings:
            # Find the corresponding StringReference object in binaryview
            if str_refs.length >= len(s) and s in str_refs.value:
                # Get code references to the string
                refs = list(bv.get_code_refs(str_refs.start))
                if len(refs) > 0:
                    address = refs[0].function.start
                    break
    return address       

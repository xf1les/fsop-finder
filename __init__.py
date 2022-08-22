from binaryninja import AnalysisState
from binaryninja import BackgroundTaskThread
from binaryninja import PluginCommand
from binaryninja import log_info, log_warn, log_error

from .finder import LibIOVtableFuncCallGraph
from .utils  import get_glibc_version, get_vtable_range, get_vtable_check_func

class FinderTask(BackgroundTaskThread):
    def __init__(self, bv):
        BackgroundTaskThread.__init__(self, "Looking for eligible FSOP code path...", True)
        self.bv = bv
    
    def run(self):
        bv = self.bv
        
        if bv.analysis_progress.state == AnalysisState.AnalyzeState:
            log_warn("[!] An active analysis is running now. Please wait until it is completed.")
            return
        if bv.arch.name not in ['x86', 'x86_64', 'thumb2', 'aarch64']:
            log_warn(f"[!] Unsupported or untest platform '{bv.arch.name}', result may be incorrect. We currently support i386/x64/thumb2/aarch64.")

        glibc_ver = get_glibc_version(bv)
        if glibc_ver != None:
            log_info(f"[*] glibc version: {glibc_ver}")
        else:
            log_info(f"[!] Failed to detect glibc version!")
        
        G = LibIOVtableFuncCallGraph(bv)
        
        log_info("[*] Looking for __libc_IO_vtables section")
        start, stop = get_vtable_range(bv)
        if None in [start, stop]:
            log_error("[-] Failed to detect vtable!")
            return
        G.set_vtable_range(start, stop)
        if glibc_ver == None or glibc_ver >= 2.24:
            log_info("[*] Looking for _IO_vtable_check function...")
            func = get_vtable_check_func(bv)
            if not func:
                log_error(f"[-] Can't find _IO_vtable_check!")
                return
            G.set_vtable_check_func(func)
            log_info(f"_IO_vtable_check@{hex(func)}")
        else:
            log_info("[*] _IO_vtable_check is not available in this version of glibc.")

        G.parse_vtable()
        G.build_graph()
        G.find_indirect_call()
        G.generate_call_chain()

def main(bv):
    FinderTask(bv).start()

PluginCommand.register(
    'Find FSOP code path',
    'Find code path that can hijack control flow and stack pointer in GLIBC libc.so.6',
    main
)

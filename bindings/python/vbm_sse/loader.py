"""Hand-written loader (trusted, docs/trust-ledger.md T11): finds and opens libvbm_sse. It decides nothing about SSE."""
import ctypes, ctypes.util, os, sys

_NAMES = {"win32": "vbm_sse.dll", "darwin": "libvbm_sse.dylib"}.get(sys.platform, "libvbm_sse.so")


def load():
    """VBM_SSE_LIB (a path) first, then the library next to this package, then the system's (ctypes.util.find_library)."""
    here = os.path.dirname(os.path.abspath(__file__))
    cands = [os.environ.get("VBM_SSE_LIB"), os.path.join(here, _NAMES), ctypes.util.find_library("vbm_sse")]
    errs = []
    for c in cands:
        if not c: continue
        try:
            return ctypes.CDLL(c)
        except OSError as e:
            errs.append(str(e))
    raise ImportError("vbm-sse: cannot load libvbm_sse (set VBM_SSE_LIB to its path): " + "; ".join(errs))

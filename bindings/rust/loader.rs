// Hand-written build script (trusted, docs/trust-ledger.md T11): points the linker at libvbm_sse (a directory in VBM_SSE_LIB_DIR; else the system's). It decides nothing about SSE.
fn main() {
    println!("cargo:rerun-if-env-changed=VBM_SSE_LIB_DIR");
    if let Ok(dir) = std::env::var("VBM_SSE_LIB_DIR") {
        println!("cargo:rustc-link-search=native={}", dir);
        println!("cargo:rustc-link-arg=-Wl,-rpath,{}", dir);
    }
}

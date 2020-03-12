use inkwell::module::Module;
use std::fs;
use std::io;

pub fn verify(out_path: &str, module: &Module) {
    if let Err(err) = fs::remove_file(out_path) {
        match err.kind() {
            io::ErrorKind::NotFound => {}
            _ => panic!("Could not remove {}: {}", out_path, err),
        }
    }

    if let Err(err) = module.verify() {
        module.print_to_file(out_path).unwrap();

        panic!(
            "LLVM verification failed (IR written to {})\n{}",
            out_path, err
        );
    }
}

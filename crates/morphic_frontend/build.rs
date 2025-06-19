fn main() -> anyhow::Result<()> {
    println!("cargo:rerun-if-changed=build.rs");

    lalrpop::Configuration::new()
        .emit_rerun_directives(true)
        .process_current_dir()
        .map_err(|err| anyhow::anyhow!("{err}"))?;

    Ok(())
}

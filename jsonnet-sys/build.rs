use std::env;
use std::error::Error;
use std::fs::{create_dir_all, File};
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process::Command;

fn main() -> Result<(), Box<dyn Error>> {
    if !Path::new("jsonnet/.git").exists() {
        let _ = Command::new("git")
            .args(&["submodule", "update", "--init"])
            .status();
    }

    let dir = Path::new("jsonnet");
    let out_dir = PathBuf::from(env::var_os("OUT_DIR").expect("OUT_DIR undefined"));

    let embedded = ["std"];
    for f in &embedded {
        let output = out_dir.join("include").join(format!("{}.jsonnet.h", f));
        let input = dir.join("stdlib").join(format!("{}.jsonnet", f));
        println!("embedding: {:?} -> {:?}", input, output);
        create_dir_all(output.parent().unwrap())?;
        let in_f = File::open(input)?;
        let mut out_f = File::create(&output)?;
        for b in in_f.bytes() {
            write!(&mut out_f, "{},", b?)?;
        }
        writeln!(&mut out_f, "0")?;
    }

    let jsonnet_core = [
        "desugarer.cpp",
        "formatter.cpp",
        "lexer.cpp",
        "libjsonnet.cpp",
        "parser.cpp",
        "pass.cpp",
        "static_analysis.cpp",
        "string_utils.cpp",
        "vm.cpp",
    ];

    let mut c = cc::Build::new();
    c.cpp(true)
        .flag_if_supported("-std=c++0x")
        .include(out_dir.join("include"))
        .include(dir.join("include"))
        .include(dir.join("third_party/md5"));

    for f in &jsonnet_core {
        c.file(dir.join("core").join(f));
    }

    c.file(dir.join("third_party/md5/md5.cpp"));

    c.compile("libjsonnet.a");

    Ok(())
}

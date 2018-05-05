extern crate gcc;

use std::path::Path;
use std::process::Command;
use std::fs::File;
use std::io::{Read,Write};

fn main() {
    if !Path::new("jsonnet/.git").exists() {
        let _ = Command::new("git")
            .args(&["submodule", "update", "--init"])
            .status();
    }

    let dir = Path::new("jsonnet");

    let embedded = [
        "std",
    ];
    for f in &embedded {
        let output = dir.join("core").join(format!("{}.jsonnet.h", f));
        if output.exists() {
            continue;
        }
        let input = dir.join("stdlib").join(format!("{}.jsonnet", f));
        println!("embedding: {:?} -> {:?}", input, output);
        let in_f = File::open(input).unwrap();
        let mut out_f = File::create(&output).unwrap();
        for b in in_f.bytes() {
            write!(&mut out_f, "{},", b.unwrap()).unwrap();
        }
        writeln!(&mut out_f, "0").unwrap();
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

    let mut c = gcc::Build::new();
    c.cpp(true)
        .flag("-std=c++0x")
        .include(dir.join("include"))
        .include(dir.join("third_party/md5"));

    for f in &jsonnet_core {
        c.file(dir.join("core").join(f));
    }

    c.file(dir.join("third_party/md5/md5.cpp"));

    c.compile("libjsonnet.a")
}

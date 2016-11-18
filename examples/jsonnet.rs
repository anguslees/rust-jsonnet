/// An almost-but-not-quite drop-in for the official `jsonnet`
/// executable.

#[macro_use] extern crate clap;
extern crate jsonnet;

use std::io::{self,Write};
use std::{process,env};
use clap::{App,Arg,SubCommand,AppSettings,ArgMatches};
use std::error::Error as StdError;
use std::borrow::Cow;
use jsonnet::{JsonnetVm,jsonnet_version};

fn typed_arg_or_exit<'a, T>(matches: &ArgMatches<'a>, arg: &str) -> Option<T>
    where T: std::str::FromStr
{
    if matches.is_present(arg) {
        let v = value_t!(matches, arg, T).unwrap_or_else(|e| e.exit());
        Some(v)
    } else {
        None
    }
}

/// Parse "foo" into ("foo", None) and "foo=bar" into ("foo", Some("bar"))
fn parse_kv(s: &str) -> (&str, Option<&str>) {
    match s.find('=') {
        Some(i) => (&s[..i], Some(&s[i+1..])),
        None => (s, None),
    }
}

#[test]
fn test_parse_kv() {
    assert_eq!(parse_kv("foo=bar"), ("foo", Some("bar")));
    assert_eq!(parse_kv("foo"), ("foo", None));
    assert_eq!(parse_kv("foo="), ("foo", Some("")));
}

fn build_cli<'a,'b>(version: &'b str) -> App<'a,'b> {
    App::new("jsonnet")
        .version(version)
        .author(crate_authors!())
        .about("Jsonnet command line tool")
        .setting(AppSettings::VersionlessSubcommands)
        .setting(AppSettings::SubcommandRequiredElseHelp)
        .subcommand(SubCommand::with_name("eval")
                    .about("Evaluate a jsonnet file/expression")
                    .arg(Arg::with_name("exec")
                         .short("e")
                         .long("exec")
                         .help("Treat INPUT as code"))
                    .arg(Arg::with_name("incdir")
                         .short("j")
                         .long("jpath")
                         .value_name("DIR")
                         .multiple(true)
                         .use_delimiter(false)
                         .number_of_values(1)
                         .help("Specify an additional library search dir"))
                    .arg(Arg::with_name("string")
                         .short("S")
                         .long("string")
                         .help("Expect a string, manifest as plain text"))
                    .arg(Arg::with_name("max-stack")
                         .short("s")
                         .long("max-stack")
                         .value_name("N")
                         .help("Number of allowed stack frames"))
                    .arg(Arg::with_name("max-trace")
                         .short("t")
                         .long("max-trace")
                         .value_name("N")
                         .help("Max length of stack trace before cropping"))
                    .arg(Arg::with_name("gc-min-objects")
                         .long("gc-min-objects")
                         .value_name("N")
                         .help("Do not run garbage collector until this many"))
                    .arg(Arg::with_name("gc-growth-trigger")
                         .long("gc-growth-trigger")
                         .value_name("N")
                         .help("Run garbage collector after this amount of object growth"))
                    .arg(Arg::with_name("ext-var")
                         .short("V")
                         .long("ext-str")
                         .value_name("VAR[=VAL]")
                         .multiple(true)
                         .number_of_values(1)
                         .use_delimiter(false)
                         .help("Provide 'external' variable as a string. If <VAL> is omitted, get from env var <VAR>"))
                    .arg(Arg::with_name("ext-code")
                         .long("ext-code")
                         .value_name("VAR[=CODE]")
                         .multiple(true)
                         .number_of_values(1)
                         .use_delimiter(false)
                         .help("Provide 'external' variable as code. If <VAL> is omitted, get from env var <VAR>"))
                    .arg(Arg::with_name("tla-var")
                         .short("A")
                         .long("tla-str")
                         .value_name("VAR[=VAL]")
                         .multiple(true)
                         .number_of_values(1)
                         .use_delimiter(false)
                         .help("Provide 'top-level argument' as a string.  If <VAL> is omitted, get from env var <VAR>"))
                    .arg(Arg::with_name("tla-code")
                         .long("tla-code")
                         .value_name("VAR[=CODE]")
                         .multiple(true)
                         .number_of_values(1)
                         .use_delimiter(false)
                         .help("Provide 'top-level argument' as code.  If <VAL> is omitted, get from env var <VAR>"))
                    .arg(Arg::with_name("INPUT")
                         .required(true)
                         .help("Input jsonnet file")))
        .subcommand(SubCommand::with_name("fmt")
                    .about("Reformat a jsonnet file/expression")
                    .arg(Arg::with_name("exec")
                         .short("e")
                         .long("exec")
                         .help("Treat INPUT as code"))
                    .arg(Arg::with_name("indent")
                         .short("n")
                         .long("indent")
                         .value_name("N")
                         .default_value("0")
                         .help("Number of spaces to indent by, 0 means no change"))
                    .arg(Arg::with_name("max-blank-lines")
                         .long("max-blank-lines")
                         .value_name("N")
                         .default_value("2")
                         .help("Max vertical spacing, 0 means no change"))
                    .arg(Arg::with_name("string-style")
                         .long("string-style")
                         .possible_values(&["d", "s", "l"])
                         .default_value("l")
                         .value_name("C")
                         .help("Enforce double, single quotes or 'leave'"))
                    .arg(Arg::with_name("comment-style")
                         .long("comment-style")
                         .possible_values(&["h", "s", "l"])
                         .default_value("l")
                         .value_name("C")
                         .help("# (h)  // (s) or 'leave'. Never changes she-bang"))
                    .arg(Arg::with_name("no-pretty-field-names")
                         .long("no-pretty-field-names")
                         .help("Don't use syntax sugar for fields and indexing"))
                    .arg(Arg::with_name("pad-arrays")
                         .long("pad-arrays")
                         .help("[ 1, 2, 3 ] instead of [1, 2, 3]"))
                    .arg(Arg::with_name("no-pad-objects")
                         .long("no-pad-objects")
                         .help("{ x: 1, x: 2 } instead of {x: 1, y: 2}"))
                    .arg(Arg::with_name("debug-desugaring")
                         .long("debug-desugaring")
                         .help("Unparse the desugared AST without executing it"))
                    .arg(Arg::with_name("INPUT")
                         .required(true)
                         .help("Input jsonnet file")))
}

fn eval<'a, 'b>(vm: &'a mut JsonnetVm, matches: &ArgMatches<'b>) -> Result<(), Box<StdError+'a>> {
    if let Some(n) = typed_arg_or_exit(matches, "max-stack") {
        vm.max_stack(n);
    }
    if let Some(n) = typed_arg_or_exit(matches, "max-trace") {
        vm.max_trace(Some(n));
    }
    if let Some(n) = typed_arg_or_exit(matches, "gc-min-objects") {
        vm.gc_min_objects(n);
    }
    if let Some(n) = typed_arg_or_exit(matches, "gc-growth-trigger") {
        vm.gc_growth_trigger(n);
    }
    if matches.is_present("string") {
        vm.string_output(true);
    }
    if let Some(paths) = matches.values_of_os("incdir") {
        for path in paths {
            vm.jpath_add(path);
        }
    }
    if let Some(vars) = matches.values_of("ext-var") {
        for (var, val) in vars.map(parse_kv) {
            let val = val
                .map(Cow::from)
                .or_else(|| env::var(var).ok().map(Cow::from))
                .unwrap_or("".into());
            vm.ext_var(var, &val);
        }
    }
    if let Some(vars) = matches.values_of("ext-code") {
        for (var, val) in vars.map(parse_kv) {
            let val = val
                .map(Cow::from)
                .or_else(|| env::var(var).ok().map(Cow::from))
                .unwrap_or("".into());
            vm.ext_code(var, &val);
        }
    }
    if let Some(vars) = matches.values_of("tla-var") {
        for (var, val) in vars.map(parse_kv) {
            let val = val
                .map(Cow::from)
                .or_else(|| env::var(var).ok().map(Cow::from))
                .unwrap_or("".into());
            vm.tla_var(var, &val);
        }
    }
    if let Some(vars) = matches.values_of("tla-code") {
        for (var, val) in vars.map(parse_kv) {
            let val = val
                .map(Cow::from)
                .or_else(|| env::var(var).ok().map(Cow::from))
                .unwrap_or("".into());
            vm.tla_code(var, &val);
        }
    }

    let output =
        if matches.is_present("exec") {
            let expr = matches.value_of("INPUT").unwrap();
            try!(vm.evaluate_snippet("INPUT", expr))
        } else {
            let file = matches.value_of_os("INPUT").unwrap();
            try!(vm.evaluate_file(file))
        };

    print!("{}", output);
    Ok(())
}

fn fmt<'a, 'b>(vm: &'a mut JsonnetVm, matches: &ArgMatches<'b>) -> Result<(), Box<StdError+'a>> {
    if let Some(n) = typed_arg_or_exit(matches, "indent") {
        vm.fmt_indent(n);
    }
    if let Some(n) = typed_arg_or_exit(matches, "max-blank-lines") {
        vm.fmt_max_blank_lines(n);
    }
    if let Some(v) = matches.value_of("string-style") {
        let v = match v {
            "d" => jsonnet::FmtString::Double,
            "s" => jsonnet::FmtString::Single,
            "l" => jsonnet::FmtString::Leave,
            _ => unreachable!(),
        };
        vm.fmt_string(v);
    }
    if let Some(v) = matches.value_of("comment-style") {
        let v = match v {
            "h" => jsonnet::FmtComment::Hash,
            "s" => jsonnet::FmtComment::Slash,
            "l" => jsonnet::FmtComment::Leave,
            _ => unreachable!(),
        };
        vm.fmt_comment(v);
    }
    if matches.is_present("no-pretty-field-names") {
        vm.fmt_pretty_field_names(false);
    }
    if matches.is_present("pad-arrays") {
        vm.fmt_pad_arrays(true);
    }
    if matches.is_present("no-pad-objects") {
        vm.fmt_pad_objects(false);
    }
    if matches.is_present("debug-desugaring") {
        vm.fmt_debug_desugaring(true);
    }

    let output =
        if matches.is_present("exec") {
            let expr = matches.value_of("INPUT").unwrap();
            try!(vm.fmt_snippet("INPUT", expr))
        } else {
            let file = matches.value_of_os("INPUT").unwrap();
            try!(vm.fmt_file(file))
        };

    print!("{}", output);
    Ok(())
}

fn main() {
    let version = format!("{} (libjsonnet {})", crate_version!(), jsonnet_version());

    let matches = build_cli(&version)
        .get_matches();

    let mut vm = JsonnetVm::new();

    let result =
        if let Some(matches) = matches.subcommand_matches("eval") {
            eval(&mut vm, matches)
        } else if let Some(matches) = matches.subcommand_matches("fmt") {
            fmt(&mut vm, matches)
        } else {
            unreachable!();
        };

    match result {
        Ok(()) => (),
        Err(e) => {
            write!(&mut io::stderr(), "{}", e).unwrap();
            process::exit(1);
        },
    };
}

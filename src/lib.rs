//! # jsonnet bindings for Rust
//!
//! This library contains bindings to the [jsonnet][1] C library,
//! a template language that generates JSON and YAML.
//!
//! Almost all interaction with this module will be via the
//! `JsonnetVm` type.
//!
//! [1]: https://jsonnet.org/
//!
//! # Examples
//!
//! ```
//! use jsonnet::JsonnetVm;
//!
//! let mut vm = JsonnetVm::new();
//! let output = vm.evaluate_snippet("example", "'Hello ' + 'World'").unwrap();
//! assert_eq!(output.to_string(), "\"Hello World\"\n");
//! ```

#![deny(missing_docs)]
#![allow(trivial_casts)]

extern crate libc;
extern crate jsonnet_sys;

use std::ffi::{CStr, CString, OsStr};
use std::path::{Path,PathBuf};
use std::{error,iter,ptr,fmt};
use std::ops::Deref;
use libc::{c_int, c_uint, c_char, c_void};

mod string;
mod value;

pub use string::JsonnetString;
use string::JsonnetStringIter;
pub use value::{JsonVal, JsonValue};
use jsonnet_sys::JsonnetJsonValue;

/// Error returned from jsonnet routines on failure.
#[derive(Debug,PartialEq,Eq)]
pub struct Error<'a>(JsonnetString<'a>);

impl<'a> From<JsonnetString<'a>> for Error<'a> {
    fn from(s: JsonnetString<'a>) -> Self { Error(s) }
}

impl<'a> From<Error<'a>> for JsonnetString<'a> {
    fn from(e: Error<'a>) -> Self { e.0 }
}

impl<'a> Deref for Error<'a> {
    type Target = JsonnetString<'a>;
    fn deref(&self) -> &Self::Target { &self.0 }
}

impl<'a> fmt::Display for Error<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}

impl<'a> error::Error for Error<'a> {
    fn description(&self) -> &str { "jsonnet error" }
}

/// Result from "multi" eval methods.
///
/// Contains a list of (&str, &str) pairs.
pub struct EvalMap<'a>(JsonnetString<'a>);
impl<'a> EvalMap<'a> {
    /// Returns an iterator over the contained values.
    pub fn iter<'b>(&'b self) -> EvalMapIter<'b,'a> {
        EvalMapIter(unsafe { JsonnetStringIter::new(&self.0) })
    }
}

impl<'a,'b> IntoIterator for &'b EvalMap<'a> {
    type Item = (&'b str, &'b str);
    type IntoIter = EvalMapIter<'b,'a>;
    fn into_iter(self) -> Self::IntoIter { self.iter() }
}

/// Iterator returned from "multi" eval methods.
///
/// Yields (&str, &str) pairs.
#[derive(Debug)]
pub struct EvalMapIter<'a,'b:'a>(JsonnetStringIter<'a,'b>);

impl<'a,'b> Iterator for EvalMapIter<'a,'b> {
    type Item = (&'a str, &'a str);
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
            .map(|first| {
                let second = self.0.next().unwrap();
                (first, second)
            })
    }
}

/// Result from "stream" eval methods.
///
/// Contains a list of &str.
pub struct EvalList<'a>(JsonnetString<'a>);
impl<'a> EvalList<'a> {
    /// Returns an iterator over the contained values.
    pub fn iter<'b>(&'b self) -> EvalListIter<'b,'a> {
        EvalListIter(unsafe { JsonnetStringIter::new(&self.0) })
    }
}

/// Iterator returned from "stream" eval methods.
///
/// Yields &str items.
pub struct EvalListIter<'a,'b:'a>(JsonnetStringIter<'a,'b>);

impl<'a,'b> Iterator for EvalListIter<'a,'b> {
    type Item = &'a str;
    fn next(&mut self) -> Option<Self::Item> { self.0.next() }
}

impl<'a,'b> IntoIterator for &'b EvalList<'a> {
    type Item = &'b str;
    type IntoIter = EvalListIter<'b,'a>;
    fn into_iter(self) -> Self::IntoIter { self.iter() }
}

/// String literal style
#[derive(Debug,PartialEq,Eq)]
pub enum FmtString {
    /// Double quoted `"foo"`.
    Double,
    /// Single quoted `'foo'`.
    Single,
    /// Leave quoting as-is.
    Leave,
}

impl FmtString {
    fn to_char(self) -> c_int {
        let c = match self {
            FmtString::Double => 'd',
            FmtString::Single => 's',
            FmtString::Leave => 'l',
        };
        c as c_int
    }
}

impl Default for FmtString {
    fn default() -> FmtString { FmtString::Leave }
}

/// Comment style
#[derive(Debug,PartialEq,Eq)]
pub enum FmtComment {
    /// Hash comments (like shell).
    Hash,
    /// Double slash comments (like C++).
    Slash,
    /// Leave comments as-is.
    Leave,
}

impl FmtComment {
    fn to_char(self) -> c_int {
        let c = match self {
            FmtComment::Hash => 'h',
            FmtComment::Slash => 's',
            FmtComment::Leave => 'l',
        };
        c as c_int
    }
}

impl Default for FmtComment {
    fn default() -> FmtComment { FmtComment::Leave }
}

/// Return the version string of the Jsonnet interpreter.  Conforms to
/// [semantic versioning][1].
///
/// [1]: http://semver.org/
pub fn jsonnet_version() -> &'static str {
    let s = unsafe { CStr::from_ptr(jsonnet_sys::jsonnet_version()) };
    s.to_str().unwrap()
}

#[test]
fn test_version() {
    let s = jsonnet_version();
    println!("Got version: {}", s);
    // Should be 1.2.3 semver format
    assert_eq!(s.split('.').count(), 3);
}

/// Callback used to load imports.
struct ImportContext<'a, F> {
    vm: &'a JsonnetVm,
    cb: F,
}

#[cfg(unix)]
fn bytes2osstr(b: &[u8]) -> &OsStr {
    use std::os::unix::ffi::OsStrExt;
    OsStr::from_bytes(b)
}

/// Panics if os contains invalid utf8!
#[cfg(windows)]
fn bytes2osstr(b: &[u8]) -> &OsStr {
    let s = std::str::from_utf8(b).unwrap();
    OsStr::new(s)
}

fn cstr2osstr(cstr: &CStr) -> &OsStr {
    bytes2osstr(cstr.to_bytes())
}

#[cfg(unix)]
fn osstr2bytes(os: &OsStr) -> &[u8] {
    use std::os::unix::ffi::OsStrExt;
    os.as_bytes()
}

/// Panics if os contains invalid utf8!
#[cfg(windows)]
fn osstr2bytes(os: &OsStr) -> &[u8] {
    os.to_str().unwrap().as_bytes()
}

fn osstr2cstring<T: AsRef<OsStr>>(os: T) -> CString {
    let b = osstr2bytes(os.as_ref());
    CString::new(b).unwrap()
}

// `jsonnet_sys::JsonnetImportCallback`-compatible function that
// interprets `ctx` as an `ImportContext` and converts arguments
// appropriately.
extern fn import_callback<F>(ctx: *mut c_void, base: &c_char, rel: &c_char, found_here: &mut *mut c_char, success: &mut c_int) -> *mut c_char
where F: Fn(&JsonnetVm, &Path, &Path) -> Result<(PathBuf, String), String>
{
    let ctx = unsafe { &*(ctx as *mut ImportContext<F>) };
    let vm = ctx.vm;
    let callback = &ctx.cb;
    let base_path = Path::new(cstr2osstr(unsafe { CStr::from_ptr(base) }));
    let rel_path = Path::new(cstr2osstr(unsafe { CStr::from_ptr(rel) }));
    match callback(vm, base_path, rel_path) {
        Ok((found_here_path, contents)) => {
            *success = 1;

            let v = {
                // Note: PathBuf may not be valid utf8.
                let b = osstr2bytes(found_here_path.as_os_str());
                JsonnetString::from_bytes(vm, b)
            };
            *found_here = v.into_raw();

            JsonnetString::new(vm, &contents).into_raw()
        },
        Err(err) => {
            *success = 0;
            JsonnetString::new(vm, &err).into_raw()
        }
    }
}

/// Callback to provide native extensions to Jsonnet.
///
/// This callback should not have side-effects!  Jsonnet is a lazy
/// functional language and will call your function when you least
/// expect it, more times than you expect, or not at all.
struct NativeContext<'a, F> {
    vm: &'a JsonnetVm,
    argc: usize,
    cb: F,
}

// `jsonnet_sys::JsonnetNativeCallback`-compatible function that
// interprets `ctx` as a `NativeContext` and converts arguments
// appropriately.
extern fn native_callback<'a, F>(ctx: *mut libc::c_void, argv: *const *const JsonnetJsonValue, success: &mut c_int) -> *mut JsonnetJsonValue
where F: Fn(&'a JsonnetVm, &[JsonVal<'a>]) -> Result<JsonValue<'a>, String>
{
    let ctx = unsafe { &*(ctx as *mut NativeContext<F>) };
    let vm = ctx.vm;
    let callback = &ctx.cb;
    let args: Vec<_> = (0..ctx.argc)
        .map(|i| unsafe { JsonVal::from_ptr(vm, *argv.offset(i as isize)) })
        .collect();
    match callback(vm, &args) {
        Ok(v) => {
            *success = 1;
            v.into_raw()
        },
        Err(err) => {
            *success = 0;
            let ret = JsonValue::from_str(vm, &err);
            ret.into_raw()
        }
    }
}

/// Jsonnet virtual machine context.
pub struct JsonnetVm(*mut jsonnet_sys::JsonnetVm);

impl JsonnetVm {
    /// Create a new Jsonnet virtual machine.
    pub fn new() -> Self {
        let vm = unsafe { jsonnet_sys::jsonnet_make() };
        JsonnetVm(vm)
    }

    fn as_ptr(&self) -> *mut jsonnet_sys::JsonnetVm { self.0 }

    /// Set the maximum stack depth.
    pub fn max_stack(&mut self, v: u32) {
        unsafe { jsonnet_sys::jsonnet_max_stack(self.0, v as c_uint) }
    }

    /// Set the number of objects required before a garbage collection
    /// cycle is allowed.
    pub fn gc_min_objects(&mut self, v: u32) {
        unsafe { jsonnet_sys::jsonnet_gc_min_objects(self.0, v as c_uint) }
    }

    /// Run the garbage collector after this amount of growth in the
    /// number of objects.
    pub fn gc_growth_trigger(&mut self, v: f64) {
        unsafe { jsonnet_sys::jsonnet_gc_growth_trigger(self.0, v) }
    }

    /// Expect a string as output and don't JSON encode it.
    pub fn string_output(&mut self, v: bool) {
        unsafe { jsonnet_sys::jsonnet_string_output(self.0, v as c_int) }
    }


    /// Override the callback used to locate imports.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::path::{Path,PathBuf};
    /// use std::ffi::OsStr;
    /// use jsonnet::JsonnetVm;
    ///
    /// let mut vm = JsonnetVm::new();
    /// vm.import_callback(|_vm, base, rel| {
    ///    if rel.file_stem() == Some(OsStr::new("bar")) {
    ///       let newbase = base.into();
    ///       let contents = "2 + 3".to_owned();
    ///       Ok((newbase, contents))
    ///    } else {
    ///       Err("not found".to_owned())
    ///    }
    /// });
    ///
    /// {
    ///    let output = vm.evaluate_snippet("myimport", "import 'x/bar.jsonnet'").unwrap();
    ///    assert_eq!(output.to_string(), "5\n");
    /// }
    ///
    /// {
    ///    let result = vm.evaluate_snippet("myimport", "import 'x/foo.jsonnet'");
    ///    assert!(result.is_err());
    /// }
    /// ```
    pub fn import_callback<F>(&mut self, cb: F)
        where F: Fn(&JsonnetVm, &Path, &Path) -> Result<(PathBuf, String), String>
    {
        let ctx = ImportContext {
            vm: self,
            cb: cb,
        };
        unsafe {
            jsonnet_sys::jsonnet_import_callback(self.as_ptr(),
                                                 import_callback::<F> as *const _,
                                                 // TODO: ctx is leaked :(
                                                 Box::into_raw(Box::new(ctx)) as *mut _);
        }
    }

    /// Register a native extension.
    ///
    /// This will appear in Jsonnet as a function type and can be
    /// accessed from `std.native("foo")`.
    ///
    /// # Examples
    ///
    /// ```
    /// use jsonnet::{JsonnetVm, JsonVal, JsonValue};
    ///
    /// fn myadd<'a>(vm: &'a JsonnetVm, args: &[JsonVal<'a>]) -> Result<JsonValue<'a>, String> {
    ///    let a = try!(args[0].as_num().ok_or("Expected a number"));
    ///    let b = try!(args[1].as_num().ok_or("Expected a number"));
    ///    Ok(JsonValue::from_num(vm, a + b))
    /// }
    ///
    /// let mut vm = JsonnetVm::new();
    /// vm.native_callback("myadd", myadd, &["a", "b"]);
    ///
    /// {
    ///    let result = vm.evaluate_snippet("nativetest",
    ///       "std.native('myadd')(2, 3)");
    ///    assert_eq!(result.unwrap().as_str(), "5\n");
    /// }
    ///
    /// {
    ///    let result = vm.evaluate_snippet("nativefail",
    ///       "std.native('myadd')('foo', 'bar')");
    ///    assert!(result.is_err());
    /// }
    ///
    /// vm.native_callback("upcase", |vm, args| {
    ///       let s = try!(args[0].as_str().ok_or("Expected a string"));
    ///       Ok(JsonValue::from_str(vm, &s.to_uppercase()))
    ///    }, &["s"]);
    /// {
    ///    let result = vm.evaluate_snippet("nativeclosure",
    ///       "std.native('upcase')('foO')");
    ///    assert_eq!(result.unwrap().as_str(), "\"FOO\"\n");
    /// }
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `name` or `params` contain any embedded nul characters.
    pub fn native_callback<F>(&mut self, name: &str, cb: F, params: &[&str])
        where for<'a> F: Fn(&'a JsonnetVm, &[JsonVal<'a>]) -> Result<JsonValue<'a>, String>
    {
        let ctx = NativeContext {
            vm: self,
            argc: params.len(),
            cb: cb,
        };
        let cname = CString::new(name).unwrap();
        let cparams: Vec<_> = params.into_iter()
            .map(|&p| CString::new(p).unwrap())
            .collect();
        let cptrs: Vec<_> = cparams.iter()
            .map(|p| p.as_ptr())
            .chain(iter::once(ptr::null()))
            .collect();
        unsafe {
            jsonnet_sys::jsonnet_native_callback(self.as_ptr(),
                                                 cname.as_ptr(),
                                                 native_callback::<F> as *const _,
                                                 // TODO: ctx is leaked :(
                                                 Box::into_raw(Box::new(ctx)) as *mut _,
                                                 cptrs.as_slice().as_ptr());
        }
    }

    /// Bind a Jsonnet external var to the given string.
    ///
    /// # Panics
    ///
    /// Panics if `key` or `val` contain embedded nul characters.
    pub fn ext_var(&mut self, key: &str, val: &str) {
        let ckey = CString::new(key).unwrap();
        let cval = CString::new(val).unwrap();
        unsafe {
            jsonnet_sys::jsonnet_ext_var(self.0, ckey.as_ptr(), cval.as_ptr());
        }
    }

    /// Bind a Jsonnet external var to the given code.
    ///
    /// # Panics
    ///
    /// Panics if `key` or `code` contain embedded nul characters.
    pub fn ext_code(&mut self, key: &str, code: &str) {
        let ckey = CString::new(key).unwrap();
        let ccode = CString::new(code).unwrap();
        unsafe {
            jsonnet_sys::jsonnet_ext_code(self.0, ckey.as_ptr(), ccode.as_ptr());
        }
    }

    /// Bind a string top-level argument for a top-level parameter.
    ///
    /// # Panics
    ///
    /// Panics if `key` or `val` contain embedded nul characters.
    pub fn tla_var(&mut self, key: &str, val: &str) {
        let ckey = CString::new(key).unwrap();
        let cval = CString::new(val).unwrap();
        unsafe {
            jsonnet_sys::jsonnet_tla_var(self.0, ckey.as_ptr(), cval.as_ptr());
        }
    }

    /// Bind a code top-level argument for a top-level parameter.
    ///
    /// # Panics
    ///
    /// Panics if `key` or `code` contain embedded nul characters.
    pub fn tla_code(&mut self, key: &str, code: &str) {
        let ckey = CString::new(key).unwrap();
        let ccode = CString::new(code).unwrap();
        unsafe {
            jsonnet_sys::jsonnet_tla_code(self.0, ckey.as_ptr(), ccode.as_ptr());
        }
    }

    /// Indentation level when reformatting (number of spaces).
    pub fn fmt_indent(&mut self, n: u32) {
        unsafe {
            jsonnet_sys::jsonnet_fmt_indent(self.0, n as c_int);
        }
    }

    /// Maximum number of blank lines when reformatting.
    pub fn fmt_max_blank_lines(&mut self, n: u32) {
        unsafe {
            jsonnet_sys::jsonnet_fmt_max_blank_lines(self.0, n as c_int);
        }
    }

    /// Preferred style for string literals (`""` or `''`).
    pub fn fmt_string(&mut self, fmt: FmtString) {
        unsafe {
            jsonnet_sys::jsonnet_fmt_string(self.0, fmt.to_char());
        }
    }

    /// Preferred style for line comments (# or //).
    pub fn fmt_comment(&mut self, fmt: FmtComment) {
        unsafe {
            jsonnet_sys::jsonnet_fmt_comment(self.0, fmt.to_char());
        }
    }

    /// Whether to add an extra space on the inside of arrays.
    pub fn fmt_pad_arrays(&mut self, pad: bool) {
        unsafe {
            jsonnet_sys::jsonnet_fmt_pad_arrays(self.0, pad as c_int);
        }
    }

    /// Whether to add an extra space on the inside of objects.
    pub fn fmt_pad_objects(&mut self, pad: bool) {
        unsafe {
            jsonnet_sys::jsonnet_fmt_pad_objects(self.0, pad as c_int);
        }
    }

    /// Use syntax sugar where possible with field names.
    pub fn fmt_pretty_field_names(&mut self, sugar: bool) {
        unsafe {
            jsonnet_sys::jsonnet_fmt_pretty_field_names(self.0, sugar as c_int);
        }
    }

    /// Sort top-level imports in alphabetical order
    pub fn fmt_sort_import(&mut self, sort: bool) {
        unsafe {
            jsonnet_sys::jsonnet_fmt_sort_imports(self.0, sort as c_int);
        }
    }

    /// Reformat the Jsonnet input after desugaring.
    pub fn fmt_debug_desugaring(&mut self, reformat: bool) {
        unsafe {
            jsonnet_sys::jsonnet_fmt_debug_desugaring(self.0, reformat as c_int);
        }
    }

    /// Reformat a file containing Jsonnet code, return a Jsonnet string.
    ///
    /// # Panics
    ///
    /// Panics if `filename` contains embedded nul characters.
    pub fn fmt_file<'a,P>(&'a mut self, filename: P) -> Result<JsonnetString<'a>, Error<'a>>
        where P: AsRef<OsStr>
    {
        let fname = osstr2cstring(filename);
        let mut error = 1;
        let output = unsafe {
            let v = jsonnet_sys::jsonnet_fmt_file(self.0, fname.as_ptr(), &mut error);
            JsonnetString::from_ptr(self, v)
        };
        match error {
            0 => Ok(output),
            _ => Err(Error(output)),
        }
    }

    /// Reformat a string containing Jsonnet code, return a Jsonnet string.
    ///
    /// # Panics
    ///
    /// Panics if `filename` or `snippet` contain embedded nul characters.
    pub fn fmt_snippet<'a,P>(&'a mut self, filename: P, snippet: &str) -> Result<JsonnetString<'a>, Error<'a>>
        where P: AsRef<OsStr>
    {
        let fname = osstr2cstring(filename);
        let snippet = CString::new(snippet).unwrap();
        let mut error = 1;
        let output = unsafe {
            let v = jsonnet_sys::jsonnet_fmt_snippet(self.0, fname.as_ptr(), snippet.as_ptr(), &mut error);
            JsonnetString::from_ptr(self, v)
        };
        match error {
            0 => Ok(output),
            _ => Err(Error(output)),
        }
    }

    /// Set the number of lines of stack trace to display (None for unlimited).
    pub fn max_trace(&mut self, limit: Option<u32>) {
        let v = limit.unwrap_or(0);
        unsafe {
            jsonnet_sys::jsonnet_max_trace(self.0, v);
        }
    }

    /// Add to the default import callback's library search path.
    ///
    /// Search order is last to first, so more recently appended paths
    /// take precedence.
    ///
    /// # Panics
    ///
    /// Panics if `path` contains embedded nul characters.
    pub fn jpath_add<P>(&mut self, path: P)
        where P: AsRef<OsStr>
    {
        let v = osstr2cstring(path);
        unsafe {
            jsonnet_sys::jsonnet_jpath_add(self.0, v.as_ptr());
        }
    }

    /// Evaluate a file containing Jsonnet code, returning a JSON string.
    ///
    /// # Errors
    ///
    /// Returns any jsonnet error during evaluation.
    ///
    /// # Panics
    ///
    /// Panics if `filename` contains embedded nul characters.
    pub fn evaluate_file<'a,P>(&'a mut self, filename: P) -> Result<JsonnetString<'a>, Error<'a>>
        where P: AsRef<OsStr>
    {
        let fname = osstr2cstring(filename);
        let mut error = 1;
        let output = unsafe {
            let v = jsonnet_sys::jsonnet_evaluate_file(self.0, fname.as_ptr(), &mut error);
            JsonnetString::from_ptr(self, v)
        };
        match error {
            0 => Ok(output),
            _ => Err(Error(output)),
        }
    }

    /// Evaluate a string containing Jsonnet code, returning a JSON string.
    ///
    /// The `filename` argument is only used in error messages.
    ///
    /// # Errors
    ///
    /// Returns any jsonnet error during evaluation.
    ///
    /// # Panics
    ///
    /// Panics if `filename` or `snippet` contain embedded nul characters.
    pub fn evaluate_snippet<'a,P>(&'a mut self, filename: P, snippet: &str) -> Result<JsonnetString<'a>, Error<'a>>
        where P: AsRef<OsStr>
    {
        let fname = osstr2cstring(filename);
        let snip = CString::new(snippet).unwrap();
        let mut error = 1;
        let output = unsafe {
            let v = jsonnet_sys::jsonnet_evaluate_snippet(self.0, fname.as_ptr(), snip.as_ptr(), &mut error);
            JsonnetString::from_ptr(self, v)
        };
        match error {
            0 => Ok(output),
            _ => Err(Error(output)),
        }
    }

    /// Evaluate a file containing Jsonnet code, returning a number of
    /// named JSON files.
    ///
    /// # Errors
    ///
    /// Returns any jsonnet error during evaluation.
    ///
    /// # Panics
    ///
    /// Panics if `filename` contains embedded nul characters.
    pub fn evaluate_file_multi<'a,P>(&'a mut self, filename: P) -> Result<EvalMap<'a>, Error<'a>>
        where P: AsRef<OsStr>
    {
        let fname = osstr2cstring(filename);
        let mut error = 1;
        let output = unsafe {
            let v = jsonnet_sys::jsonnet_evaluate_file_multi(self.0, fname.as_ptr(), &mut error);
            JsonnetString::from_ptr(self, v)
        };
        match error {
            0 => Ok(EvalMap(output)),
            _ => Err(Error(output)),
        }
    }

    /// Evaluate a file containing Jsonnet code, returning a number of
    /// named JSON files.
    ///
    /// # Errors
    ///
    /// Returns any jsonnet error during evaluation.
    ///
    /// # Panics
    ///
    /// Panics if `filename` or `snippet` contain embedded nul characters.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    /// use jsonnet::JsonnetVm;
    ///
    /// let mut vm = JsonnetVm::new();
    /// let output = vm.evaluate_snippet_multi("multi",
    ///    "{'foo.json': 'foo', 'bar.json': 'bar'}").unwrap();
    ///
    /// let map: HashMap<_,_> = output.iter().collect();
    /// assert_eq!(*map.get("bar.json").unwrap(), "\"bar\"\n");
    /// ```
    pub fn evaluate_snippet_multi<'a,P>(&'a mut self, filename: P, snippet: &str) -> Result<EvalMap<'a>, Error<'a>>
        where P: AsRef<OsStr>
    {
        let fname = osstr2cstring(filename);
        let snippet = CString::new(snippet).unwrap();
        let mut error = 1;
        let output = unsafe {
            let v = jsonnet_sys::jsonnet_evaluate_snippet_multi(self.0, fname.as_ptr(), snippet.as_ptr(), &mut error);
            JsonnetString::from_ptr(self, v)
        };
        match error {
            0 => Ok(EvalMap(output)),
            _ => Err(Error(output)),
        }
    }

    /// Evaluate a file containing Jsonnet code, returning a number of
    /// JSON files.
    ///
    /// # Errors
    ///
    /// Returns any jsonnet error during evaluation.
    ///
    /// # Panics
    ///
    /// Panics if `filename` contains embedded nul characters.
    pub fn evaluate_file_stream<'a,P>(&'a mut self, filename: P) -> Result<EvalList<'a>, Error<'a>>
        where P: AsRef<OsStr>
    {
        let fname = osstr2cstring(filename);
        let mut error = 1;
        let output = unsafe {
            let v = jsonnet_sys::jsonnet_evaluate_file_stream(self.0, fname.as_ptr(), &mut error);
            JsonnetString::from_ptr(self, v)
        };
        match error {
            0 => Ok(EvalList(output)),
            _ => Err(Error(output)),
        }
    }

    /// Evaluate a string containing Jsonnet code, returning a number
    /// of JSON files.
    ///
    /// # Errors
    ///
    /// Returns any jsonnet error during evaluation.
    ///
    /// # Panics
    ///
    /// Panics if `filename` or `snippet` contain embedded nul characters.
    ///
    /// # Examples
    ///
    /// ```
    /// use jsonnet::JsonnetVm;
    ///
    /// let mut vm = JsonnetVm::new();
    /// let output = vm.evaluate_snippet_stream("stream",
    ///    "['foo', 'bar']").unwrap();
    ///
    /// let list: Vec<_> = output.iter().collect();
    /// assert_eq!(list, vec!["\"foo\"\n", "\"bar\"\n"]);
    /// ```
    pub fn evaluate_snippet_stream<'a,P>(&'a mut self, filename: P, snippet: &str) -> Result<EvalList<'a>, Error<'a>>
        where P: AsRef<OsStr>
    {
        let fname = osstr2cstring(filename);
        let snippet = CString::new(snippet).unwrap();
        let mut error = 1;
        let output = unsafe {
            let v = jsonnet_sys::jsonnet_evaluate_snippet_stream(self.0, fname.as_ptr(), snippet.as_ptr(), &mut error);
            JsonnetString::from_ptr(self, v)
        };
        match error {
            0 => Ok(EvalList(output)),
            _ => Err(Error(output)),
        }
    }
}

impl Drop for JsonnetVm {
    fn drop(&mut self) {
        assert!(!self.0.is_null());
        unsafe { jsonnet_sys::jsonnet_destroy(self.0) }
    }
}

#[test]
fn basic_eval() {
    let mut vm = JsonnetVm::new();
    let result = vm.evaluate_snippet("example", "'Hello ' + 'World'");
    println!("result is {:?}", result);
    assert!(result.is_ok());
    assert_eq!(result.unwrap().to_string(), "\"Hello World\"\n");
}

#[test]
fn basic_eval_err() {
    let mut vm = JsonnetVm::new();
    let result = vm.evaluate_snippet("example", "bogus");
    println!("result is {:?}", result);
    assert!(result.is_err());
    assert!(result.unwrap_err().contains("Unknown variable: bogus"));
}

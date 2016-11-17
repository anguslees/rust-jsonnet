extern crate libc;

use libc::{c_char, c_int, c_uint, size_t, c_void, c_double};

pub type JsonnetImportCallback =
    extern fn(ctx: *mut c_void, base: *const c_char, rel: *const c_char, found_here: *mut *mut c_char, success: *mut c_int) -> *mut c_char;

pub type JsonnetNativeCallback =
    extern fn(ctx: *mut c_void, argv: *const *const JsonnetJsonValue, success: *mut c_int) -> *mut JsonnetJsonValue;

pub enum JsonnetVm {}
pub enum JsonnetJsonValue {}

extern {
    pub fn jsonnet_version() -> *const c_char;

    pub fn jsonnet_make() -> *mut JsonnetVm;
    pub fn jsonnet_max_stack(vm: *mut JsonnetVm, v: c_uint);
    pub fn jsonnet_gc_min_objects(vm: *mut JsonnetVm, v: c_uint);
    pub fn jsonnet_gc_growth_trigger(vm: *mut JsonnetVm, v: c_double);
    pub fn jsonnet_string_output(vm: *mut JsonnetVm, v: c_int);

    pub fn jsonnet_json_extract_string(vm: *mut JsonnetVm, v: *const JsonnetJsonValue) -> *const c_char;
    pub fn jsonnet_json_extract_number(vm: *mut JsonnetVm, v: *const JsonnetJsonValue, out: *mut c_double) -> c_int;
    pub fn jsonnet_json_extract_bool(vm: *mut JsonnetVm, v: *const JsonnetJsonValue) -> c_int;
    pub fn jsonnet_json_extract_null(vm: *mut JsonnetVm, v: *const JsonnetJsonValue) -> c_int;

    pub fn jsonnet_json_make_string(vm: *mut JsonnetVm, v: *const c_char) -> *mut JsonnetJsonValue;
    pub fn jsonnet_json_make_number(vm: *mut JsonnetVm, v: c_double) -> *mut JsonnetJsonValue;
    pub fn jsonnet_json_make_bool(vm: *mut JsonnetVm, v: c_int) -> *mut JsonnetJsonValue;
    pub fn jsonnet_json_make_null(vm: *mut JsonnetVm) -> *mut JsonnetJsonValue;
    pub fn jsonnet_json_make_array(vm: *mut JsonnetVm) -> *mut JsonnetJsonValue;
    pub fn jsonnet_json_array_append(vm: *mut JsonnetVm, arr: *mut JsonnetJsonValue, v: *mut JsonnetJsonValue);
    pub fn jsonnet_json_make_object(vm: *mut JsonnetVm) -> *mut JsonnetJsonValue;
    pub fn jsonnet_json_object_append(vm: *mut JsonnetVm, obj: *mut JsonnetJsonValue, f: *const c_char, v: *mut JsonnetJsonValue);

    pub fn jsonnet_json_destroy(vm: *mut JsonnetVm, v: *mut JsonnetJsonValue);

    pub fn jsonnet_realloc(vm: *mut JsonnetVm, buf: *const c_char, sz: size_t) -> *mut c_char;
    pub fn jsonnet_import_callback(vm: *mut JsonnetVm, cb: *const JsonnetImportCallback, ctx: *mut c_void);
    pub fn jsonnet_native_callback(vm: *mut JsonnetVm, name: *const c_char, cb: *const JsonnetNativeCallback, ctx: *mut c_void, params: *const *const c_char);

    pub fn jsonnet_ext_var(vm: *mut JsonnetVm, key: *const c_char, val: *const c_char);
    pub fn jsonnet_ext_code(vm: *mut JsonnetVm, key: *const c_char, val: *const c_char);

    pub fn jsonnet_tla_var(vm: *mut JsonnetVm, key: *const c_char, val: *const c_char);
    pub fn jsonnet_tla_code(vm: *mut JsonnetVm, key: *const c_char, val: *const c_char);

    pub fn jsonnet_fmt_indent(vm: *mut JsonnetVm, n: c_int);
    pub fn jsonnet_fmt_max_blank_lines(vm: *mut JsonnetVm, n: c_int);
    pub fn jsonnet_fmt_string(vm: *mut JsonnetVm, c: c_int);
    pub fn jsonnet_fmt_comment(vm: *mut JsonnetVm, c: c_int);
    pub fn jsonnet_fmt_pad_arrays(vm: *mut JsonnetVm, v: c_int);
    pub fn jsonnet_fmt_pad_objects(vm: *mut JsonnetVm, v: c_int);
    pub fn jsonnet_fmt_pretty_field_names(vm: *mut JsonnetVm, v: c_int);
    pub fn jsonnet_fmt_debug_desugaring(vm: *mut JsonnetVm, v: c_int);
    pub fn jsonnet_fmt_file(vm: *mut JsonnetVm, filename: *const c_char, error: *mut c_int) -> *mut c_char;
    pub fn jsonnet_fmt_snippet(vm: *mut JsonnetVm, filename: *const c_char, snippet: *const c_char, error: *mut c_int) -> *mut c_char;

    pub fn jsonnet_max_trace(vm: *mut JsonnetVm, v: c_uint);

    pub fn jsonnet_jpath_add(vm: *mut JsonnetVm, v: *const c_char);

    pub fn jsonnet_evaluate_file(vm: *mut JsonnetVm, filename: *const c_char, error: *mut c_int) -> *mut c_char;
    pub fn jsonnet_evaluate_snippet(vm: *mut JsonnetVm, filename: *const c_char, snippet: *const c_char, error: *mut c_int) -> *mut c_char;
    pub fn jsonnet_evaluate_file_multi(vm: *mut JsonnetVm, filename: *const c_char, error: *mut c_int) -> *mut c_char;
    pub fn jsonnet_evaluate_snippet_multi(vm: *mut JsonnetVm, filename: *const c_char, snippet: *const c_char, error: *mut c_int) -> *mut c_char;
    pub fn jsonnet_evaluate_file_stream(vm: *mut JsonnetVm, filename: *const c_char, error: *mut c_int) -> *mut c_char;
    pub fn jsonnet_evaluate_snippet_stream(vm: *mut JsonnetVm, filename: *const c_char, snippet: *const c_char, error: *mut c_int) -> *mut c_char;

    pub fn jsonnet_destroy(vm: *mut JsonnetVm);
}

#[test]
fn basic_eval() {
    use std::ffi::{CStr, CString};

    let filename = CString::new("testdata").unwrap();
    let snippet = CString::new("40 + 2").unwrap();
    let expected = CString::new("42\n").unwrap();

    unsafe {
        let vm = jsonnet_make();

        let mut error = 1;
        let result = jsonnet_evaluate_snippet(vm, filename.as_ptr(), snippet.as_ptr(), &mut error);
        assert_eq!(error, 0);
        assert_eq!(CStr::from_ptr(result).to_bytes(), expected.as_bytes());

        jsonnet_realloc(vm, result, 0);
        jsonnet_destroy(vm);
    }
}

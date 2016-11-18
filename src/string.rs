use std::ffi::CStr;
use std::ops::Deref;
use std::{fmt,ptr,mem};
use std::marker::PhantomData;
use libc::{c_char, size_t};

use jsonnet_sys;
use super::JsonnetVm;

/// Rust wrapper for libjsonnet string values.
///
/// This string is allocated against a particular JsonnetVm, and may
/// not outlive the JsonentVm.  It is UTF-8, and may not contain
/// embedded nul characters (ie: it is javascript and C -safe).
pub struct JsonnetString<'a> {
    vm: &'a JsonnetVm,
    data: *mut c_char,
}

impl<'a> JsonnetString<'a> {
    /// Allocate a new JsonnetString and copy `v` into it.
    ///
    /// # Panics
    ///
    /// Panics if `v` contains an embedded nul character.
    pub fn new(vm: &'a JsonnetVm, v: &str) -> Self {
        JsonnetString::from_bytes(vm, v.as_bytes())
    }

    /// Allocate a new JsonnetString and copy `v` into it.
    ///
    /// # Panics
    ///
    /// Panics if `v` contains an embedded nul character.  In most
    /// cases, jsonnet requires strings to be utf8, so prefer
    /// `JsonnetString::new` over this function.
    pub fn from_bytes(vm: &'a JsonnetVm, v: &[u8]) -> Self {
        unsafe {
            let p = jsonnet_sys::jsonnet_realloc(vm.as_ptr(), ptr::null(), v.len() + 1);
            ptr::copy_nonoverlapping(v.as_ptr(), p as *mut u8, v.len());
            *(p.offset(v.len() as isize)) = 0;  // trailing nul for C string
            Self::from_ptr(vm, p)
        }
    }

    /// Construct a `JsonnetString` from a pointer returned from a
    /// low-level jsonnet C function.
    ///
    /// # Safety
    ///
    /// It is assumed that `p` points to a UTF-8 C string (ie: nul
    /// terminated).  It is up to the caller to ensure that `p` was
    /// indeed allocated by `vm`.
    pub unsafe fn from_ptr(vm: &'a JsonnetVm, p: *mut c_char) -> Self {
        JsonnetString{vm: vm, data: p}
    }

    fn realloc(&mut self, size: size_t) {
        unsafe {
            self.data = jsonnet_sys::jsonnet_realloc(self.vm.as_ptr(), self.data, size);
        }
    }

    /// Returns the contents as a `&str`.
    pub fn as_str(&self) -> &'a str {
        self.as_cstr().to_str().unwrap()
    }

    /// Returns the contents as a `&CStr`.
    pub fn as_cstr(&self) -> &'a CStr {
        unsafe { CStr::from_ptr(self.data) }
    }

    /// Returns the inner pointer to this jsonnet string.
    ///
    /// The returned pointer will be valid for as long as `self` is.
    pub fn as_ptr(&self) -> *const c_char { self.data }

    /// Transfer ownership to a C caller (presumably a jsonnet
    /// function).
    ///
    /// If you call this, it is up to you to ensure that the string is
    /// freed correctly (using the appropriate jsonnet function), or
    /// the memory will leak.
    pub fn into_raw(self) -> *mut c_char {
        let result = self.data;
        mem::forget(self);
        result
    }
}

impl<'a> Deref for JsonnetString<'a> {
    type Target = str;
    fn deref(&self) -> &str { self.as_str() }
}

impl<'a> fmt::Debug for JsonnetString<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(self.as_str(), f)
    }
}

impl<'a> fmt::Display for JsonnetString<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self.as_str(), f)
    }
}

impl<'a> Drop for JsonnetString<'a> {
    fn drop(&mut self) {
        self.realloc(0);
    }
}

impl<'a> PartialEq for JsonnetString<'a> {
    fn eq<'b>(&self, other: &JsonnetString<'b>) -> bool {
        self.as_str() == other.as_str()
    }
}

impl<'a> Eq for JsonnetString<'a> {}

#[test]
fn simple() {
    let vm = JsonnetVm::new();
    let s = JsonnetString::new(&vm, "1234");
    assert_eq!(s.as_str(), "1234");
    assert_eq!(s.as_cstr().to_bytes_with_nul(), b"1234\0");
}

/// An iterator over nul-separated multi-valued jsonnet string.
#[derive(Debug)]
pub struct JsonnetStringIter<'a,'b:'a> {
    cursor: *const c_char,
    marker: PhantomData<&'a JsonnetString<'b>>,
}

impl<'a,'b> JsonnetStringIter<'a,'b> {
    /// Caller takes responsibility for ensuring this actually is a
    /// multi-valued string.
    pub unsafe fn new(inner: &'a JsonnetString<'b>) -> Self {
        let cursor = inner.as_ptr();
        JsonnetStringIter{cursor: cursor, marker: PhantomData}
    }

    fn end(&self) -> bool {
        let c = unsafe { *self.cursor };
        c == 0
    }

    // Caller checks that cursor is actually pointing at another string.
    unsafe fn take_next(&mut self) -> &'a CStr {
        let ret = CStr::from_ptr(self.cursor);
        let len = ret.to_bytes_with_nul().len();
        self.cursor = self.cursor.offset(len as isize);
        ret
    }
}

impl<'a,'b> Iterator for JsonnetStringIter<'a,'b> {
    type Item = &'a str;
    fn next(&mut self) -> Option<Self::Item> {
        if self.end() {
            None
        } else {
            let v = unsafe { self.take_next() };
            Some(v.to_str().unwrap())
        }
    }
}

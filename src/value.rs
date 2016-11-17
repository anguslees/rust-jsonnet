use std::ffi::{CStr,CString};
use std::mem;
use std::marker;
use libc::{c_int};

use jsonnet_sys::{self,JsonnetJsonValue};
use super::JsonnetVm;

/// Rust wrapper for borrowed libjsonnet JSON values.
///
/// See `JsonValue` for the owned version.
pub struct JsonVal<'a> {
    vm: &'a JsonnetVm,
    value: *const JsonnetJsonValue,
}

impl<'a> JsonVal<'a> {
    /// Construct a `JsonVal` from a pointer returned from a
    /// low-level jsonnet C function.
    ///
    /// # Safety
    ///
    /// It is up to the caller to ensure that `p` was indeed allocated
    /// by `vm`.
    pub unsafe fn from_ptr(vm: &'a JsonnetVm, p: *const JsonnetJsonValue) -> Self {
        JsonVal{vm: vm, value: p}
    }

    /// Returns the inner pointer to this jsonnet value.
    ///
    /// The returned pointer will be valid for as long as `self` is.
    pub fn as_ptr(&self) -> *const JsonnetJsonValue { self.value }

    /// Returns the value, if it is a string.
    pub fn as_str(&self) -> Option<&str> {
        unsafe {
            let p = jsonnet_sys::jsonnet_json_extract_string(self.vm.as_ptr(), self.as_ptr());
            if p.is_null() {
                None
            } else {
                // Jsonnet asserts this is UTF-8
                Some(CStr::from_ptr(p).to_str().unwrap())
            }
        }
    }

    /// Returns the value, if it is a number.
    pub fn as_num(&self) -> Option<f64> {
        let mut number = 0.0;
        let ok = unsafe {
            jsonnet_sys::jsonnet_json_extract_number(self.vm.as_ptr(), self.as_ptr(), &mut number)
        };
        if ok != 0 {
            Some(number)
        } else {
            None
        }
    }

    /// Returns the value, if it is a bool.
    pub fn as_bool(&self) -> Option<bool> {
        let v = unsafe {
            jsonnet_sys::jsonnet_json_extract_bool(self.vm.as_ptr(), self.as_ptr())
        };
        match v {
            0 => Some(false),
            1 => Some(true),
            2 => None,
            _ => unreachable!(),
        }
    }

    /// Returns `Some(())` if the value is `null`.
    pub fn as_null(&self) -> Option<()> {
        let v = unsafe {
            jsonnet_sys::jsonnet_json_extract_null(self.vm.as_ptr(), self.as_ptr())
        };
        match v {
            0 => None,
            1 => Some(()),
            _ => unreachable!(),
        }
    }
}

/// Rust wrapper for owned libjsonnet JSON values.
///
/// These are used as return values from jsonnet native callbacks.
/// See `JsonVal` for the borrowed version.
pub struct JsonValue<'a> {
    vm: &'a JsonnetVm,
    value: *mut JsonnetJsonValue,
    _marker: marker::PhantomData<JsonnetJsonValue>,
}

impl<'a> JsonValue<'a> {
    /// Construct a `JsonValue` from a pointer returned from a
    /// low-level jsonnet C function.
    ///
    /// # Safety
    ///
    /// It is up to the caller to ensure that `p` was indeed allocated
    /// by `vm`.
    pub unsafe fn from_ptr(vm: &'a JsonnetVm, p: *mut JsonnetJsonValue) -> Self {
        JsonValue{vm: vm, value: p, _marker: marker::PhantomData}
    }

    /// Returns the inner pointer to this jsonnet value.
    ///
    /// The returned pointer will be valid for as long as `self` is.
    pub fn as_ptr(&self) -> *const JsonnetJsonValue { self.value }

    /// Returns the value, if it is a string.
    pub fn as_str(&self) -> Option<&str> {
        unsafe {
            let p = jsonnet_sys::jsonnet_json_extract_string(self.vm.as_ptr(), self.as_ptr());
            if p.is_null() {
                None
            } else {
                // Jsonnet asserts this is UTF-8
                Some(CStr::from_ptr(p).to_str().unwrap())
            }
        }
    }

    /// Returns the value, if it is a number.
    pub fn as_num(&self) -> Option<f64> {
        let mut number = 0.0;
        let ok = unsafe {
            jsonnet_sys::jsonnet_json_extract_number(self.vm.as_ptr(), self.as_ptr(), &mut number)
        };
        if ok != 0 {
            Some(number)
        } else {
            None
        }
    }

    /// Returns the value, if it is a bool.
    pub fn as_bool(&self) -> Option<bool> {
        let v = unsafe {
            jsonnet_sys::jsonnet_json_extract_bool(self.vm.as_ptr(), self.as_ptr())
        };
        match v {
            0 => Some(false),
            1 => Some(true),
            2 => None,
            _ => unreachable!(),
        }
    }

    /// Returns `Some(())` if the value is `null`.
    pub fn as_null(&self) -> Option<()> {
        let v = unsafe {
            jsonnet_sys::jsonnet_json_extract_null(self.vm.as_ptr(), self.as_ptr())
        };
        match v {
            0 => None,
            1 => Some(()),
            _ => unreachable!(),
        }
    }

    /// Convert the given UTF8 string to a JsonValue.
    ///
    /// # Panics
    ///
    /// Panics if `v` contains an embedded nul character.
    pub fn from_str(vm: &'a JsonnetVm, v: &str) -> Self {
        let cstr = CString::new(v).unwrap();
        unsafe {
            let p = jsonnet_sys::jsonnet_json_make_string(vm.as_ptr(), cstr.as_ptr());
            Self::from_ptr(vm, p)
        }
    }

    /// Convert the given double to a JsonValue.
    pub fn from_num(vm: &'a JsonnetVm, v: f64) -> Self {
        unsafe {
            let p = jsonnet_sys::jsonnet_json_make_number(vm.as_ptr(), v);
            Self::from_ptr(vm, p)
        }
    }

    /// Convert the given bool to a JsonValue.
    pub fn from_bool(vm: &'a JsonnetVm, v: bool) -> Self {
        unsafe {
            let p = jsonnet_sys::jsonnet_json_make_bool(vm.as_ptr(), v as c_int);
            Self::from_ptr(vm, p)
        }
    }

    /// Make a JsonValue representing `null`.
    pub fn null(vm: &'a JsonnetVm) -> Self {
        unsafe {
            let p = jsonnet_sys::jsonnet_json_make_null(vm.as_ptr());
            Self::from_ptr(vm, p)
        }
    }

    /// Convert the given list into a JsonValue array.
    pub fn from_array<T>(vm: &'a JsonnetVm, iter: T) -> Self
        where T: IntoIterator<Item=JsonValue<'a>>
    {
        unsafe {
            let p = jsonnet_sys::jsonnet_json_make_array(vm.as_ptr());
            for item in iter {
                jsonnet_sys::jsonnet_json_array_append(vm.as_ptr(), p, item.into_raw());
            }
            Self::from_ptr(vm, p)
        }
    }

    /// Convert the given map into a JsonValue object.
    pub fn from_map<'b,T>(vm: &'a JsonnetVm, iter: T) -> Self
        where T: IntoIterator<Item=(&'b CStr,JsonValue<'a>)>
    {
        unsafe {
            let p = jsonnet_sys::jsonnet_json_make_object(vm.as_ptr());
            for (f, v) in iter {
                jsonnet_sys::jsonnet_json_object_append(vm.as_ptr(),
                                                        p,
                                                        f.as_ptr(),
                                                        v.into_raw());
            }
            Self::from_ptr(vm, p)
        }
    }

    /// Transfer ownership to a C caller (presumably a jsonnet
    /// function).
    ///
    /// If you call this, it is up to you to ensure that the value is
    /// freed correctly (using the appropriate jsonnet function), or
    /// the memory will leak.
    pub fn into_raw(self) -> *mut JsonnetJsonValue {
        let result = self.value;
        mem::forget(self);
        result
    }
}

impl<'a> Drop for JsonValue<'a> {
    fn drop(&mut self) {
        unsafe {
            jsonnet_sys::jsonnet_json_destroy(self.vm.as_ptr(), self.value);
        }
    }
}

// Copyright (c) 2019 Sequence Planner
// SPDX-License-Identifier: Apache-2.0 AND MIT
// Adapted from https://github.com/sequenceplanner/r2r/blob/89cec03d07a1496a225751159cbc7bfb529d9dd1/r2r/src/utils.rs
// Further adapted from https://github.com/mvukov/rules_ros2/pull/371

use std::{ffi::CString, sync::Mutex};

use crate::rcl_bindings::*;

// Used to protect calls to rcl/rcutils in case those functions manipulate global variables
static LOG_GUARD: Mutex<()> = Mutex::new(());

/// Calls the underlying rclutils logging function
/// Don't call this directly, use the logging macros instead.
///
/// # Panics
///
/// This function might panic in the following scenarios:
/// - when called if the lock is already held by the current thread.
/// - if the construction of CString objects used to create the log output fail,
///   although, this highly unlikely to occur in most cases
#[doc(hidden)]
pub fn log(msg: &str, logger_name: &str, file: &str, line: u32, severity: LogSeverity) {
    // currently not possible to get function name in rust.
    // see https://github.com/rust-lang/rfcs/pull/2818
    let function = CString::new("").unwrap();
    let file = CString::new(file).unwrap();
    let location = rcutils_log_location_t {
        function_name: function.as_ptr(),
        file_name: file.as_ptr(),
        line_number: line as usize,
    };
    let format = CString::new("%s").unwrap();
    let logger_name = CString::new(logger_name)
        .expect("Logger name is a valid c style string, e.g. check for extraneous null characters");
    let message = CString::new(msg)
        .expect("Valid c style string required, e.g. check for extraneous null characters");
    let severity = severity.to_native();

    let _guard = LOG_GUARD.lock().unwrap();
    // SAFETY: Global variables are protected via LOG_GUARD, no other preconditions are required
    unsafe {
        rcutils_log(
            &location,
            severity as i32,
            logger_name.as_ptr(),
            format.as_ptr(),
            message.as_ptr(),
        );
    }
}

/// Logging severity
#[doc(hidden)]
pub enum LogSeverity {
    Unset,
    Debug,
    Info,
    Warn,
    Error,
    Fatal,
}

impl LogSeverity {
    fn to_native(&self) -> RCUTILS_LOG_SEVERITY {
        use crate::rcl_bindings::rcl_log_severity_t::*;
        match self {
            LogSeverity::Unset => RCUTILS_LOG_SEVERITY_UNSET,
            LogSeverity::Debug => RCUTILS_LOG_SEVERITY_DEBUG,
            LogSeverity::Info => RCUTILS_LOG_SEVERITY_INFO,
            LogSeverity::Warn => RCUTILS_LOG_SEVERITY_WARN,
            LogSeverity::Error => RCUTILS_LOG_SEVERITY_ERROR,
            LogSeverity::Fatal => RCUTILS_LOG_SEVERITY_FATAL,
        }
    }
}

/// A helper macro to log the message.
#[macro_export]
macro_rules! __impl_log {
    ($logger_name:expr, $msg:expr, $file:expr, $line:expr, $severity:expr) => {{
        $crate::log(
            &std::fmt::format($msg),
            $logger_name,
            $file,
            $line,
            $severity,
        );
    }};
}

/// Debug log message.
#[macro_export]
macro_rules! log_debug {
    ($logger_name:expr, $($args:tt)*) => {{
        $crate::__impl_log!($logger_name, format_args!($($args)*),
                            file!(), line!(), $crate::LogSeverity::Debug)
    }}
}

/// Info log message.
#[macro_export]
macro_rules! log_info {
    ($logger_name:expr, $($args:tt)*) => {{
        $crate::__impl_log!($logger_name, format_args!($($args)*),
                            file!(), line!(), $crate::LogSeverity::Info)
    }}
}

/// Warning log message.
#[macro_export]
macro_rules! log_warn {
    ($logger_name:expr, $($args:tt)*) => {{
        $crate::__impl_log!($logger_name, format_args!($($args)*),
                            file!(), line!(), $crate::LogSeverity::Warn)
    }}
}

/// Error log message.
#[macro_export]
macro_rules! log_error {
    ($logger_name:expr, $($args:tt)*) => {{
        $crate::__impl_log!($logger_name, format_args!($($args)*),
                            file!(), line!(), $crate::LogSeverity::Error)
    }}
}

/// Fatal log message.
#[macro_export]
macro_rules! log_fatal {
    ($logger_name:expr, $($args:tt)*) => {{
        $crate::__impl_log!($logger_name, format_args!($($args)*),
                            file!(), line!(), $crate::LogSeverity::Fatal)
    }}
}

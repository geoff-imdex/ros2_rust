use std::sync::{Arc, Mutex, OnceLock, Weak};

use crate::{
    rcl_bindings::*,
    RclrsError, ToResult, ENTITY_LIFECYCLE_MUTEX,
};

struct LoggingConfiguration {
    lifecycle: Mutex<Weak<LoggingLifecycle>>,
}

pub(crate) struct LoggingLifecycle;

impl LoggingLifecycle {
    fn new(args: &rcl_arguments_t) -> Result<Self, RclrsError> {
        // SAFETY:
        // * Lock the mutex as we cannot guarantee that rcl_* functions are protecting their global variables
        // * This is only called by Self::configure, which requires that a valid context was passed to it
        // * No other preconditions for calling this function
        unsafe {
            let allocator = rcutils_get_default_allocator();
            let _lock = ENTITY_LIFECYCLE_MUTEX.lock().unwrap();
            rcl_logging_configure(args, &allocator).ok()?;
        }
        Ok(Self)
    }

    /// SAFETY: Ensure rcl_context_t is valid before passing it in.
    pub(crate) unsafe fn configure(
        context: &rcl_context_t,
    ) -> Result<Arc<LoggingLifecycle>, RclrsError> {
        static CONFIGURATION: OnceLock<LoggingConfiguration> = OnceLock::new();
        let configuration = CONFIGURATION.get_or_init(|| LoggingConfiguration {
            lifecycle: Mutex::new(Weak::new()),
        });

        let mut lifecycle = configuration.lifecycle.lock().unwrap();
        if let Some(arc_lifecycle) = lifecycle.upgrade() {
            return Ok(arc_lifecycle);
        }
        let arc_lifecycle = Arc::new(LoggingLifecycle::new(&context.global_arguments)?);
        *lifecycle = Arc::downgrade(&arc_lifecycle);
        Ok(arc_lifecycle)
    }
}

impl Drop for LoggingLifecycle {
    fn drop(&mut self) {
        let _lock = ENTITY_LIFECYCLE_MUTEX.lock().unwrap();
        unsafe {
            rcl_logging_fini();
        }
    }
}

pub(crate) mod log_handler {
    //! This module provides a way to customize how log output is handled. For
    //! now we are not making this a public API and are only using it for tests
    //! in rclrs. We can consider making it public in the future, but we should
    //! put more consideration into the API before doing so.

    use std::{
        sync::OnceLock,
        time::Instant,
    };

    use crate::{
        rcl_bindings::*, LogSeverity,
    };

    /// Global variable that allows a custom log handler to be set. This log
    /// handler will be applied throughout the entire application and cannot be
    /// undone. If you want to be able to change the log handler over the
    /// lifetime of your application, you should design your own custom handler
    /// with an Arc<Mutex<T>> inside that allows its behavior to be modified.
    static LOGGING_OUTPUT_HANDLER: OnceLock<RawLogHandler> = OnceLock::new();

    /// Alias for an arbitrary log handler that is compatible with raw rcl types
    pub(crate) type RawLogHandler = Box<dyn Fn(
        *const rcutils_log_location_t, // location
        std::os::raw::c_int, // severity
        *const std::os::raw::c_char, // logger name
        rcutils_time_point_value_t, // timestamp
        *const std::os::raw::c_char, // message
        *mut rcutils_char_array_t, // logging_output
    ) + 'static + Send + Sync>;

    /// Alias for an abitrary idiomatic log handler
    pub(crate) type LogHandler = Box<dyn Fn(
        LogLocation,
        LogSeverity,
        &str, // logger name
        Instant, // timestamp
        &str, // message

    ) + 'static + Send + Sync>;

    /// Rust-idiomatic representation of the location of a log
    pub(crate) struct LogLocation<'a> {
        pub function_name: &'a str,
        pub file_name: &'a str,
        pub line_number: usize,
    }

    /// Set an idiomatic log hander
    pub(crate) fn set_logging_output_handler(
        handler: LogHandler,
    ) -> Result<(), RawLogHandler> {
        let raw_handler = Box::new(
            |
                location: *const rcutils_log_location_t,
                severity: std::os::raw::c_int,
                logger_name: *const std::os::raw::c_char,
                timestamp: rcutils_time_point_value_t,
                message: *const std::os::raw::c_char,
                logging_output: *mut rcutils_char_array_t,
            | {

            }
        );

        set_raw_logging_output_handler(raw_handler)
    }

    /// Set the raw value for the logging output handler
    pub(crate) fn set_raw_logging_output_handler(
        handler: RawLogHandler,
    ) -> Result<(), RawLogHandler> {
        LOGGING_OUTPUT_HANDLER.set(handler)
    }
}

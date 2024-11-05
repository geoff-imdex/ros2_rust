use std::{
    sync::{Arc, Mutex, OnceLock, Weak},
    time::Instant,
};

use crate::{
    rcl_bindings::*,
    RclrsError, ToResult, ENTITY_LIFECYCLE_MUTEX, LogSeverity,
};

struct LoggingConfiguration {
    lifecycle: Mutex<Weak<LoggingLifecycle>>,
}

pub(crate) struct LoggingLifecycle {
    // Keep the pointer
    handler: Option<LoggingOutputHandler>,
}

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

pub struct LogLocation<'a> {
    pub function_name: &'a str,
    pub file_name: &'a str,
    pub line_number: usize,
}

pub type RawLogHandler = Box<dyn Fn(
    *const rcutils_log_location_t, // location
    std::os::raw::c_int, // severity
    *const std::os::raw::c_char, // logger name
    rcutils_time_point_value_t, // timestamp
    *const std::os::raw::c_char, // message
    *mut rcutils_char_array_t, // logging_output
) + 'static + Send + Sync>;

static LOGGING_OUTPUT_HANDLER: OnceLock<RawLogHandler> = OnceLock::new();

pub fn set_raw_logging_output_handler(

) -> Result<(), RawLogHandler> {
    Ok(())
}

pub type LogHandler = Box<dyn Fn(
    LogLocation,
    LogSeverity,
    &str, // logger name
    Instant, // timestamp
    &str, // message

) + 'static + Send + Sync>;

pub fn set_logging_output_handler(

) -> Result<(),  {

}

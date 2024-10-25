use crate::{
    clock::Clock,
    rcl_bindings::{
        rcl_get_zero_initialized_timer, rcl_timer_fini, rcl_timer_init, rcl_timer_t,
        rcutils_get_default_allocator,
    },
    NodeHandle, RclrsError, ToResult, ENTITY_LIFECYCLE_MUTEX,
};
use std::{
    sync::{atomic::AtomicBool, Arc, Mutex, MutexGuard},
    time::Duration,
};

// SAFETY: The functions accessing this type, including drop(), shouldn't care
// about the thread they are running in (partly because they're protected by mutex).
// Therefore, this type can be safely sent to another thread.
unsafe impl Send for rcl_timer_t {}

/// Manage the lifecycle of an `rcl_timer_t`, including managing its dependencies
/// on `rcl_clock_t` and `rcl_context_t` by ensuring that these dependencies are
/// [dropped after][1] the `rcl_timer_t`.
///
/// [1]: <https://doc.rust-lang.org/reference/destructors.html>
pub(crate) struct TimerHandle {
    rcl_timer: Mutex<rcl_timer_t>,
    clock: Clock,
    node_handle: Arc<NodeHandle>,
    pub(crate) in_use_by_wait_set: Arc<AtomicBool>,
}

impl TimerHandle {
    pub(crate) fn lock(&self) -> MutexGuard<rcl_timer_t> {
        self.rcl_timer.lock().unwrap()
    }
}

impl Drop for TimerHandle {
    fn drop(&mut self) {
        let rcl_timer = self.rcl_timer.get_mut().unwrap();
        let _lifecycle_lock = ENTITY_LIFECYCLE_MUTEX.lock().unwrap();
        // SAFETY: The entity lifecycle mutex is locked to protect against the risk of
        // global variables in the rmw implementation being unsafely modified during cleanup.
        unsafe {
            rcl_timer_fini(rcl_timer);
        }
    }
}

/// Trait to be implemented by concrete [`Timer`]s.
pub(crate) trait TimerBase: Send + Sync {
    /// Internal function to get a reference to the `rcl` handle.
    fn handle(&self) -> &TimerHandle;
    /// Tries to call the timer and run the associated callback.
    fn execute(&self) -> Result<(), RclrsError>;
}

struct Timer {
    callback: Arc<dyn Fn(&mut Timer) + Send + Sync>,
    handle: TimerHandle,
}

impl Timer {
    pub(crate) fn new<F>(
        node_handle: Arc<NodeHandle>,
        clock: Clock,
        period: &Duration,
        callback: F,
    ) -> Result<Self, RclrsError>
    where
        F: Fn(&mut Timer) + 'static + Send + Sync,
    {
        // Move the callback to our reference counted container so rcl_callback can use it
        let callback = Arc::new(callback);

        // SAFETY: Getting a zero-initialized value is always safe.
        let mut rcl_timer = unsafe { rcl_get_zero_initialized_timer() };

        let clock_clone = clock.rcl_clock.clone();
        let mut rcl_clock = clock_clone.lock().unwrap();

        let node_handle_clone = node_handle.clone();
        let mut rcl_context = node_handle_clone.context_handle.rcl_context.lock().unwrap();

        // core::time::Duration will always be >= 0, so no need to check for negatives.
        let period_nanos = period.as_nanos() as i64;

        // SAFETY: No preconditions for this function.
        let allocator = unsafe { rcutils_get_default_allocator() };
        {
            let _lifecycle_lock = ENTITY_LIFECYCLE_MUTEX.lock().unwrap();
            unsafe {
                // SAFETY:
                // * The rcl_timer is zero-initialized as mandated by this function.
                // * The rcl_clock is kept alive by the Clock within TimerHandle because it is
                //   a dependency of the timer.
                // * The rcl_context is kept alive by the NodeHandle within TimerHandle because
                //   it is a dependency of the timer.
                // * The period is copied into this function so it can be dropped afterwards.
                // * The callback is None / nullptr so doesn't need to be kept alive.
                // * The entity lifecycle mutex is locked to protect against the risk of global
                //   variables in the rmw implementation being unsafely modified during initialization.
                rcl_timer_init(
                    &mut rcl_timer,
                    &mut *rcl_clock,
                    &mut *rcl_context,
                    period_nanos,
                    None,
                    allocator,
                )
                .ok()?;
            }
        }

        Ok(Self {
            callback,
            handle: TimerHandle {
                rcl_timer: Mutex::new(rcl_timer),
                clock,
                node_handle,
                in_use_by_wait_set: Arc::new(AtomicBool::new(false)),
            },
        })
    }
}

impl TimerBase for Timer {
    fn handle(&self) -> &TimerHandle {
        &self.handle
    }

    fn execute(&self) -> Result<(), RclrsError> {
        // let mut callback = self.callback.clone();
        // callback(&mut self);
        Ok(())
    }
}

// tests: timers with 0 periods should return immediately, could be a good test for the timer

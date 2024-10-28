use crate::{
    clock::Clock,
    rcl_bindings::{
        rcl_get_zero_initialized_timer, rcl_timer_call, rcl_timer_cancel,
        rcl_timer_exchange_period, rcl_timer_fini, rcl_timer_get_period,
        rcl_timer_get_time_since_last_call, rcl_timer_get_time_until_next_call, rcl_timer_init,
        rcl_timer_is_canceled, rcl_timer_is_ready, rcl_timer_reset, rcl_timer_t,
        rcutils_get_default_allocator,
    },
    NodeHandle, RclrsError, ToResult, ENTITY_LIFECYCLE_MUTEX,
};
use std::{
    i64,
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
pub struct TimerHandle {
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

pub struct Timer {
    callback: Arc<dyn Fn(&mut Timer) + Send + Sync>,
    handle: TimerHandle,
}

impl Timer {
    /// Creates a new `Timer` with the given period and callback.
    /// Periods greater than i64::MAX nanoseconds will saturate to i64::MAX.
    pub(crate) fn new<F>(
        node_handle: Arc<NodeHandle>,
        clock: Clock,
        period: Duration,
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
        let period_nanos = i64::try_from(period.as_nanos()).unwrap_or(i64::MAX);

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

    /// Calculates if the timer is ready to be called.
    /// Returns true if the timer is due or past due to be called.
    pub fn is_ready(&self) -> Result<bool, RclrsError> {
        let mut timer = self.handle.lock();
        let mut is_ready = false;
        // SAFETY:
        // * The timer is initialized, which is guaranteed by the constructor.
        // * The is_ready pointer is allocated on the stack and is valid for the duration of this function.
        unsafe {
            rcl_timer_is_ready(&mut *timer, &mut is_ready).ok()?;
        }
        Ok(is_ready)
    }

    /// Get the time until the next call of the timer is due. Saturates to 0 if the timer is ready.
    pub fn time_until_next_call(&self) -> Result<Duration, RclrsError> {
        let mut timer = self.handle.lock();
        let mut remaining_time = 0;
        // SAFETY:
        // * The timer is initialized, which is guaranteed by the constructor.
        // * The remaining_time pointer is allocated on the stack and is valid for the duration of this function.
        unsafe {
            rcl_timer_get_time_until_next_call(&mut *timer, &mut remaining_time).ok()?;
        }
        Ok(Duration::from_nanos(
            u64::try_from(remaining_time).unwrap_or(0),
        ))
    }

    /// Get the time since the last call of the timer.
    /// Calling this function within a callback will not return the time since the
    /// previous call but instead the time since the current callback was called.
    /// Saturates to 0 if the timer was last called in the future (i.e. the clock jumped).
    pub fn time_since_last_call(&self) -> Result<Duration, RclrsError> {
        let mut timer = self.handle.lock();
        let mut elapsed_time = 0;
        // SAFETY:
        // * The timer is initialized, which is guaranteed by the constructor.
        // * The elapsed_time pointer is allocated on the stack and is valid for the duration of this function.
        unsafe {
            rcl_timer_get_time_since_last_call(&mut *timer, &mut elapsed_time).ok()?;
        }
        Ok(Duration::from_nanos(
            u64::try_from(elapsed_time).unwrap_or(0),
        ))
    }

    /// Get the period of the timer.
    pub fn get_period(&self) -> Result<Duration, RclrsError> {
        let timer = self.handle.lock();
        let mut period = 0;
        // SAFETY:
        // * The timer is initialized, which is guaranteed by the constructor.
        // * The period pointer is allocated on the stack and is valid for the duration of this function.
        unsafe {
            rcl_timer_get_period(&*timer, &mut period).ok()?;
        }
        // The period should never be negative as we only expose (unsigned) Duration structs
        // for setting, but if it is, saturate to 0.
        Ok(Duration::from_nanos(u64::try_from(period).unwrap_or(0)))
    }

    /// Set the period of the timer. Periods greater than i64::MAX nanoseconds will saturate to i64::MAX.
    pub fn set_period(&self, period: Duration) -> Result<(), RclrsError> {
        let timer = self.handle.lock();
        let new_period = i64::try_from(period.as_nanos()).unwrap_or(i64::MAX);
        let mut old_period = 0;
        // SAFETY:
        // * The timer is initialized, which is guaranteed by the constructor.
        // * The new_period is copied into this function so it can be dropped afterwards.
        // * The old_period pointer is allocated on the stack and is valid for the duration of this function.
        unsafe {
            rcl_timer_exchange_period(&*timer, new_period, &mut old_period).ok()?;
        }
        Ok(())
    }

    /// Cancel the timer so it will no longer be fired by the waitset. Can be restarted with [`reset`][1].
    ///
    /// [1]: crate::timer::Timer::reset
    pub fn cancel(&self) -> Result<(), RclrsError> {
        let mut timer = self.handle.lock();
        // SAFETY: The timer is initialized, which is guaranteed by the constructor.
        unsafe {
            rcl_timer_cancel(&mut *timer).ok()?;
        }
        Ok(())
    }

    /// Check if the timer has been cancelled.
    pub fn is_canceled(&self) -> Result<bool, RclrsError> {
        let timer = self.handle.lock();
        let mut cancelled = false;
        // SAFETY:
        // * The timer is initialized, which is guaranteed by the constructor.
        // * The new_period is copied into this function so it can be dropped afterwards.
        // * The old_period pointer is allocated on the stack and is valid for the duration of this function.
        unsafe {
            rcl_timer_is_canceled(&*timer, &mut cancelled).ok()?;
        }
        Ok(cancelled)
    }

    /// Set the timer's last call time to now. Additionally marks cancelled timers as not-cancelled.
    pub fn reset(&self) -> Result<(), RclrsError> {
        let mut timer = self.handle.lock();
        // SAFETY: The timer is initialized, which is guaranteed by the constructor.
        unsafe {
            rcl_timer_reset(&mut *timer).ok()?;
        }
        Ok(())
    }

    /// Internal function to check the timer is still valid and set the last call time in rcl.
    fn call_rcl(&self) -> Result<(), RclrsError> {
        let mut timer = self.handle.lock();
        // SAFETY: Safe if the timer is initialized, which is guaranteed by the constructor.
        unsafe {
            rcl_timer_call(&mut *timer).ok()?;
        }
        Ok(())
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

// Timer.rs does very little other than call rcl functions.
// To keep these tests easy to maintain, most of them just check the rcl functions
// can be called without returning errors.
#[cfg(test)]
mod tests {
    use std::time::Duration;

    use crate::{create_node, Context};

    use super::Timer;

    // Pass in a new node name each time to avoid logging conflicts.
    fn new_timer(node_name: &str) -> Timer {
        let node = create_node(&Context::new([]).unwrap(), node_name).unwrap();

        let timer = Timer::new(
            node.handle.clone(),
            node.get_clock(),
            Duration::from_secs(0),
            |_| {},
        );

        timer.expect("Timer::new should not return an error")
    }

    #[test]
    fn creation() {
        let _ = new_timer("test_timer_creation");
    }

    #[test]
    fn is_ready() {
        let timer = new_timer("test_timer_is_ready");

        // Period is 0, so the timer should be already ready
        timer
            .is_ready()
            .expect("Timer::is_ready should not return an error");
    }

    #[test]
    fn time_until_next_call() {
        let timer = new_timer("test_timer_next_call");

        timer
            .time_until_next_call()
            .expect("Timer::time_until_next_call should not error");
    }

    #[test]
    fn time_since_last_call() {
        let timer = new_timer("test_timer_last_call");

        timer
            .time_since_last_call()
            .expect("Timer::time_since_last_call should not error");
    }

    #[test]
    fn update_period() {
        let timer = new_timer("test_timer_update_period");

        let new_period = Duration::from_millis(100);
        timer
            .set_period(new_period.clone())
            .expect("Timer::set_period should not error");

        let retrieved_period = timer.get_period().unwrap();

        assert_eq!(new_period, retrieved_period);
    }

    #[test]
    fn cancel_timer() {
        let timer = new_timer("test_timer_cancel");

        assert!(!timer.is_canceled().unwrap());

        timer.cancel().unwrap();

        assert!(timer.is_canceled().unwrap());
    }

    #[test]
    fn reset_cancelled_timer() {
        let timer = new_timer("test_timer_reset");
        timer.cancel().unwrap();

        timer.reset().unwrap();

        assert!(!timer.is_canceled().unwrap());
    }
}

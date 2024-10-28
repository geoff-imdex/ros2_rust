use crate::{
    clock::Clock,
    rcl_bindings::{
        rcl_get_zero_initialized_timer, rcl_timer_call, rcl_timer_cancel,
        rcl_timer_exchange_period, rcl_timer_fini, rcl_timer_get_period,
        rcl_timer_get_time_since_last_call, rcl_timer_get_time_until_next_call, rcl_timer_init,
        rcl_timer_is_canceled, rcl_timer_is_ready, rcl_timer_reset, rcl_timer_t,
        rcutils_get_default_allocator,
    },
    Context, ContextHandle, RclReturnCode, RclrsError, ToResult, ENTITY_LIFECYCLE_MUTEX,
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
    _clock: Clock,
    _context_handle: Arc<ContextHandle>,
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
pub trait TimerBase: Send + Sync {
    /// Internal function to get a reference to the `rcl` handle.
    fn handle(&self) -> &TimerHandle;
    /// Tries to call the timer and run the associated callback.
    /// Timers are allowed to modify themselves while being executed.
    fn execute(&mut self) -> Result<(), RclrsError>;
}

/// A struct for triggering a callback at regular intervals.
///
/// If created via [`Node::create_timer()`][1], calling [`spin_once`][2] or [`spin`][3]
/// on the timer's node will wait until the configured period of time has passed since
/// the timer was last called (or since it was created) before triggering the timer's callback.
///
/// If created via [`Timer::new`], [`is_ready`][4] must be polled until the timer has
/// expired, after which [`execute`][5] must be called to trigger the timer's callback.
/// The timer can also be added to a [`WaitSet`][6] to block until it is ready.
///
/// [1]: crate::Node::create_timer
/// [2]: crate::spin_once
/// [3]: crate::spin
/// [4]: crate::Timer::is_ready
/// [5]: crate::Timer::execute
/// [6]: crate::WaitSet
pub struct Timer {
    callback: Arc<Mutex<dyn FnMut(&mut Timer) + Send + Sync>>,
    handle: TimerHandle,
}

impl Timer {
    /// Creates a new `Timer` with the given period and callback.
    /// Periods greater than i64::MAX nanoseconds will saturate to i64::MAX.
    ///
    /// Note that most of the time [`Node::create_timer`][1] is the better way to make
    /// a new timer, as that will allow the timer to be triggered by spinning the node.
    /// Timers created with [`Timer::new`] must be checked and executed by the user.
    ///
    /// [1]: crate::Node::create_timer
    pub fn new<F>(
        context: &Context,
        clock: Clock,
        period: Duration,
        callback: F,
    ) -> Result<Self, RclrsError>
    where
        F: FnMut(&mut Timer) + 'static + Send + Sync,
    {
        Timer::new_with_context_handle(Arc::clone(&context.handle), clock, period, callback)
    }

    /// Version of [`Timer::new`] that takes a context handle directly.
    pub(crate) fn new_with_context_handle<F>(
        context_handle: Arc<ContextHandle>,
        clock: Clock,
        period: Duration,
        callback: F,
    ) -> Result<Self, RclrsError>
    where
        F: FnMut(&mut Timer) + 'static + Send + Sync,
    {
        let callback = Arc::new(Mutex::new(callback));

        // SAFETY: Getting a zero-initialized value is always safe.
        let mut rcl_timer = unsafe { rcl_get_zero_initialized_timer() };

        let clock_clone = clock.rcl_clock.clone();
        let mut rcl_clock = clock_clone.lock().unwrap();

        let context_handle_clone = context_handle.clone();
        let mut rcl_context = context_handle_clone.rcl_context.lock().unwrap();

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
                // * The rcl_context is kept alive by the ContextHandle within TimerHandle because
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
                _clock: clock,
                _context_handle: context_handle,
                in_use_by_wait_set: Arc::new(AtomicBool::new(false)),
            },
        })
    }

    /// Calculates if the timer is ready to be called.
    /// Returns true if the timer is due or past due to be called.
    /// Returns false if the timer is not yet due or has been canceled.
    pub fn is_ready(&self) -> bool {
        let mut timer = self.handle.lock();
        let mut is_ready = false;
        // SAFETY:
        // * The timer is initialized, which is guaranteed by the constructor.
        // * The is_ready pointer is allocated on the stack and is valid for the duration of this function.
        let ret = unsafe { rcl_timer_is_ready(&mut *timer, &mut is_ready) };

        // rcl_timer_is_ready should only error if incorrect arguments are given or something isn't initialised,
        // both of which we control in this function.
        debug_assert_eq!(RclReturnCode::try_from(ret).unwrap(), RclReturnCode::Ok);

        is_ready
    }

    /// Get the time until the next call of the timer is due. Saturates to 0 if the timer is ready.
    /// Returns [`RclReturnCode::TimerCanceled`] as an error if the timer has already been canceled.
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
    pub fn time_since_last_call(&self) -> Duration {
        let mut timer = self.handle.lock();
        let mut elapsed_time = 0;
        // SAFETY:
        // * The timer is initialized, which is guaranteed by the constructor.
        // * The elapsed_time pointer is allocated on the stack and is valid for the duration of this function.
        let ret = unsafe { rcl_timer_get_time_since_last_call(&mut *timer, &mut elapsed_time) };

        // rcl_timer_get_time_since_last_call should only error if incorrect arguments are given
        // or something isn't initialised, both of which we control in this function.
        debug_assert_eq!(RclReturnCode::try_from(ret).unwrap(), RclReturnCode::Ok);

        Duration::from_nanos(u64::try_from(elapsed_time).unwrap_or(0))
    }

    /// Get the period of the timer.
    pub fn get_period(&self) -> Duration {
        let timer = self.handle.lock();
        let mut period = 0;
        // SAFETY:
        // * The timer is initialized, which is guaranteed by the constructor.
        // * The period pointer is allocated on the stack and is valid for the duration of this function.
        let ret = unsafe { rcl_timer_get_period(&*timer, &mut period) };

        // rcl_timer_get_period should only error if incorrect arguments are given
        // or something isn't initialised, both of which we control in this function.
        debug_assert_eq!(RclReturnCode::try_from(ret).unwrap(), RclReturnCode::Ok);

        // The period should never be negative as we only expose (unsigned) Duration structs
        // for setting, but if it is, saturate to 0.
        Duration::from_nanos(u64::try_from(period).unwrap_or(0))
    }

    /// Set the period of the timer. Periods greater than i64::MAX nanoseconds will saturate to i64::MAX.
    ///
    /// The updated period will not take affect until either [`reset`][1] is called
    /// or the timer next expires, whichever comes first.
    ///
    /// [1]: crate::Timer::reset
    pub fn set_period(&self, period: Duration) {
        let timer = self.handle.lock();
        let new_period = i64::try_from(period.as_nanos()).unwrap_or(i64::MAX);
        let mut old_period = 0;
        // SAFETY:
        // * The timer is initialized, which is guaranteed by the constructor.
        // * The new_period is copied into this function so it can be dropped afterwards.
        // * The old_period pointer is allocated on the stack and is valid for the duration of this function.
        let ret = unsafe { rcl_timer_exchange_period(&*timer, new_period, &mut old_period) };

        // rcl_timer_exchange_period should only error if incorrect arguments are given
        // or something isn't initialised, both of which we control in this function.
        debug_assert_eq!(RclReturnCode::try_from(ret).unwrap(), RclReturnCode::Ok);
    }

    /// Cancel the timer so it will no longer return ready. Can be restarted with [`reset`][1].
    ///
    /// [1]: crate::timer::Timer::reset
    pub fn cancel(&self) {
        let mut timer = self.handle.lock();
        // SAFETY: The timer is initialized, which is guaranteed by the constructor.
        let ret = unsafe { rcl_timer_cancel(&mut *timer) };

        // rcl_timer_cancel should only error if incorrect arguments are given
        // or something isn't initialised, both of which we control in this function.
        debug_assert_eq!(RclReturnCode::try_from(ret).unwrap(), RclReturnCode::Ok);
    }

    /// Check if the timer has been canceled.
    pub fn is_canceled(&self) -> bool {
        let timer = self.handle.lock();
        let mut canceled = false;
        // SAFETY:
        // * The timer is initialized, which is guaranteed by the constructor.
        // * The canceled pointer is allocated on the stack and is valid for the duration of this function.
        let ret = unsafe { rcl_timer_is_canceled(&*timer, &mut canceled) };

        // rcl_timer_is_canceled should only error if incorrect arguments are given
        // or something isn't initialised, both of which we control in this function.
        debug_assert_eq!(RclReturnCode::try_from(ret).unwrap(), RclReturnCode::Ok);

        canceled
    }

    /// Set the timer's last call time to now. Additionally marks canceled timers as not-canceled.
    pub fn reset(&self) {
        let mut timer = self.handle.lock();
        // SAFETY: The timer is initialized, which is guaranteed by the constructor.
        let ret = unsafe { rcl_timer_reset(&mut *timer) };

        // rcl_timer_reset should only error if incorrect arguments are given
        // or something isn't initialised, both of which we control in this function.
        debug_assert_eq!(RclReturnCode::try_from(ret).unwrap(), RclReturnCode::Ok);
    }

    /// Internal function to check the timer is still valid and set the last call time in rcl.
    /// Returns [`RclReturnCode::TimerCanceled`] as an error if the timer has already been canceled.
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

    fn execute(&mut self) -> Result<(), RclrsError> {
        // Timer still needs to be called within RCL, even though we handle the callback ourselves.
        self.call_rcl()?;

        let callback = self.callback.clone();
        (*callback.lock().unwrap())(self);

        Ok(())
    }
}

// Timer.rs does very little other than call rcl functions.
// To keep these tests easy to maintain, most of them just check the rcl functions
// can be called without returning errors.
#[cfg(test)]
mod tests {
    use std::time::Duration;

    use crate::{Clock, Context};

    use super::Timer;

    fn new_timer() -> Timer {
        let context = Context::new([]).unwrap();

        // This is technically a wall clock, but we have a period of 0 so it won't slow down unit testing.
        let clock = Clock::system();

        let timer = Timer::new(&context, clock, Duration::from_secs(0), |_| {});

        timer.expect("Timer::new should not return an error")
    }

    #[test]
    fn creation() {
        let _ = new_timer();
    }

    #[test]
    fn is_ready() {
        let timer = new_timer();

        // Calling is_ready will trigger the debug_assert check on the rcl return value.
        timer.is_ready();
    }

    #[test]
    fn time_until_next_call() {
        let timer = new_timer();

        timer
            .time_until_next_call()
            .expect("Calling Timer::time_until_next_call on a non-canceled timer should not error");
    }

    #[test]
    fn time_since_last_call() {
        let timer = new_timer();

        // Calling time_since_last_call will trigger the debug_assert check on the rcl return value.
        timer.time_since_last_call();
    }

    #[test]
    fn update_period() {
        let timer = new_timer();

        let new_period = Duration::from_millis(100);

        // Calling set_period will trigger the debug_assert check on the rcl return value.
        timer.set_period(new_period.clone());

        // Calling get_period will trigger the debug_assert check on the rcl return value.
        let retrieved_period = timer.get_period();

        assert_eq!(new_period, retrieved_period);
    }

    #[test]
    fn cancel_timer() {
        let timer = new_timer();

        // Calling is_canceled will trigger the debug_assert check on the rcl return value.
        assert!(!timer.is_canceled());

        // Calling cancel will trigger the debug_assert check on the rcl return value.
        timer.cancel();

        assert!(timer.is_canceled());
    }

    #[test]
    fn reset_canceled_timer() {
        let timer = new_timer();
        timer.cancel();

        // Calling reset will trigger the debug_assert check on the rcl return value.
        timer.reset();

        assert!(!timer.is_canceled());
    }
}

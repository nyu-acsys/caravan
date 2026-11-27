let write cell = ignore (Atomic.exchange cell false)

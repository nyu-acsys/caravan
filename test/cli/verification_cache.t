Verification reuses unchanged obligations across body edits, new polymorphic calls,
and shifted source positions; contract edits invalidate callers and failures are
never cached.

  $ python3 check_verification_cache.py

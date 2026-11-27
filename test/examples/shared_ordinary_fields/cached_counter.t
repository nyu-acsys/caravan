After acquiring a publication cut, stale post-publication capacity writes remain
possible. Positive cache entries conservatively admit a push when head positions
advance. A zero cache triggers refresh rather than proving fullness. Positions
are mathematical integers; this experiment does not prove machine-int arithmetic.

  $ cat thread_views.rav past_writes.rav cached_counter.rav > cache.rav
  $ raven --shh cache.rav
  Verification successful.

Without acquisition, private writes can violate the capacity bound. Acquisition
does not imply the latest cache write, and head regression breaks conservativity.

  $ cat cache.rav cache_without_acquire_fail.rav > without_acquire.rav
  $ raven --shh without_acquire.rav > without_acquire.out 2>&1
  [1]
  $ grep -c '^Verification Error: This assertion may be violated.' without_acquire.out
  1
  $ cat cache.rav cache_latest_fail.rav > latest.rav
  $ raven --shh latest.rav > latest.out 2>&1
  [1]
  $ grep -c '^Verification Error: This assertion may be violated.' latest.out
  1
  $ cat cache.rav cache_head_regression_fail.rav > regression.rav
  $ raven --shh regression.rav > regression.out 2>&1
  [1]
  $ grep -c '^Verification Error: This assertion may be violated.' regression.out
  1

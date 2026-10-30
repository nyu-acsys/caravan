  $ caravan --shh -I include_dirs include_dirs.ml
  Verification successful.
  $ caravan --shh include_dirs.ml
  [Error] File "include_dirs.ml", line 5, columns 53-59:
  5 |   if n > 0 then spin (n - 1) (Backoff.once backoff) (Ticker.tick ticker)
                                                           ^^^^^^
  Type Error: Unbound module Ticker.
  [1]

  $ caravan --shh trusted.ml
  [Warning] File "trusted.ml", line 4, columns 0-54:
  4 | let digits (n : int) = String.length (string_of_int n)
      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Warning: digits is trusted: its contract is assumed, not verified.
  Verification successful.

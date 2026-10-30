  $ caravan --shh manual_state_cast_fail.ml
  [Error] File "manual_state_cast_fail.ml", line 4, columns 14-18:
  4 |     (result, (cell : bool Atomic.t))) *)
                    ^^^^
  Type Error: The value cell has type int Atomic.t but an expression was expected of type
    bool Atomic.t
  Type int is not compatible with type bool.
  [1]

  $ caravan --shh ghost_params_error.ml
  [Error] File "ghost_params_error.ml", line 10, columns 20-40:
  10 | let read_fresh () = read (Atomic.make 0)
                           ^^^^^^^^^^^^^^^^^^^^
  Type Error: Caravan cannot tell the ghost argument of this call: the argument is not a variable known to be the field a of a value, as one a record pattern binds.
  [1]

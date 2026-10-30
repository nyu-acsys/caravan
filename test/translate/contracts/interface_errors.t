Interfaces and proofs that do not fit their implementation; each file has its own run.

  $ caravan --shh interface_error_1.ml
  [Error] File "interface_error_1.mli", line 3, columns 0-43:
  3 | (*@ predicate is_lock (l : t) (b : bool) *)
      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Type Error: The predicate is_lock is not defined: define it in the proof or an annotation.
  [1]
  $ caravan --shh interface_error_2.ml
  [Error] File "interface_error_2.ml", line 1, columns 0-18:
  1 | let incr x = x + 1
      ^^^^^^^^^^^^^^^^^^
  Type Error: incr has a contract in its interface and another one here.
  File "interface_error_2.mli", line 1, columns 0-21:
  1 | val incr : int -> int
      ^^^^^^^^^^^^^^^^^^^^^
  Related Location: Its contract in the interface.
  [1]
  $ caravan --shh interface_error_3.ml
  [Error] File "interface_error_3.proof", line 1, columns 10-17:
  1 | predicate is_lock (l : t) (b : int) = own l true && b = 0
                ^^^^^^^
  Type Error: The predicate is_lock is defined with other parameter types than it is declared with.
  File "interface_error_3.mli", line 3, columns 0-43:
  3 | (*@ predicate is_lock (l : t) (b : bool) *)
      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: Its declaration.
  [1]
  $ caravan --shh interface_error_4.ml
  [Error] File "interface_error_4.proof", line 1, columns 10-17:
  1 | predicate is_lock (l : t) (b : bool) = own l b
                ^^^^^^^
  Type Error: The predicate is_lock is defined twice.
  File "interface_error_4.ml", line 3, columns 0-53:
  3 | (*@ predicate is_lock (l : t) (b : bool) = own l b *)
      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: Its first definition.
  [1]
  $ caravan --shh interface_error_5.ml
  [Error] File "interface_error_5.proof", line 1, columns 37-40:
  1 | predicate is_lock (l : t) (b : bool) own l b
                                           ^^^
  Syntax Error: Syntax error.
  [1]

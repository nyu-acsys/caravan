Argument normalization retains genuine source-type mismatches.

  $ caravan --shh function_cases_type_fail.ml
  [Error] File "function_cases_type_fail.ml", line 2, columns 46-48:
  2 | (*@ result = invalid xs ensures boolean_items xs *)
                                                    ^^
  Type Error: The value xs has type int list but an expression was expected of type
    bool list
  Type int is not compatible with type bool.
  [1]

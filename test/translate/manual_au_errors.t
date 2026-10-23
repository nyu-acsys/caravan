  $ caravan --shh manual_au_double_open_fail.ml
  [Error] File "manual_au_double_open_fail.ml", line 5, columns 20-42:
  5 |     let duplicate = Read.access token cell in
                          ^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: Atomic token token is already open.
  [1]
  $ caravan --shh manual_au_double_commit_fail.ml
  [Error] File "manual_au_double_commit_fail.ml", line 9, columns 4-33:
  9 |     Read.commit token cell result;
          ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: Cannot commitAU: atomic token token is not open.
  [1]
  $ caravan --shh manual_au_unclosed_fail.ml
  [Error] File "manual_au_unclosed_fail.ml", line 1, columns 47-48:
  1 | let read (cell : int Atomic.t) = Atomic.get cell
                                                     ^
  Verification Error: Missing commitAU or abortAU for open atomic update token.
  File "manual_au_unclosed_fail.ml", line 4, columns 16-38:
  4 |     let value = Read.access token cell in
                      ^^^^^^^^^^^^^^^^^^^^^^
  Related Location: token was opened here.
  [1]
  $ caravan --shh manual_au_bad_result_fail.ml
  [Error] File "manual_au_bad_result_fail.ml", line 8, columns 4-28:
  8 |     Read.commit token cell 1;
          ^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: An atomic postcondition may not hold at this commit point.
  [Error] File "manual_au_bad_result_fail.ml", line 8, columns 4-28:
  8 |     Read.commit token cell 1;
          ^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: A postcondition may not hold at this return point.
  File "manual_au_bad_result_fail.ml", line 14, columns 42-56:
  14 |     atomic ensures contents cell value && result = value *)
                                                 ^^^^^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]
  $ caravan --shh manual_au_wrong_token_fail.ml
  [Error] File "manual_au_wrong_token_fail.ml", line 4, columns 29-34:
  4 |     let value = Other.access token cell in
                                   ^^^^^
  Type Error: The value token has type Read.token but an expression was expected of type
    Other.token
  The type constructor Other.token would escape its scope.
  [1]

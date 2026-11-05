Manual atomic updates distinguish normal and exceptional completion, including
polymorphic results, unit results, and exceptional completion resources.

  $ caravan --shh raises.ml
  Verification successful.

Witness-dependent results keep source token indices while sharing one backend update.

  $ caravan --shh witness.ml
  Verification successful.

An operation whose only polymorphic parameter is its result index needs no backend dictionary.

  $ caravan --shh index_only.ml
  Verification successful.

Existing tuple-valued ghost results retain their meaning on calls that may raise.

  $ caravan --shh pair_client.ml
  Verification successful.

Exceptional completion preserves the identity of the exception.

  $ cp raises.ml wrong_exception.ml
  $ sed 's/Read.commit_raise token cell Empty/Read.commit_raise token cell Exit/' raises.proof > wrong_exception.proof
  $ caravan --shh wrong_exception.ml > wrong_exception.out 2>&1
  [1]
  $ grep 'Verification Error:' wrong_exception.out
  Verification Error: A precondition may not hold for this call.

An exceptional completion cannot replace the normal completion of a successful read.

  $ cp raises.ml wrong_normal.ml
  $ sed 's/Read.commit token cell expected/Read.commit_raise token cell Empty/' raises.proof > wrong_normal.proof
  $ caravan --shh wrong_normal.ml > wrong_normal.out 2>&1
  [1]
  $ grep 'Verification Error:' wrong_normal.out
  Verification Error: An atomic postcondition may not hold at this commit point.
  Verification Error: A postcondition may not hold at this return point.

Erasing the backend result index preserves the source token type distinction.

  $ cp witness.ml wrong_index.ml
  $ sed 's/| Value -> Saved_value token/| Value -> Saved_option token/' witness.proof > wrong_index.proof
  $ caravan --shh wrong_index.ml > wrong_index.out 2>&1
  [1]
  $ grep 'Type Error:' wrong_index.out
  Type Error: The value token has type (a, a) Read.token

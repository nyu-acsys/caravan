Invalid action updates report their source error instead of keeping the old state.

  $ mkdir wrong_type
  $ cp ra_view.ml ra_view.mli wrong_type/
  $ sed 's/value = advance s.value + identity after - after/value = true/' ra_view.proof > wrong_type/ra_view.proof
  $ caravan --shh wrong_type/ra_view.ml > wrong_type/error 2>&1
  [1]
  $ grep 'Type Error:' wrong_type/error
  Type Error: This expression should not be a boolean literal, the expected type is
  $ grep -q 'int' wrong_type/error

  $ mkdir unknown_value
  $ cp ra_view.ml ra_view.mli unknown_value/
  $ sed 's/advance s.value + identity after - after/missing + s.value/' ra_view.proof > unknown_value/ra_view.proof
  $ caravan --shh unknown_value/ra_view.ml > unknown_value/error 2>&1
  [1]
  $ grep 'Type Error:' unknown_value/error
  Type Error: Unbound value missing.

A lexical binding cannot reuse a projection of the shadowed state.

  $ mkdir shadowed_state
  $ cp ra_view.ml ra_view.mli shadowed_state/
  $ sed 's/R.excl (s.value + 2)/R.excl (let s = true in s.value + 2)/' ra_view.proof > shadowed_state/ra_view.proof
  $ caravan --shh shadowed_state/ra_view.ml > shadowed_state/error 2>&1
  [1]
  $ grep 'Type Error:' shadowed_state/error
  Type Error: This expression has type bool

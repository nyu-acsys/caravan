A generic proof type is instantiated even when its template has no proof terms.

  $ caravan --shh models_type_only.ml
  Verification successful.
  $ caravan --shh --emit-rav models_type_only.ml > models_type_only.rav
  $ raven --shh models_type_only.rav
  Verification successful.

The two applications retain distinct ghost model types.

  $ cp models_type_only.ml models_type_only_cross.ml
  $ cat models_type_only.proof > models_type_only_cross.proof
  $ printf '\nlemma incompatible (cell : Second.t) =\n  let (value : First.model) = Second.Item cell in ()\n' >> models_type_only_cross.proof
  $ ! caravan --shh models_type_only_cross.ml > models_type_only_cross.out 2>&1
  $ grep -q 'Type Error:' models_type_only_cross.out

An unapplied template must not emit its model as a global type.

  $ cat > unapplied_model.ml <<'ML'
  > module type ARG = sig type t end
  > module Make (Arg : ARG) = struct
  >   let identity (value : Arg.t) = value
  > end
  > ML
  $ cat > unapplied_model.proof <<'PROOF'
  > module Make (Arg : ARG) = struct
  >   type model = Empty
  > end
  > PROOF
  $ ! caravan --shh unapplied_model.ml > unapplied_model.out 2>&1
  $ grep -F 'A functor proof without a supported generic runtime body and application is not supported yet.' unapplied_model.out
  Unsupported Error: A functor proof without a supported generic runtime body and application is not supported yet.

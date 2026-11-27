Known tasks transfer resources at spawn and recover them at join.

  $ caravan --shh runtime.ml
  Verification successful.
  $ caravan --shh runtime_raises.ml
  Verification successful.
  $ caravan --shh --emit-rav runtime.ml > runtime.rav
  $ raven --shh runtime.rav
  Verification successful.
  $ caravan --shh --emit-rav runtime_raises.ml > runtime_raises.rav
  $ raven --shh runtime_raises.rav
  Verification successful.

A second join cannot recover the task's resources again.

  $ sed 's/let alias = domain in/let ignored = finish domain cell in let alias = domain in/' runtime.ml > twice.ml
  $ cp runtime.mlp twice.mlp
  $ caravan --shh twice.ml > twice.out 2>&1
  [1]
  $ grep 'Verification Error:' twice.out
  Verification Error: A precondition may not hold for this call.

The parent cannot access resources owned by a running task.

  $ sed 's/let alias = domain in/let ignored = !cell in let alias = domain in/' runtime.ml > early.ml
  $ cp runtime.mlp early.mlp
  $ caravan --shh early.ml > early.out 2>&1
  [1]
  $ grep 'Verification Error:' early.out
  Verification Error: A precondition may not hold for this call.

Closure computations must stay in a separately verified task.

  $ sed 's/fun () -> work cell/fun () -> work (if true then cell else cell)/' runtime.ml > computed.ml
  $ cp runtime.mlp computed.mlp
  $ caravan --shh computed.ml > computed.out 2>&1
  [1]
  $ grep 'Unsupported Error:' computed.out
  Unsupported Error: A domain task argument computed inside its closure; move the computation into the verified task is not supported yet.

Join exceptions must be handled or declared by the caller.

  $ sed '/let finish/,$ s/raises Failed -> own cell.contents 1/ensures true/' runtime_raises.ml > undeclared.ml
  $ cp runtime_raises.mlp undeclared.mlp
  $ caravan --shh undeclared.ml > undeclared.out 2>&1
  [1]
  $ grep 'Error:' undeclared.out
  Type Error: This may raise Failed, which the contract of the function does not declare: add a raises clause.

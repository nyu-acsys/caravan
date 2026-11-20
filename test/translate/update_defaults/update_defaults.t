In the proof of an operation, operations on its own atomic update may omit the
update's arguments, which are the operation's parameters. A step at a call that
fulfills the update can delegate it to the call.

  $ caravan --shh cell.ml
  Verification successful.

An omitted argument must not be rebound where it is omitted.

  $ sed 's/    Read.commit token result;/    let cell = cell in\n    Read.commit token result;/' cell.proof > rebound.proof
  $ cp cell.ml rebound.ml
  $ cp cell.mli rebound.mli
  $ caravan --shh rebound.ml
  [Error] File "rebound.proof", line 12, columns 4-28:
  12 |     Read.commit token result;
           ^^^^^^^^^^^^^^^^^^^^^^^^
  Type Error: cell is rebound here: give the update's arguments explicitly.
  [1]

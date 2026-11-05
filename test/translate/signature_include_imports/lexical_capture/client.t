A free logical contract variable cannot capture an unrelated OCaml value introduced
by the including signature.

  $ caravan --shh client.ml 2>&1 | sed -n 's/^Unsupported Error: A signature contract whose names have a different implementation scope.*/Rejected lexical capture/p'
  Rejected lexical capture

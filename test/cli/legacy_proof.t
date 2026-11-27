A companion proof file with the legacy .proof extension is still used, with a
warning, but not next to a .mlp file.

  $ cp ../translate/modules/opens.ml legacy.ml
  $ cp ../translate/modules/opens.mlp legacy.proof
  $ caravan --shh legacy.ml
  [Warning] File "legacy.proof", line 1, columns 0-0:
  1 | module Original = struct
      ^
  Warning: The proof file extension .proof is deprecated; rename it to legacy.mlp.
  Verification successful.

  $ cp legacy.proof legacy.mlp
  $ caravan --shh legacy.ml
  [Error] File "legacy.proof", line 1, columns 0-0:
  1 | module Original = struct
      ^
  Type Error: Both legacy.mlp and legacy.proof exist; rename or remove legacy.proof.
  [1]

A nonrecursive proof alias refers to the outer runtime type.

  $ caravan --shh nonrec.ml
  Verification successful.

An ordinary recursive self-alias remains a type error.

  $ cp nonrec.ml recursive.ml
  $ sed 's/type nonrec t = t/type t = t/' nonrec.mlp > recursive.mlp
  $ caravan --shh recursive.ml > recursive.out 2>&1
  [1]
  $ grep -i -m1 -o 'type abbreviation t is cyclic' recursive.out
  type abbreviation t is cyclic

Recursive logical definitions check a decreasing measure over mathematical inputs.

  $ caravan --shh copy.ml
  Verification successful.

  $ caravan --shh --emit-rav copy.ml > copy.rav
  $ raven --shh copy.rav
  Verification successful.

Missing measures, non-decreasing recursion, and false automatic lemmas are rejected.

  $ caravan --shh missing.ml
  [Error] File "missing.proof", line 1, columns 8-16:
  1 | let rec infinite (value : int) : int = infinite value
              ^^^^^^^^
  Type Error: A recursive logical function needs a variant.
  [1]

  $ caravan --shh bad_progress.ml
  [Error] File "bad_progress.proof", line 2, columns 10-18:
  2 |   variant (values) = repeat values
                ^^^^^^^^
  Verification Error: This decreases clause's termination measure may not decrease on this recursive call.
  [1]

  $ caravan --shh bad_auto.ml
  [Error] File "bad_auto.proof", line 1, columns 24-24:
  1 | lemma [@auto] impossible (value : bool)
                              ^
  Verification Error: A postcondition may not hold at this return point.
  File "bad_auto.proof", line 2, columns 11-30:
  2 |   ensures (value === not value) = ()
                 ^^^^^^^^^^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]

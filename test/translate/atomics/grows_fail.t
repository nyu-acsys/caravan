  $ caravan --shh grows_fail.ml
  [Error] File "grows_fail.proof", line 6, columns 10-10:
  6 | action dec = { s with count = s.count - 1 }
                ^
  Verification Error: The action dec may make a field marked [@grows] shrink.
  File "grows_fail.proof", line 6, columns 7-10:
  6 | action dec = { s with count = s.count - 1 }
             ^^^
  Related Location: This assertion may not hold.
  [1]
  $ caravan --shh --history=monotone grows_fail.ml
  [Error] File "grows_fail.proof", line 6, columns 10-10:
  6 | action dec = { s with count = s.count - 1 }
                ^
  Verification Error: The action dec may make a field marked [@grows] shrink.
  File "grows_fail.proof", line 6, columns 7-10:
  6 | action dec = { s with count = s.count - 1 }
             ^^^
  Related Location: This assertion may not hold.
  [1]

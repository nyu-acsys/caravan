Automatic views store RA elements as data, including invalid elements. Two views of
one carrier keep distinct observations through allocation, CAS and read commits.
State projections and inferred action parameters stay typed inside helper calls.

  $ caravan --shh ra_view.ml
  Verification successful.
  $ caravan --shh --emit-rav ra_view.ml > ra_view.rav
  $ raven --shh ra_view.rav
  Verification successful.

The update cannot promise the old observation.

  $ mkdir stale
  $ cp ra_view.ml ra_view.proof stale/
  $ sed 's/atomic ensures model c (R.excl 1) \&\& other c (R.excl 3) \*)/atomic ensures model c R.invalid \&\& other c (R.excl 3) *)/' ra_view.mli > stale/ra_view.mli
  $ caravan --shh stale/ra_view.ml
  [Error] File "stale/ra_view.ml", line 7, columns 5-33:
  7 |   if Atomic.compare_and_set c 0 1 (*@ performs set_one *) then () else set_one c
           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: The atomic postcondition may not hold after this step, which linearizes the function.
  File "stale/ra_view.mli", line 12, columns 19-58:
  12 |     atomic ensures model c R.invalid && other c (R.excl 3) *)
                          ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: The atomic postcondition.
  [Error] File "stale/ra_view.ml", line 7, columns 5-33:
  7 |   if Atomic.compare_and_set c 0 1 (*@ performs set_one *) then () else set_one c
           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: A postcondition may not hold at this return point.
  File "stale/ra_view.mli", line 12, columns 19-36:
  12 |     atomic ensures model c R.invalid && other c (R.excl 3) *)
                          ^^^^^^^^^^^^^^^^^
  Related Location: This predicate may not hold.
  [Error] File "stale/ra_view.ml", line 14, columns 2-8:
  14 |   read c
         ^^^^^^
  Verification Error: A precondition may not hold for this call.
  File "stale/ra_view.mli", line 16, columns 20-38:
  16 |     atomic requires model c (R.excl 1) && other c (R.excl 3)
                           ^^^^^^^^^^^^^^^^^^
  Related Location: This predicate may not hold.
  [1]

Variables appearing only in a result are inferred at each use. Empty containers
do not require an inhabitant of their element domain.

  $ caravan --shh result_variables.ml
  Verification successful.
  $ caravan --shh --emit-rav result_variables.ml > result_variables.rav
  $ raven --shh result_variables.rav
  Verification successful.

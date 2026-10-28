Repeated applications with equal type arguments share their Raven type.

  $ caravan --shh library_ra_sharing.ml
  Verification successful.
  $ caravan --shh --emit-rav library_ra_sharing.ml > sharing.rav
  $ raven --shh sharing.rav
  Verification successful.

Different arguments retain distinct types.

  $ cp library_ra_sharing.ml library_ra_sharing_distinct.ml
  $ caravan --shh library_ra_sharing_distinct.ml > library_ra_sharing_distinct.out 2>&1; status=$?; test "$status" -eq 1 && grep -qF 'Type Error:' library_ra_sharing_distinct.out

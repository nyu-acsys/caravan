One stateful invariant and view support integer and boolean cells through shared workers.

  $ caravan --shh cell.ml
  Verification successful.
  $ caravan --shh --emit-rav cell.ml > cell.rav
  $ grep -c 'inv is_cell(' cell.rav
  1
  $ raven --shh cell.rav
  Verification successful.

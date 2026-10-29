Recursive atomic payloads share one worker and retain their layout fields in clients.

  $ caravan --shh generic_recursive_cells.ml
  Verification successful.
  $ caravan --shh --emit-rav generic_recursive_cells.ml > emitted.rav
  $ raven --shh emitted.rav
  Verification successful.
  $ grep -c 'Generic_.*\[Parameter:' emitted.rav
  1
  $ grep -c '^[[:space:]]*proc method_create(' emitted.rav
  1
  $ grep -c '^[[:space:]]*field atomic_Data_node:' emitted.rav
  1

Ordinary reference and mutable-record accesses cannot run while an invariant is open.

  $ caravan --shh nonatomic_ref_read_fail.ml
  [Error] File "nonatomic_ref_read_fail.ml", line 3, columns 15-20:
  3 |   let result = !cell in
                     ^^^^^
  Verification Error: Cannot take a non-atomic step while an invariant or atomic update is open.
  [1]
  $ caravan --shh nonatomic_record_pattern_fail.ml
  [Error] File "nonatomic_record_pattern_fail.ml", line 5, columns 6-15:
  5 |   let { count } = cell in
            ^^^^^^^^^
  Verification Error: Cannot take a non-atomic step while an invariant or atomic update is open.
  [1]
  $ caravan --shh nonatomic_ref_write_fail.ml
  [Error] File "nonatomic_ref_write_fail.ml", line 3, columns 2-11:
  3 |   cell := 0;
        ^^^^^^^^^
  Verification Error: Cannot take a non-atomic step while an invariant or atomic update is open.
  [1]
  $ caravan --shh nonatomic_record_read_fail.ml
  [Error] File "nonatomic_record_read_fail.ml", line 5, columns 15-25:
  5 |   let result = cell.count in
                     ^^^^^^^^^^
  Verification Error: Cannot take a non-atomic step while an invariant or atomic update is open.
  [1]
  $ caravan --shh nonatomic_record_write_fail.ml
  [Error] File "nonatomic_record_write_fail.ml", line 5, columns 2-17:
  5 |   cell.count <- 0;
        ^^^^^^^^^^^^^^^
  Verification Error: Cannot take a non-atomic step while an invariant or atomic update is open.
  [1]

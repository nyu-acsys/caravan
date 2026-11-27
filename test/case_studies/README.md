# Independent case studies

This directory is reserved for substantial data structure implementations and
their proofs developed independently of Saturn.

Saturn implementations and clients belong in `test/saturn`. Smaller verified
clients, proof patterns, and algorithm fragments belong in `test/examples`;
focused translator regressions belong in `test/translate`.

The [generic striped hash set](generic_striped_hash_set) follows the lock-striped
design in *The Art of Multiprocessor Programming*, with mutex-protected bucket rows,
an abstract key type, and manual abstract-set proofs.

# Independent case studies

This directory is reserved for substantial data structure implementations and
their proofs developed independently of Saturn.

Saturn implementations and clients belong in `test/saturn`. Smaller verified
clients, proof patterns, and algorithm fragments belong in `test/examples`;
focused translator regressions belong in `test/translate`.

The [striped hash set](striped_hash_set) follows the lock-striped design in
*The Art of Multiprocessor Programming*, with mutex-protected bucket rows and
manual abstract-set proofs.

The [generic striped hash set](generic_striped_hash_set) retains the same locking
and resize proof while abstracting over key equality and hashing; the integer
version remains available as a performance comparison.

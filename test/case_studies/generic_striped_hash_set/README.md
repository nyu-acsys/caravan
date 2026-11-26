# Generic striped hash set

This functor generalizes the [integer-key hash set](../striped_hash_set) to an
abstract key type. The original implementation and proof remain unchanged for
comparison. Both versions implement membership, insertion, removal, and resizing
under all stripe locks, following Herlihy and Shavit's *The Art of Multiprocessor
Programming*, Section 13.2.2.

`Make (Key)` takes a module with a type `t`, a pure `equal` operation matching
logical equality (`===`), and a pure `hash` operation returning a nonnegative
OCaml integer. Equality and hashing require no heap resources. Hash collisions
are unrestricted, and equal keys have equal hashes by purity and congruence.
These contracts exclude equality or hashing that depends on mutable key contents.
Reference keys can instead use identity equality and stable hashing.

The public contracts appear on the functor's result signature in the `.ml` file;
the companion `.proof` file mirrors the functor. The abstract contents are a
`Key.t finset`. The proof uses the same stripe snapshots, table agreement,
registration, and resize protocol as the integer version. Mathematical key
quantifiers range over the entire logical carrier through a proof-only record;
they do not assume every carrier value is an executable OCaml value.

The constructor requires between 1 and 1,000 stripes. Set operations and resize
require an empty incoming held-lock set. Resize requests have a positive expected
capacity, and doubling is guarded against the maximum array length. The public
resize contract preserves abstract contents and lock cleanup; it does not expose
capacity growth. The heuristic counter has no exact cardinality specification.
Automatic load-factor-based resizing, termination, fairness, and deadlock freedom
are outside this case study's specification.

The clients instantiate the functor with signed integer keys, immutable record
keys with colliding hashes, and reference keys whose contents can change while
identity remains fixed. The instance fixture is assembled from the functor and
its companion proof, so it has no separately maintained implementation copy.
The concrete instances have a companion interface. Caravan translates it to an
abstract Raven interface and checks forwarding adapters against its frozen
contracts, with resource aliases connecting the implementation. The export check
succeeds: `tabled`, `locked`, and `counted`
are private children of the public `is_set` invariant, declared with
`[@within is_set s]`. The table invariant carries the immutable set record as
its stable owner; the constructor keeps its table resources in an ordinary
predicate until that owner exists. Mutex registration is not opened by this
proof. Helpers explicitly reserve the public root, or use `opens {}` when they
only reason about mutex identities. Clients verify against the opaque contracts
of all three instances, whose exports are checked against the implementation.
They need no `opens` clause: the opaque execution context they hold depends on
no invariant, and they need no permission for the private invariant families.

Run the case-study regression with:

```bash
dune build @test/case_studies/generic_striped_hash_set/runtest -j2
```

For serial performance measurements of both versions with the same executable:

```bash
dune build bin/caravan.exe -j2
python3 test/case_studies/generic_striped_hash_set/compare.py
```

The script performs one warmup and five interleaved measured runs per version,
with verification caching disabled. It records source/executable hashes, outputs,
emitted Raven sizes, and timing summaries under a new temporary directory.
Emission measures source loading, OCaml typing, translation, and printing;
end-to-end verification also includes Raven preprocessing and SMT solving.
Their difference is not a measurement of solver time alone.

See [the performance comparison](PERFORMANCE.md) for measured results and scope.

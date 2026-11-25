# Verification performance comparison

This comparison measures the preserved integer implementation and the generic
functor declaration, including all operations, resizing, and auxiliary lemmas.
Both proofs contain 37 auxiliary lemmas. The generic body is checked once against
an abstract key module; these timings exclude the separate concrete-instance and
interface-only client checks.

## Method

The two versions use the same freshly built Caravan executable and Raven revision
`9b685d611680f3df055a9280e48dd0a92a1b68c6`. Runs are serial, with no verification
cache and no simultaneous regression suite. Each phase has one warmup followed by
five measured runs per version, interleaved with alternating order.

The machine uses an Intel Core i7-1365U, Linux x86-64, OCaml 5.5.0, and Z3 5.1.0.
The default per-query SMT timeout is unchanged.

```bash
opam exec --switch=raven -- python3 test/case_studies/generic_striped_hash_set/compare.py
```

`--emit-rav` measures process startup, source loading/typechecking, Caravan
translation, and Raven printing. Full verification also includes Raven
preprocessing, SMT encoding, and solver execution. Subtracting the emission time
from verification time does not isolate solver cost.

The script saves every command, output, exit status, timing, emitted program, and
source/executable SHA-256 in a temporary results directory. CPU time includes the
process and its waited-for descendants.

## Results

| Phase | Integer median (range) | Generic median (range) |
| --- | ---: | ---: |
| Emission | 0.653s (0.650–0.668s) | 2.336s (2.324–2.367s) |
| Full verification | 29.406s (28.482–30.118s) | 20.488s (20.359–21.243s) |

| Version | Emission CPU | Verification CPU | Emitted Raven bytes |
| --- | ---: | ---: | ---: |
| Integer | 0.65s | 29.72s | 145,054 |
| Generic | 2.33s | 20.86s | 233,409 |

All five measured runs per version succeeded in each phase, as did both
warmup runs per phase. No run failed or timed out.

The generic proof's median full-verification time is 30.3% lower
(1.44× speedup). Its emission time is 3.58× the integer
version's, and its emitted program is 60.9% larger.

## Interpretation

This measures the actual two proofs, rather than isolated functor overhead. The
generic proof includes abstract equality/hash operations and their contracts;
it replaces integer key arithmetic by arithmetic on stable hash values. Its
mathematical key quantifiers cover the full logical carrier. The integer source,
interface, and proof are unchanged from the comparison baseline.

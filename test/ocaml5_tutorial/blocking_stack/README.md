# Tutorial blocking stack

The `Atomic_stack` module in `blocking_stack.ml` is copied unchanged from
[`solutions/prod_cons_b.ml`](https://github.com/ocaml-multicore/ocaml5-tutorial/blob/d212ad1f74b0c69e7ee4eb001487592310ef3c0b/solutions/prod_cons_b.ml)
at revision `d212ad1f74b0c69e7ee4eb001487592310ef3c0b`.
The source-parity test checks the module's exact bytes.

The companion interface and proof establish polymorphic LIFO contracts. The proof
accounts for interference and spurious wakeups: a waiting `pop` retries after
reacquiring the mutex. It proves safety and linearizability, with no claim about
termination, fairness, or deadlock freedom.

The appended Caravan clients check integer and Boolean LIFO order and a Domain
handoff. The handoff joins the producer before popping. The tutorial's command-line
harness, printing, and simultaneous producer/consumer execution are not included.

Run `dune exec -- caravan test/ocaml5_tutorial/blocking_stack/blocking_stack.ml`
from the repository root. All proof annotations are in `.mli` and `.proof` files.

The upstream module is covered by [the tutorial's MIT license](../LICENSE).

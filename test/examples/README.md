# Verification examples

Complete verification examples that illustrate combinations of features, without
constituting full data structure implementations. Each example keeps its sources,
proofs, and positive and negative checks together.

- [Module stack drain](module_stack_drain/): a client of the stack's atomic
  interface packaged in a concrete module.
- [Functor stack drain](functor_stack_drain/): the corresponding monomorphic
  functor client, checked against its parameter's contract.
- [Module-wrapped history queue](module_ms_queue/): the complete queue proof
  behind a static signature, with alias-based clients.
- [Queue tail advancement](queue_tail_advance/): an additional `swing_tail`
  operation checked with both the history and segment queue invariants.

Focused translator regressions belong in `test/translate`, Saturn implementations
and clients in `test/saturn`, and substantial independent implementations in
`test/case_studies`.

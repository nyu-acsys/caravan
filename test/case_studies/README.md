# Other case studies

This directory contains complete verification examples that do not match an
upstream Saturn implementation. Focused translator regressions belong in
`test/translate`; annotated Saturn examples belong in `test/saturn`.

- [Queue tail advancement](queue_tail_advance/): the additional `swing_tail`
  operation checked with both the history and segment queue invariants.

# Moonpool case studies

Upstream Moonpool implementations with Caravan specifications and proofs.
Implementation files retain their upstream bytes; verification annotations live
in companion `.proof` files.

- [Parker](parker/): a mutex/condition-based coalescing permit.

Focused translator regressions belong in `test/translate`; Saturn counterparts
remain under `test/saturn`.

## License

The upstream Moonpool implementations are MIT-licensed; see [LICENSE](LICENSE).
The attribution names Simon Cruanes, the author listed in upstream package
metadata. It omits a year because the pinned upstream revision supplies none.
Caravan specifications and proofs use the repository's [license](../../LICENSE).

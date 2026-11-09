# Moonpool parker

`parker_.ml` is a byte-for-byte copy of Moonpool's
[`src/private/parker_.ml`](https://github.com/c-cube/moonpool/blob/c51b63326602e75332b33a5e83b800c6a1476036/src/private/parker_.ml)
at revision `c51b63326602e75332b33a5e83b800c6a1476036`.

The proof establishes permit coalescing and safety across `Condition.wait`,
`Condition.signal`, and the associated mutex. It makes no liveness claim.

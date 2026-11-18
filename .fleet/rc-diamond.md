**Result.** The manuscript proves integrality of the diamond translates
but does not state whole-module `hdiam` (tex 9638–9668, 9891–9902).
The missing implication follows from its good Hecke formula and its
choice of fresh Frobenius tests at each coefficient (tex 9712–9717).
The deduction is on-the-spot, provenance (c).

For each positive index `n`, approximate an arbitrary scalar trace
using primes not dividing `n`. Its coefficient on an expansion
vanishing modulo `𝔪` lies in `𝔪` by continuity. For a fixed good
`q`, evaluate this trace congruence at `qn` for `Fr_q`; subtract
`v[q²n]` in the full Hecke formula, and use `q ≡ 1 (mod 𝔪)` to
deduce the required diamond congruence at `n`.

The constructor can use `Diamond.hdiam_of_hecke` with its existing
operator and Fourier data. It needs no saturation and no change to
its consumers. The genuine theta data and the other constructor
inputs remain with their respective tasks. See
`docs/research/rc-diamond.md` for the exact inputs and provenance.

`Congruence.lean` compiled with `lake env lean --threads=1`. The axiom
audits of both new theorems report only `propext`,
`Classical.choice`, and `Quot.sound`.

Final proof commit: `351b74f23e2af4c1aea317b1b0fce668561e893b`. The follow-up commit that records
this note is identified by `git log -1 --format=%H -- .fleet/rc-diamond.md`.

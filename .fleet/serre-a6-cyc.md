# Serre A6 cyclotomic sign check

**Closed.** `LocalArtin.serreA6_integerUnits_cyclotomic` proves (iv) at
`n = 1` on all integer units of every finite Galois `K/ℚ_[p]` in
`PadicAlgCl p`. Tau Ceti's arithmetic Artin normalization gives
`χ_cyc(art_K(u)) = N(u)⁻¹`, and the conjugate product gives `N(u)`.

The file passed Lean. The audit lists `propext`, `Classical.choice`, and
`Quot.sound`. The GitHub proxy returned HTTP 403 on fetch and push preflight.
[Research report](../docs/research/serre-a6-cyc.md)

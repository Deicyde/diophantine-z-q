# Dyadic Kato reroute: results log

- **VERIFIED** (reading desk, published page): Prop. 8.12 on p. 186 uses
  the difference of omitted supports; (5.1.1), p. 152, fixes the
  symbol-dependent support. Step 0 changed documentation only.
- **VERIFIED** (source): tex 1884–1892 and 7206–7241 use the dyadic
  13.4(1)(2) conclusion; 7235–7241 specifies torsion and the away-two
  kernel bound on the evaluations of the retained class. Issue #168
  concerns the cited proof, not the frozen implication.
- **VERIFIED** (tool help): read both `lake --help` and
  `lake build --help` before building. Neither exposes a jobs option.
  Use sequential Lake commands; where dependencies are missing, choose
  one-module builds. Check `uptime` and `free -g` before each command.
- **VERIFIED** (git grep on the base): see [consumer list](consumers.md).
  The old bound is a field of two structures; no proof uses its
  inequality as a projection, except that the adapter copies the field
  into the old structure. The current route uses conditional wiring.

## Exact shapes at the cut

- `Thm13_4Conclusion 2`: torsion of `D.H2` over `Λ`, plus
  `length((ker D.loc)_𝔭) ≤ length(Λ_𝔭/J(D.zIw)_𝔭)` for each height-one
  prime away from 2. Both dyadic bundles require the whole conjunction.
- `KatoZetaLeaf`: all elliptic non-CM `E/ℚ` and finite supports
  `Sbad ∋ 2` with the stated model good outside them; supplies
  `∃ Sig ⊇ Sbad, Nonempty (KatoZetaInterface E Sig Sbad)`.
- `AppEFromKato E N L`: the preceding support-indexed supply for a
  fixed elliptic curve implies `AppEOutputs E N L`.
- `evenScalar32_of_kato`: old leaf, non-CM curve, `N ≠ 0` and preceding
  construction imply `EvenScalar32 E N L`.
- `KatoXi p Sig m`: `1 ≤ m ∧ p ∣ m`, and any prime of `m` in `Sig`
  must equal `p`. The old set is an independent subfamily of the extended
  positive levels prime to the smoothers; intersect it with `N_K ∣ m`
  when using it as a subfamily of the 1999 domain.

The exact types and location of each reference are in the companion
consumer list. Documentary references to the old names do not count as
additional proof consumers.

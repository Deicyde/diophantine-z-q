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

## Extended system and transport

- **VERIFIED** (Lean): `KodaiPrint.lean`, `ExtendedNorm.lean`,
  `Comparison.lean`, `Abelian.lean` and `Irreducibility.lean` pass
  `lake env lean` individually. Missing dependencies were built serially
  by Lake command, with `--no-cache build +<Module>:deps` (or
  `+<Module>:olean` for the initially missing `PrintsArith.Kato`).
- **VERIFIED** (Lean): for extended indices the new-prime polynomial is
  evaluated at inverse arithmetic Frobenius divided by the prime;
  repeated primes have multiplier one. The base-to-dyadic trace on the
  untwisted elements has empty Euler support. The §0.7 class is the image
  of the retained class, conditional on the named projection comparison.
- **VERIFIED** (Lean): `SerreThm3` gives the abelian-kernel fixed-space
  condition for the actual rational twist. The same Serre input with
  the existing determinant–cyclotomic theorem gives absolute
  irreducibility after arbitrary extension of the rational coefficients.
- **SPECULATIVE / UNVERIFIED** (source): the 1999 hypothesis list and
  output conventions in the application-shaped draft require the cited
  page check. The in-tree page audit supports the use of the retained
  class and the away-two bound, and records the different supports.

## Consumer checks

- **VERIFIED** (Lean): `EvenBridge.lean` passes `lake env lean` after
  building its imports. It uses the actual rational twist, the two Serre
  results, the old curve-level data, and the conditional post-(K15) work.
- **VERIFIED** (import graph): no new module imports `ZInQKernel.OneProof.Main`,
  directly or transitively. The declaration closure check is in `Check.lean`.
- **VERIFIED** (Lean): `FiniteAppE.lean` and `FiniteAnchor.lean` pass
  standalone checks after their dependencies have built; the additional
  whole-full-H²-to-kernel lemma in `Comparison.lean` also passes. No new
  check was started during the interval of host load above 150.
- **VERIFIED** (Lean): `lake env lean scratch/rc-kato-p2-reroute/Check.lean`
  exits successfully after building the three top modules' `.olean`s.
  [`axioms.txt`](axioms.txt) records all 36 outputs. Only `propext`,
  `Classical.choice` and `Quot.sound` occur. The checker typechecks the
  definitional equality of the retained (K15) predicate and the old
  conclusion, and walks the new proofs and types to confirm that none of
  the replacement entry points uses the old conclusion or interface.

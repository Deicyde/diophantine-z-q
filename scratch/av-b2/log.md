# av-b2 results log

Task av-b2 (2026-11-13). Base: 8ec80711 + origin/wip/leaf-fold3 (f7951690) merged (55904cbb).
Targets (group B of docs/research/leaf-fold3.md §3, minus t5, t26, t27, t35, homLatticeCorr, t6, t7, t8):
`t4`, `t9`, `t10`, `t11b`, `t09SymmIsogenyExists`, `isogenyQuasiInverse`, `divisiblePoints`, `serreRigidity3`.

## Setup
- `lake build ZInQKernel.Hypotheses.JHeight` needed first (builds the upstream `lean/` package `ZInQ.*`); OK.
- Olean chain: leaf-fold3's `olean/*.lean` sources copied to `scratch/av-b2/olean/`; `scratch/av-b2/chain.sh`
  (copy of leaf-fold3's) compiles them with `scratch/av-b2/ctail.sh` (oleans written to scratch/av-b2/olean, gitignored).

## Statements read (VERIFIED, scratch/leaf-fold3/Leaves3.lean)
- `t9 : LeafPush.T09_WeilPairing.{0}` (l.11905). weil-pairing's `WeilPairing.oldT9_of_symmIsogeny`
  (l.49811) proves `OldT9.T09_WeilPairing` (verbatim copy with `Type u` → `Type`) from
  `T09_SymmIsogenyExists` and `IsogenyQuasiInverse`, both already fields of `OpenAddedLeaves3`.
- `divisiblePoints : WeilPairing.DivisiblePoints` (l.50148): all fields `K`, all `n > 0`, `[n]` onto on `A(K̄)`.
  `G0FibreSimple.MulIsogeny` (proved, `HSyn.mulIsogeny_proved`) gives `[n]` finite + surjective in char 0.
- `serreRigidity3 : HeckeRest.SerreRigidity3` (l.98709): over `Qbar = AlgebraicClosure ℚ`.
- `t10 : T10Etale.T10_TateDuality` (l.27887): over Mathlib's pro-étale `Scheme.EllAdicCohomology`
  (Mathlib/AlgebraicGeometry/Sites/ElladicCohomology.lean:76), a genuine definition; no comparison theorem
  for pro-étale cohomology of abelian varieties exists in Mathlib.
- `t11b : ZInQ.LeafPush2.T11b_Rigidity` (l.21477).
- `t4 : PkgI2.ReductionTorsionBijective.{0}` (l.1593).

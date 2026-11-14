# modular-split results log

Build: `.lake/build/lib/lean/ZInQKernel` copied from ~/dzq-wt/leaf-fold8 (sources identical except
`Contrib/CloudW07JacobiansCurves/`, verified by `git diff --name-only`); `lake build
ZInQKernel.OneProof.H.TailT ZInQKernel.OneProof.H.LPrefix` exits 0 (VERIFIED, 11-14 11:3x).

## r15 `HDec.HSyn.DeligneSerreConseq` — DONE
- `scratch/modular-split/R15.lean`: `ModularSplit.deligneSerreConseq_of_ds : DSThm966 → HDec.HSyn.DeligneSerreConseq`.
  Leaf: `ZInQ.Contrib.HodgeSplit.DSThm966` (Deligne–Serre 1974 Thm 4.1 / Diamond–Shurman Thm 9.6.6; already a
  published-form LEAF of the bundle, field `dsThm966`). Glue proved: `artinTransport_finite` (copy of hodge-split's
  `artinTransport_proof`, returning finite image), `attachedConj_proof` (T18+T19, kernel).
  Compile: `lake env lean scratch/modular-split/R15.lean` → axioms [propext, Classical.choice, Quot.sound]. VERIFIED.

## r17 `LadicCond.CarayolR17'` — REDUCED (not done: remaining leaf is a consequence, not printed form)
- `scratch/modular-split/R17.lean`: `ModularSplit.R17.carayolR17'_of_realization : CarayolRealization → LadicCond.CarayolR17'`.
  New glue proved: `condExp_conj` (Serre–Tate conductor exponent invariant under conjugation; via `invariants_conj`,
  `codimInv_conj`, `isAdapted_conj`, `swan_conj`), plus `attachedConj_proof` (T18+T19).
  Remaining leaf `CarayolRealization` (∃ semisimple attached ρ with condExp = v_p(N) at all p ≠ ℓ): consequence of
  Carayol 1986 Thm (A) + Casselman 1973 + Ribet irreducibility; not printed form (automorphic reps / LLC not in Mathlib).
  Compile: axioms [propext, Classical.choice, Quot.sound]. VERIFIED.

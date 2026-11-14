# modular-split (2026-11-14): fleet summary

**Verdict.** Of the six strict-GLUE rows, one is now a theorem from published-form leaves only (r15). One has no literature
leaf left (dimJacobianEqGenus). Two are narrowed to one realization-level leaf each (r17, eigenformHTNew). Two are still not
splittable, and the missing definitions are named (r16, t09). Report: `docs/research/modular-split.md`. Lean:
`scratch/modular-split/`. Results log: `log.md`. Nothing under `ZInQKernel/` was edited.

**What compiles.** Each file was checked with `lake env lean scratch/modular-split/<file>.lean`, and `#print axioms` gives
only `propext`, `Classical.choice` and `Quot.sound`. Every row statement is imported from the kernel, not copied.
- `R15.lean`: `ModularSplit.deligneSerreConseq_of_ds : DSThm966 → HDec.HSyn.DeligneSerreConseq`. **r15 done.** `DSThm966`
  (Deligne–Serre Thm 4.1) is already a bundle LEAF, so the field can be dropped: strict GLUE 27 → 26.
- `DimJac.lean`: `dimJacobianEqGenus_of_glue : H0DifferentialsEqHolo → CurvesG.DimJacobianEqGenus`. Milne Prop. 2.1 and
  Serre duality are now Lean proofs, using cloud-w07's vendored Jacobian-Challenge library (`Pic⁰` is smooth of relative
  dimension `dim H¹(𝒪)`; Serre duality). What is left is one project glue, `dim H⁰(X, Ω¹) = fieldGenus F`; no literature
  is involved.
- `R17.lean`: `carayolR17'_of_realization : CarayolRealization → LadicCond.CarayolR17'`. New proved glue: `condExp_conj`,
  the invariance of the Serre–Tate conductor under conjugation. The remaining leaf asserts Carayol's theorem for one
  realization (∃ semisimple attached ρ with the conductor).
- `EigenHT.lean`: `eigenformHTNew_of_coh : KatoRealizationCoh → HTDual → EigenformHTNew` and
  `eigenformHTNew_of_realization`. The contragredient (`dualGR`) is proved continuous, irreducible and attached. `HTDual`
  (the negation of HT weights) is a named glue.

**What remains.**
- `H0DifferentialsEqHolo`: textbook sheaf theory. Its steps (a)–(e) are in report §3.4.
- `HTDual`: needs Tate's theorems and the Hodge–Tate decomposition.
- `CarayolRealization`, `KatoRealizationCoh`: consequences (c). Their objects, Carayol's `σ_λ(π)` and Kato's `V_f`, are
  étale cohomology and cannot be defined in Mathlib.
- r16 needs Hecke correspondences on `X₁(N)`, the Hecke algebra of `J₁(N)`, and quotients `J₁(N)/I_f J₁(N)`.
- t09 needs `Pic⁰` of abelian varieties of dimension > 1 (the vendored library has it for curves only), `φ_L` and the
  Weil pairing.
- Build note: `DimJac.lean` needs the cloud-w07 modules built (about 700 vendored files, ~17 min).

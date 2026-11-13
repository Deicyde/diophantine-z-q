# r10-amend: fleet summary

**Main result: G9 is closed from the amended R10 alone.**
`ZInQ.Contrib.R10.g9GlueHT : G9GlueHT` (`ZInQKernel/Contrib/R10/Final.lean`) is proved outright.
`G9GlueHT` is g0-mod-galois's `G9Glue` with its hypothesis R10 replaced by the amended leaf
`DeRhamComparisonHT`, and the unused hypothesis T23 dropped. Two variants:
- `g9GlueHT' : G9GlueHT'` keeps T23;
- `g9Glue_of_deRhamComparisonHT : DeRhamComparisonHT → G9Glue` gives the verbatim `G9Glue`.

The proofs use g9-abvarbc's outright `abVarBaseChange` (merged) and g9-derham's descent argument.

**The amended leaf** (`Contrib/R10/Amend.lean`), `DeRhamComparisonHT`, states for each `p`, `F`, `A`:
- `(∀ g, A.dim = g → IsDeRhamOver ∧ htMultOver 0 = g ∧ htMultOver (−1) = g)`, which is the old R10;
- `∧ ∀ w ≠ 0, −1, htMultOver p (A.galRep p) w = 0`, the new clause.

Proved about it:
- `deRhamComparison_of_HT : → PkgI4.DeRhamComparison` (the old R10);
- `r10Weights_of_HT : → G9Bridge.R10Weights`;
- `deRhamComparisonWeights_of_HT`;
- `deRhamComparisonHT_iff : DeRhamComparisonHT ↔ DeRhamComparison ∧ R10Weights`;
- `htMultOver_eq_of_HT` (the multiplicity is `g · count w {0, −1}`).

Also proved (`Contrib/R10/Glue.lean`): `g9Glue_of_HT`, `g9GlueHT_of_abVarBaseChange`,
`g9GlueHT'_of_g9GlueHT`.

**Axioms.** All 11 theorems print `[propext, Classical.choice, Quot.sound]`.

**What compiles.** `lake build ZInQKernel.Contrib.R10.Final` succeeds (VERIFIED). There is no
sorry, no axiom, and no heartbeat option.

**Source** (part 1). The amended clause follows from two theorems:
- the Hodge–Tate decomposition `ℂ_p ⊗ H¹_et ≅ ℂ_p^g ⊕ ℂ_p(−1)^g`: Faltings, JAMS 1 (1988), Ch. III
  Thm 4.1 (the manuscript's own citation, L11003), or Fontaine, Invent. Math. 65 (1982), or Tate
  1967 §4 for good reduction;
- Tate's `ℂ_p(j)^{G_F} = 0` for `j ≠ 0` (Tate 1967 §3.3).

All these locators are **UNVERIFIED**: no source is on this host.

The sign convention was checked against the definitions: `htMultOver w = dim_F Hom_{G_F}(V, ℂ_p(−w))`,
so `ℚ_p(1)` has weight −1, as in R10, N5 and `G9Out`. The full statement (`g` at 0 and at −1, 0
elsewhere) is what the source gives; the amendment is not stronger.

**Statement change, for the integrator's leaf-fold/leaf-adopt** (exact text in
`docs/research/r10-amend.md` §3):
- add `PkgI4.DeRhamComparisonHT` to Leaves.lean after `DeRhamComparison`;
- replace `ResearchLeaves.r10 : PkgI4.DeRhamComparison` by `r10 : PkgI4.DeRhamComparisonHT`;
- keep `DeRhamComparison` as a derived Prop.

This task did not apply the change.

**Remains:** nothing in Lean for G9. Applying the leaf change is the integrator's job.
Report: `docs/research/r10-amend.md`; log: `scratch/r10-amend/log.md`.

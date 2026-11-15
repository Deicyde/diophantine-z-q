# unif-printed results log

Target: `BPAnalytic.Uniformization.UniformizationLeafAll` (ZInQKernel/HDecomp/Analytic/Uniformization.lean:91),
bundle field `uniformizationLeafAll` (OpenTextbookLeaves11).

## Stage 1 (scratch/unif-printed/Stage1.lean) — VERIFIED (compiled, `lake env lean`, no errors, no sorry)
- `UnifPrinted.MumfordComplexTorus` : Prop — Mumford §1 printed form over Mathlib `IsManifold 𝓘(ℂ,ℂ^g) ω`,
  `LieGroup 𝓘(ℂ,ℂ^g) ω`, T2, compact, connected ⇒ ∃ lattice Λ and biholomorphic additive-to-multiplicative
  `Torus Λ ≃ₘ^ω X`.
- `UnifPrinted.IsAnalyticStr A g` : the 4 clauses (U(ℂ) open; regular functions ContMDiffOn ω on U(ℂ); g regular
  functions are a local diffeomorphism at each point; topology = topology of regular functions).
- `UnifPrinted.AbVarAnalyticLieGroup` (composite, intermediate).
- `isLocalDiffeomorphAt_proj` (proved): proj : E → E⧸Λ is a local biholomorphism.
- `uniformizationLeafAll_of_lieGroup : MumfordComplexTorus → AbVarAnalyticLieGroup → UniformizationLeafAll` (proved).

## Stage 2a (Stage2a.lean) — VERIFIED (compiles alone)
- `CPt X`, `XPtIn`, `XevalAt` (rfl-equal to bp-analytic's on `A.X`), `classicalTopology X` (generateFrom basic sets).
- Leaves: `SmoothComplexManifold`, `ProperCompact`, `ConnectedConnected` (later restricted to proper X, see below).
- Proved: `isOpen_ptIn`, `xevalAt_res`, `good_of_isOpen`, `nhds_classical`, `xevalAt_comp`, `continuous_comp`,
  `contMDiff_comp` (regular maps holomorphic, given holo of regular functions on source, coordinates on target).

## Stage 2b (Stage2b.lean, Mathlib only) — VERIFIED (compiles alone)
- `ker_eq_bot_of_injOn` (implicit function thm ⇒ injective derivative), `contMDiffAt_rightInverse`,
  `mfderiv_section_aux`, `surjective_mfderiv_of_sections`.

## Stage 2c (Stage2c.lean, inside Unif.lean) — VERIFIED
- `irreducibleSpace_abVar`, `smooth_prod`, `isProper_prod`, `irreducibleSpace_prod` (Mathlib instances),
  `isIso_toUnit_ptObj`, `secL`, `secR`, `comp_secL`, `comp_secR`.
- `abVarAnalyticLieGroup_of_printed : SmoothComplexManifold → ProperCompact → ConnectedConnected → AbVarAnalyticLieGroup`.
- `uniformizationLeafAll_of_printed : MumfordComplexTorus → SmoothComplexManifold → ProperCompact → ConnectedConnected
  → UniformizationLeafAll`; `#print axioms`: [propext, Classical.choice, Quot.sound] (VERIFIED, Unif.lean).

## Leaf hypotheses weakened (safer): SmoothComplexManifold and ConnectedConnected now assume IsProper X.hom
  (ConnectedConnected: proper + IrreducibleSpace). Recompiled: VERIFIED.

## Deliverable: ZInQKernel/Contrib/OneProof/UniformizationPrinted.lean — `lake build` of the module: VERIFIED
  (Build completed successfully). gagaMorphism not used.
## autofold.json written; `autofold.py --dry-run`: exit 0, "strict count: 46/10 on 56 -> 49/10 on 59; strictest
  45/11 -> 48/11" (field still LEAF in this base's kinds.tsv; against the re-rated count 46/11 -> 49/10).

## #discharges — VERIFIED
- `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges`: success (12994 jobs).
- DischargesCheck.lean: `DISCHARGES [OpenTextbookLeaves11.uniformizationLeafAll] by UnifPrinted.uniformizationLeafAll_of_printed`,
  still assumes the four leaves, axioms standard; "63 open hypotheses, 1846 theorems checked, 9 discharge one".
- FoldDryRun.lean (autofold dry run minus line 1) compiles; sixContactMin_of_open30 standard axioms.

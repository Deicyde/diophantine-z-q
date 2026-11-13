# leaf-adopt2 (2026-11-12)

**Result.** `scratch/h-decomposition/Leaves.lean` now states **53 of the 56 leaves** of the H
decomposition concretely, plus three of the four parts of R1. Before this task: 48. Only **R17, T10
and R1(b)** are still `opaque`.
- leaf-push2's statements replace the placeholders R3, R18 and R22 (`ZInQ.LeafPush2.R03_LinYang`,
  `R18_Javanpeykar`, `R22_Pazuki`) and T11 (`T11a_RiemannEnd`, `T11b_Rigidity`).
- T12 is now glue: its used form `T12_ComplexConjEigen` is an unproved target.
- New textbook leaf T35 = `UniformizationExists`. I kept it rather than bp-analytic's
  `UniformizationLeaf` for three reasons:
  - R22 and T11a quantify over the same predicate;
  - it ties `g = dim A`;
  - it covers every `K` with `σ : K → ℂ`.

  bp-analytic stays the blueprint for its proof.
- rv-qm-polar applied. Every QM leaf's docstring (R1, R2, R5, R3) and the note now cite Lemma P with
  its conditions (type `μ` fixed, characteristic 0, `𝒪` maximal) instead of the SPECULATIVE
  bp-qmmoduli §2.2. No statement changed.

**Compiles (VERIFIED).** `lake env lean scratch/h-decomposition/Leaves.lean` exits 0 in 194 s.
- One `sorry` (`HSyn.glueOutputs_of_leaves`), 3 `opaque`, no `axiom`.
- All 131 `#print axioms` lines are standard, except `sixContactMin_of_leaves` (`sorryAx` through
  that `sorry`).
- The folded section is leaf-push2's file verbatim. difflib shows docstring changes only, plus two
  `_root_` declarations that `DefFaltingsSec` already has with identical text. `fold.py` reproduces
  the file from the base commit.
- Bundles: 61 concrete Props and 3 placeholders.
- New glue in Lean:
  - proved: `HSyn.isComplexConj_leafPush2_iff`;
  - target: `HSyn.HeightCopiesAgree`.

**Own check (with one independent read-only model review): no DEFECT.** Each replaced leaf is the
published statement or a consequence of it, never stronger, and not vacuous.
- RISKs: R22 identifies Pazuki's Def. 2.6 coordinates with `θ[a;b](0,Ω)` (UNVERIFIED). R3's `J`
  convention is checked only against hdec-elementary.
- Premise found: R22 needs both halves of H5, and R18 the upper half, for leaf-push2's copy of the
  height. That is the glue target `HeightCopiesAgree`.

**Remains.**
- Fold R17 (def-ladic-cond's `CarayolR17'`), which would give 54 of 56.
- T10 needs equivariant ℓ-adic cohomology.
- R1(b) needs analytification.
- Glue targets: `HeightCopiesAgree`, `T12_ComplexConjEigen`, `R03_LinYang_algClosed`.
- Human checks: Pazuki Def. 2.6, Lin–Yang (13)-(14), and the Lemma P locators (Buzzard p. 592,
  Rotger).
- WP1: unify the duplicate layers.
- `glueOutputs_of_leaves`.

Report: docs/research/leaf-adopt2.md. Log: scratch/leaf-adopt2/log.md.

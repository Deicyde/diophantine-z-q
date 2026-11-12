# glue-wp3 log

Task: WP3 of docs/research/h-decomposition.md: glue-descent's `LeafHasse`, `LeafLocalTwo` from the
announced T14-T15 (`PkgI6.BrauerHasse2C`, `BrauerReciprocity2C`, `LocalH2CardC`).

## Step 1: copies (VERIFIED by cmp / text check)
- Cochain, Constants, Chi, B2Glue, B2Assembly, B3Assembly.lean: byte-identical copies of scratch/glue-descent/ (cmp).
- PkgI6 defs in WP3.lean (IsCocycle2, IsCoboundary2, resC, BrauerHasse2C, BrauerReciprocity2C,
  H2TwoClasses, LocalH2CardC): each block occurs verbatim in scratch/pkg-I6/I6.lean and in
  scratch/h-decomposition/Leaves.lean L4153-4196 (python substring check).
- build.sh: compiles the chain to scratch/glue-wp3/.lake/out (1 min 43 s), then WP3.lean (5 s).

## Step 2: WP3.lean — compiles, no sorry; axioms propext, Classical.choice, Quot.sound (VERIFIED, lake env lean)
- sgn : ZMod 2 → ℂˣ (0 ↦ 1, 1 ↦ -1), unsgn : ℂˣ → ZMod 2; sgn_add, sgn_sub, sgn_neg, sgn_inv, sgn_sq,
  sgn_injective; sgn_unsgn (s² = 1 ⇒ sgn (unsgn s) = s).
- Over any topological group G: isCocycle2_iff (IsCocycle2 ε ↔ IsSignCocycle (sgnC ε)),
  isCoboundary2_iff (IsCoboundary2 ε ↔ SignCob (sgnC ε)), exists_of_isSignCocycle (every sign cocycle is sgnC of a
  ZMod 2 cocycle). Continuity into discrete ZMod 2 = IsLocallyConstant (Mathlib's ZMod topology is ⊥).
- pull_resp_sgnC: pull (resp p) (sgnC ε) = sgnC (resC ℚ_[p] ε) by rfl (same Mathlib map).
- real_of_finite: BrauerReciprocity2C ⇒ (cocycle trivial at all finite p ⇒ trivial at ℝ).
- leafHasse_of_T14 : BrauerHasse2C → BrauerReciprocity2C → LeafHasse.
- leafLocalTwo_of_T15 : LocalH2CardC → LeafLocalTwo (uses only the finite-place, "two nontrivial classes differ by
  a coboundary" half).
- b3_degree_le_QM_of_T14_T15: glue-descent's b3_degree_le_QM with hypotheses BrauerHasse2C, BrauerReciprocity2C,
  LocalH2CardC, LeafSqrtCrit (T30), LeafUnramified (T31) — all fields of Leaves.lean's TextbookLeaves.

## Step 3: converses — compile, axioms propext, Classical.choice, Quot.sound (VERIFIED)
- brauerHasse2C_of_leafHasse : LeafHasse → BrauerHasse2C (the ℝ hypothesis is simply dropped).
- leafHasse_iff (hR : BrauerReciprocity2C) : LeafHasse ↔ BrauerHasse2C.
- leafLocalTwo_iff : LeafLocalTwo ↔ ∀ p, (H2TwoClasses G_{ℚ_p}).2.
- Finding: glue-descent's two forms are equivalent to (parts of) the announced leaves; no residual gap between
  ±1 ⊂ ℂˣ and ZMod 2 coefficients, nor between resp p and resC ℚ_[p] (definitionally equal).
- Not used / not needed by B2-B3: the existence half of H2TwoClasses, the real half of LocalH2CardC.
- Out of scope of WP3 (unchanged): T30 LeafSqrtCrit, T31 LeafUnramified (inflation from Gal(L/ℚ) enters only
  there, through InflatedFrom), and instantiating ε on the actual algebra A.

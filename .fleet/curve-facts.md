# curve-facts (2026-11-13)

**Result.** mobius-glue's `CurveRatFactor` and `CurveSurj` are proved in Lean from three smaller
named facts, all stated over a field, with the statements unchanged (verbatim check IDENTICAL):

`curveFacts_of_leaves (h1 : SmoothStalkDimOne) (h2 : ConstOrOntoAlgClosed) (h3 : RatFactorAlgClosed) : CurveRatFactor ∧ CurveSurj`

- **C1b `SmoothStalkDimOne`** (glue, dimension theory): if `X → Spec K` is smooth of relative
  dimension 1 and `x` is a closed point, then `ringKrullDim 𝒪_{X,x} = 1`.
- **C2K `ConstOrOntoAlgClosed`** (textbook leaf, Hartshorne II.6.8, UNVERIFIED numbering): take
  `X` proper and smooth of relative dimension 1 over an algebraically closed `K`, and
  `σ : ToP1 X`. On the `K`-points of each connected component of `X`, `σ` is constant or onto
  `P¹(K)`.
- **C3K `RatFactorAlgClosed`** (glue, textbook consequence): the same setting with char 0. On a
  component where `σ` is nonconstant, a `ρ` constant on the `σ`-fibres is `[F : G] ∘ σ` with
  `F, G` coprime.

`CurveSurj` needs only C1b and C2K; `CurveRatFactor` needs only C2K and C3K. So `MobiusGlue`
now rests on C1b, C2K, C3K and the textbook leaf T5.

**Proved in Lean** (all from Mathlib, no new hypotheses):
- finitely many geometric components (`S_ℚ̄` is Noetherian);
- connected components of a Noetherian space are open;
- a Jacobson space with an open set having finitely many closed points has an open point;
- C1b ⇒ no isolated points (`ringKrullDim_stalk_eq_coheight`);
- ⇒ infinitely many `ℚ̄`-points on each geometric component;
- the dictionary between `ℚ̄`-points of `S/ℚ` and sections of `S_ℚ̄` (`bcPt`, `ptOfSection`,
  `val_bcPt`);
- coprime rational interpolation (`Mob.exists_interp`);
- the multi-component combination.

**Compiles.** `scratch/curve-facts/CurveFacts.lean`: 0 errors, 0 warnings, axioms `propext`,
`Classical.choice`, `Quot.sound` (`run8.txt`). Imports only `ZInQKernel.HDecomp.QM.Pairs`.

**Checks.** A fresh model agent, not a human, reviewed C1a, C2K and C3K: TRUE, none vacuous.
C2K needs properness and algebraic closedness; C3K needs char 0 (Frobenius counterexample) and
algebraic closedness. C1b is standard but was added after that review.

**Remains.** C1b, C2K and C3K are not in Mathlib v4.35, which has no dimension theory of
smooth morphisms, no `P¹` scheme, and no curves, degrees or fibre counts. Two further cuts are
argued in `docs/research/curve-facts.md` §6 but not formalized:
- C2K to the fact that global functions on a proper connected smooth scheme are constant;
- C3K to an algebraic discriminant lemma plus an image-curve statement.

Report: `docs/research/curve-facts.md`; log: `scratch/curve-facts/log.md`.

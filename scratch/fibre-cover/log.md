# fibre-cover results log

## Setup (04:10)
- Base 2dd83306. Built `ZInQKernel.HDecomp.QM.Leaves` (+ Descent.Constants, B2Glue, Mult Constants): 4 min.
- `scratch/fibre-cover/FibreCover.lean`: `IF`, `T`, `IsModelOver`, `FibreCtx`, `RationalFibre`,
  `FibreCoverOut`, `FibreCoverExists` copied verbatim from `scratch/g0-mod-field/ModField.lean`
  (namespace `G0ModField`). Imports: QM.Leaves, Descent.Constants, Descent.B2Glue,
  Multiplication.Certificate.Constants, Hypotheses.JHeight. `lake env lean` ~2 min.
- Pitfall: `open GlueDescent.B3Q` (namespace absent under these imports) makes the whole `open`
  fail; `ι` is a token here (like `η` under `open MonObj`), rename binders.

## run1-3 (04:35): Part 1, FibreCoverOut depends only on the residue field of y
- Proved: `spec_to_specQ_eq` (copied from rv-g0pieces), `exists_factor_of_residueImage_le`
  (`residueImage y ≤ K` ⇒ `y = yK ∘ Spec(K ⊆ ℚ̄)`), `residueImage_le_aux`, `residueImage_comp_le`,
  `isModelOver_of_baseChange` (IsBaseChangeOf + QML3.Iso ⇒ IsModelOver, via
  `IsPullback.isoPullback`), `rationalFibre_of_le` (R1fp ⇒ rational fibre over any `K ⊇ residueImage y`),
  `FibreFieldOut` (def), `fibreCoverOut_iff` (R1fp: FibreCoverOut Y Φ u P ↔ FibreFieldOut (residueImage y) u),
  `fibreCoverOut_indep` (two moduli bijections Φ, Φ' with R1fp on the same Y, same point y: G2 agrees).
- VERIFIED: `lake env lean scratch/fibre-cover/FibreCover.lean`: 0 errors, 0 warnings.

## run4-5: Parts 2-3, the reduction
- Proved: `fibreFieldOut_of` (primitive element `β` of `F`, `f = minpoly ℚ β`: separable, degree
  `[F:ℚ] ≤ 324`, `F ≤ ℚ(roots f)`; unramified via the textbook Prop `UnramifiedConjugates`).
- Named Props: `UnramifiedConjugates` (textbook), `FibreDegree` (glue), `FibreUnramified`
  (glue, Prop. TS + Lemma NV; pinning caveat).
- Proved: `fibreCoverExists_of : FibreDegree → FibreUnramified → UnramifiedConjugates → FibreCoverExists`.
- VERIFIED: 0 errors; `#print axioms` of `fibreCoverOut_iff`, `fibreCoverOut_indep`,
  `fibreCoverExists_of`: [propext, Classical.choice, Quot.sound].

## run6-9: Part 4, FibreDegree from the intrinsic count
- New Prop `TwistClassCard` (glue: the `Aut 𝒪`-twist class of a `QML3 ℚ̄` object has `≤ 324`
  classes; N5 L425-441; mentions no moduli scheme).
- Proved: `finrank_le_of_card_algHom_le` (finite `K ≤ F`: `[K:ℚ] = #Hom(K, ℚ̄)` by `AlgHom.card`,
  each extends to `F` by `IsAlgClosed.surjective_domRestrict_of_isAlgebraic`),
  `finiteDimensional_of_card_algHom_le` (maximal finite subfield via `Nat.findGreatest`, then
  `eq_of_le_of_finrank_le`), `fibreDegree_of : TwistClassCard → FibreDegree` (embeddings `e` of
  `ℚ(y)` give distinct points `e ∘ y_F` over `J(u)` (`ToP1.val_comp`), injectivity by
  `IntermediateField.algHom_ext_of_eq_adjoin`; R2fp puts their classes in the twist class).
- Pitfall: `rw` with `(fieldMap e ≫ yF).left = Spec.map … ≫ yF.left` makes ill-typed motives
  (`(fieldPt K).left` vs `Spec (of K)`); state lemmas at scheme level and apply to `y.left`.

## run10-11: Part 5, pinning
- Proved: `residueImage_comp_le_self(_aux)`, `residueImage_comp_iso`, `fibreUnramified_of_pinned`
  (`CurvePinned Y₀ π₀` + `FibreUnramifiedOn Y₀ π₀` ⇒ `FibreUnramified`),
  `fibreCoverExists_of_twistClassCard`, `fibreCoverExists_of_pinned`.
- VERIFIED: 0 errors, 0 warnings; all six `#print axioms`: [propext, Classical.choice, Quot.sound]
  (scratch/fibre-cover/compile_out.txt).

## run12-15: Part 6, TwistClassCard reduced
- New Props: `TorsionBound3` (glue + textbook leaf: `A(ℚ̄)[3]` has `≤ 81` points for `dim A = 2`;
  from `PkgI2.TorsionStructure` at `K = ℚ̄` plus `A(ℚ̄) ↪ A(AlgebraicClosure ℚ̄)`, not compiled),
  `InnerTwistCount` (glue: every `α ∈ Aut 𝒪` is `w ∘ Ad u`, `w` in a fixed set of `≤ 4`,
  `u ∈ 𝒪^×`; `N_B(𝒪)/ℚ^×𝒪^× ≅ (ℤ/2)²`, N5 L425-429).
- Proved: `level3_eta_eq`, `level3_ext` (η determined by η(1)), `level3_three` (`3•η(1) = 0`),
  `innerIso` (`ι∘w∘Ad u ≅ ι∘w` via `ι(w u⁻¹)`), `transportLevel`, `transportIso`,
  `twistClassCard_of : TorsionBound3 → InnerTwistCount → TwistClassCard` (image of `W × A[3]`,
  `4·81 = 324`), `fibreCoverExists_of_pinned'`.
- Pitfall: under `open MonObj`, `mul_one`/`mul_assoc`/`one_mul` resolve to MonObj lemmas; use `_root_.`.
- VERIFIED: 0 errors, 0 warnings; all eight `#print axioms`: [propext, Classical.choice, Quot.sound].

## run16-19: Part 7, TorsionBound3 from the bundle's leaf T5
- Proved: `spec_comp_injective` (precomposition with `Spec L → Spec K` injective on points),
  `specIncl`, `torsionBound3_of : ObjBridge.TorsionStructure → TorsionBound3` (`A(ℚ̄)[3]` injects
  into `A(AlgebraicClosure ℚ̄)[3] ≃ (ZMod 3)^4`, 81 points), `torsionBound3_of_t5` (the bundle's
  `TextbookLeaves.t5 : PkgI2.TorsionStructure.{0}`, via `ObjBridge.torsionStructure_iff`),
  `fibreCoverExists_of_leafTorsion`.
- Pitfall: `ι` is a token (GrpObj.inv notation) under these opens; rename binders.
- VERIFIED: 0 errors, 0 warnings; all eleven `#print axioms`: [propext, Classical.choice, Quot.sound].

## run20-22: Part 8, Prop. TS in Beckmann's inertia form
- New Prop `PropTS Y₀ π₀` (glue from leaves: Beckmann 1991 Prop. 4.2 or T1-T2 + R1(d)): for
  rational non-branch `t`, `p > 324`, and the three inertia orders `e_b/gcd(e_b, m_b) = 1`
  (`4 ∣ v_p(t)⁺`, `6 ∣ (−v_p(t))⁺`, `2 ∣ v_p(t+16/27)⁺`), `ℚ(y)` is unramified at `p` for every
  `ℚ̄`-point `y` over `t`.
- Proved: `fibreUnramifiedOn_of_propTS` (with `GlueRepo.PR.inertia_trivial_iff_not_dvd`,
  `J_ne_zero`, `J_ne_branch`; `S_mul ⊇ primes ≤ 324` by `Mult.mem_S_mul`, `mem_S_ht`;
  `ZInQ.JHeight.Jmap` and `GlueRepo.PR.Jmap` agree by `rfl`), `fibreCoverExists_of_propTS`
  (T5, InnerTwistCount, CurvePinned, PropTS, UnramifiedConjugates ⊢ FibreCoverExists).
- Added import `ZInQKernel.HDecomp.Repo.PRArith` (olean present).
- VERIFIED: 0 errors, 0 warnings; all 13 `#print axioms`: [propext, Classical.choice, Quot.sound].
- VERIFIED (script): the seven copied definitions are character-identical to ModField.lean.

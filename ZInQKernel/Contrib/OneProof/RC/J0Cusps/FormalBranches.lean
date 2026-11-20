import ZInQKernel.Contrib.OneProof.RC.X0Model.Chart
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_ModularPolynomialData_exists_isPrimitiveRoot_forall_isRoot_cosetConj_complex
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_ModularPolynomialData_forall_isRoot_cosetConj_jqModC_of_complex

/-! Formal branches of the normalization, using the modular polynomial at
the triangular cosets. Tex 1785–1787 and 2937–2939; on the spot (c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory ModularCurve Polynomial IntermediateField

namespace ZInQ.Manuscript.RC.J0Cusps

private def equation (N : ℕ) [NeZero N] : ModularPolynomialData N :=
  Classical.choice (nonempty_modularPolynomialData N)

private theorem liftEquation (N : ℕ) [NeZero N] {F : Type} [Field F]
    (e : ℚ⟮jq⟯ →+* F) (y : F) (hy : (equation N).toAdjoin.eval₂ e y = 0) :
    (minpoly ℚ⟮jq⟯ (jqN N)).eval₂ e y = 0 := by
  rw [(equation N).minpoly_jqN_eq (phiIrreducible_all N (equation N))]
  exact hy

private def liftBranch (N : ℕ) [NeZero N] {F : Type} [Field F]
    (e : ℚ⟮jq⟯ →+* F) (y : F) (hy : (equation N).toAdjoin.eval₂ e y = 0) :
    modularFunctionField N →+* F :=
  (AdjoinRoot.lift e y (liftEquation N e y hy)).comp
    ((adjoinRootEquivAdjoin ℚ⟮jq⟯ (X0Model.integral_jN (equation N))).symm.toRingHom.comp
      (X0Model.secondCoordinate N).toRingHom)

private theorem liftBranch_j (N : ℕ) [NeZero N] {F : Type} [Field F]
    (e : ℚ⟮jq⟯ →+* F) (y : F) (hy : (equation N).toAdjoin.eval₂ e y = 0) :
    liftBranch N e y hy ⟨jq, jq_mem N⟩ = e jGen := by
  let a := (adjoinRootEquivAdjoin ℚ⟮jq⟯ (X0Model.integral_jN (equation N))).symm
  have h : X0Model.secondCoordinate N ⟨jq, jq_mem N⟩ =
      algebraMap ℚ⟮jq⟯ (↥ℚ⟮jq⟯)⟮jqN N⟯ jGen := Subtype.ext rfl
  change AdjoinRoot.lift e y (liftEquation N e y hy)
    (a (X0Model.secondCoordinate N ⟨jq, jq_mem N⟩)) = _
  rw [h, a.commutes, AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of]

set_option backward.isDefEq.respectTransparency false in
private theorem liftBranch_jN (N : ℕ) [NeZero N] {F : Type} [Field F]
    (e : ℚ⟮jq⟯ →+* F) (y : F) (hy : (equation N).toAdjoin.eval₂ e y = 0) :
    liftBranch N e y hy ⟨jqN N, jqN_mem N⟩ = y := by
  let a := (adjoinRootEquivAdjoin ℚ⟮jq⟯ (X0Model.integral_jN (equation N))).symm
  have h : X0Model.secondCoordinate N ⟨jqN N, jqN_mem N⟩ =
      AdjoinSimple.gen ℚ⟮jq⟯ (jqN N) := Subtype.ext rfl
  change AdjoinRoot.lift e y (liftEquation N e y hy)
    (a (X0Model.secondCoordinate N ⟨jqN N, jqN_mem N⟩)) = _
  rw [h, show a (AdjoinSimple.gen ℚ⟮jq⟯ (jqN N)) = _ from
    adjoinRootEquivAdjoin_symm_apply_gen _ _, AdjoinRoot.lift_root]

private def firstAtCusp (K : Type) [Field K] [Algebra ℚ K] (N : ℕ) [NeZero N] :
    ℚ⟮jq⟯ →+* LaurentSeries K :=
  (qExpand K N).comp ((coeffEmb K).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))

private theorem firstAtCusp_j (K : Type) [Field K] [Algebra ℚ K] (N : ℕ) [NeZero N] :
    firstAtCusp K N jGen = jqNModC K N := by
  change qExpand K N (coeffEmb K jq) = _
  rw [show coeffEmb K jq = jqModC K from map_jqModC (algebraMap ℚ K)]
  rfl

private theorem firstAtCusp_eval (K : Type) [Field K] [Algebra ℚ K] (N : ℕ) [NeZero N] :
    (firstAtCusp K N).comp evalAtJGen =
      Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) (jqNModC K N) := by
  apply Polynomial.ringHom_ext' (Subsingleton.elim _ _)
  change firstAtCusp K N (evalAtJGen Polynomial.X) = Polynomial.eval₂ _ _ Polynomial.X
  rw [show evalAtJGen Polynomial.X = jGen from Polynomial.eval₂_X _ _, Polynomial.eval₂_X]
  exact firstAtCusp_j K N

private theorem triangular_root (K : Type) [Field K] [Algebra ℚ K] (N : ℕ) [NeZero N]
    (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ N) (t : ℕ × ℕ × ℕ) (ht : t ∈ primCosetReps N) :
    (equation N).toAdjoin.eval₂ (firstAtCusp K N) (cosetConj ζ (jqModC K) t) = 0 := by
  rw [ModularPolynomialData.toAdjoin, Polynomial.eval₂_map, firstAtCusp_eval,
    Polynomial.eval₂_eq_eval_map]
  exact (equation N).forall_isRoot_cosetConj_jqModC_of_complex N
    ((equation N).exists_isPrimitiveRoot_forall_isRoot_cosetConj_complex N) K ζ hζ t ht

/-- The Laurent field realization attached to a primitive triangular coset.
The parameter has width `N`, so the image of `j` is `j(q^N)`. -/
def triangularField (K : Type) [Field K] [Algebra ℚ K] (N : ℕ) [NeZero N]
    (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ N) (t : ℕ × ℕ × ℕ) (ht : t ∈ primCosetReps N) :
    modularFunctionField N →+* LaurentSeries K :=
  liftBranch N (firstAtCusp K N) _ (triangular_root K N ζ hζ t ht)

theorem triangularField_j (K : Type) [Field K] [Algebra ℚ K] (N : ℕ) [NeZero N]
    (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ N) (t : ℕ × ℕ × ℕ) (ht : t ∈ primCosetReps N) :
    triangularField K N ζ hζ t ht ⟨jq, jq_mem N⟩ = jqNModC K N :=
  (liftBranch_j N _ _ _).trans (firstAtCusp_j K N)

theorem triangularField_jN (K : Type) [Field K] [Algebra ℚ K] (N : ℕ) [NeZero N]
    (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ N) (t : ℕ × ℕ × ℕ) (ht : t ∈ primCosetReps N) :
    triangularField K N ζ hζ t ht ⟨jqN N, jqN_mem N⟩ = cosetConj ζ (jqModC K) t :=
  liftBranch_jN N _ _ _

private theorem zero_root (N : ℕ) [NeZero N] :
    (equation N).toAdjoin.eval₂ (firstAtCusp ℚ N) jq = 0 := by
  obtain ⟨ζ, hζ, _⟩ := (equation N).exists_isPrimitiveRoot_forall_isRoot_cosetConj_complex N
  have hm : (1, 0, N) ∈ primCosetReps N :=
    (mem_primCosetReps (NeZero.ne N)).2 (by simp [Nat.pos_of_ne_zero (NeZero.ne N)])
  have hz := triangular_root ℂ N ζ hζ (1, 0, N) hm
  simp only [cosetConj_eq, cosetSubst, RingHom.comp_apply, mul_zero, pow_zero, qTwist_one_apply,
    Nat.mul_one, qExpand_one_apply] at hz
  have hcoe : (coeffEmb ℂ).comp (firstAtCusp ℚ N) = firstAtCusp ℂ N := by
    apply RingHom.ext
    intro x
    ext n
    by_cases hn : (N : ℤ) ∣ n
    · obtain ⟨m, rfl⟩ := hn
      simp [firstAtCusp, coeffEmb_coeff, qExpand_coeff_mul]
    · simp [firstAtCusp, coeffEmb_coeff, qExpand_coeff_of_not_dvd N _ hn]
  apply (coeffEmb ℂ).injective
  rw [Polynomial.hom_eval₂, hcoe, show coeffEmb ℂ jq = jqModC ℂ from map_jqModC (algebraMap ℚ ℂ),
    map_zero]
  exact hz

/-- At the zero cusp in the width-`N` parameter the two Laurent generators
are exchanged. Their coefficients, and the resulting cusp point, are rational. -/
def zeroField (N : ℕ) [NeZero N] : modularFunctionField N →+* LaurentSeries ℚ :=
  liftBranch N (firstAtCusp ℚ N) jq (zero_root N)

theorem zeroField_j (N : ℕ) [NeZero N] :
    zeroField N ⟨jq, jq_mem N⟩ = jqN N :=
  (liftBranch_j N _ _ _).trans ((firstAtCusp_j ℚ N).trans (by rw [jqNModC, jqModC_rat]; rfl))

theorem zeroField_jN (N : ℕ) [NeZero N] :
    zeroField N ⟨jqN N, jqN_mem N⟩ = jq :=
  liftBranch_jN N _ _ _

/-- The valuative arc of a specified Laurent branch of the normal model. -/
def formalBranch (N : ℕ) [NeZero N] {K : Type} [Field K] [Algebra ℚ K]
    (e : modularFunctionField N →+* LaurentSeries K) :
    Spec (.of (PowerSeries K)) ⟶ X0Model.curve N :=
  (X0Model.existsUnique_specialization (R := PowerSeries K) N e).exists.choose

theorem formalBranch_generic (N : ℕ) [NeZero N] {K : Type} [Field K] [Algebra ℚ K]
    (e : modularFunctionField N →+* LaurentSeries K) :
    Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries K) (LaurentSeries K))) ≫
      formalBranch N e = X0Model.genericMap N e :=
  (X0Model.existsUnique_specialization (R := PowerSeries K) N e).exists.choose_spec.1

/-- The point at the closed end of the Laurent branch. -/
def branchPoint (N : ℕ) [NeZero N] {K : Type} [Field K] [Algebra ℚ K]
    (e : modularFunctionField N →+* LaurentSeries K) : Spec (.of K) ⟶ X0Model.curve N :=
  Spec.map (CommRingCat.ofHom PowerSeries.constantCoeff) ≫ formalBranch N e

/-- The rational point selected by the width-`N` zero branch. -/
abbrev zeroPoint (N : ℕ) [NeZero N] : Spec (.of ℚ) ⟶ X0Model.curve N :=
  branchPoint N (zeroField N)

theorem zeroPoint_overQ (N : ℕ) [NeZero N] : zeroPoint N ≫ X0Model.overQ N = 𝟙 _ := by
  apply Spec.homEquiv.injective
  exact CommRingCat.hom_ext (Subsingleton.elim _ _)


end ZInQ.Manuscript.RC.J0Cusps

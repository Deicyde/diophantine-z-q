import ZInQKernel.Contrib.OneProof.SelmerTwoPower

/-!
# Non-vacuity of `Sel₂(E_ℓ/ℚ)` over `SelmerTwoPower`

Fork issue #83, review of the genuine Selmer definitions (`ZInQ.Manuscript.SelmerTwoPower`). Two
checks that `selmerAt (curve ℓ) 1 = Sel₂(E_ℓ/ℚ)` (all places of `ℚ`) is neither zero nor all of
`H¹(G_ℚ, E_ℓ[2])`, for every `ℓ ≠ 0`:

* `selmerAt_curve_exists_ne_zero`: the Kummer class of the rational two-torsion point `(0, 0)` is a
  nonzero element of `Sel₂(E_ℓ/ℚ)`, since `(0, 0) ∉ 2 E_ℓ(ℚ)` (`two_nsmul_ne_zeroPt`: `x(2Q) = 0`
  forces `(x(Q)² + 3ℓ²)² = 0`).
* `cls_not_mem_selmerAt`: the class `c` of the continuous cocycle `σ ↦ χ_{-1}(σ) · (0, 0)` is not in
  `Sel₂(E_ℓ/ℚ)`, because its image in `H¹(G_ℝ, E_ℓ(ℝˢ))` is nonzero: complex conjugation `τ` would
  satisfy `τ R = R + (0, 0)` for some `R = (x, y)`, which forces `x · τ(x) = -3ℓ²`, while
  `x · τ(x) = |x|² ≥ 0`. So the archimedean local condition is not vacuous.
  `cls_twoPower_not_mem_selmerTwoPower`: the image of `c` in `H¹(G_ℚ, E_ℓ[2^∞])` is not in
  `Sel_{2^∞}(E_ℓ/ℚ)` either.
-/

open WeierstrassCurve TauCeti TauCeti.ContCohomology ZInQ.Manuscript
  ZInQ.Manuscript.SelmerTwoPower

noncomputable section

open scoped Classical Pointwise

namespace ZInQ.Manuscript.SelmerTwoPower.NonVacuity

/-- `E_ℓ` is an elliptic curve for `ℓ ≠ 0` (`Δ = 2304 ℓ⁶`). -/
theorem curve_isElliptic' {ℓ : ℚ} (hℓ : ℓ ≠ 0) : (curve ℓ).IsElliptic :=
  ⟨by rw [curve_Δ]; exact isUnit_iff_ne_zero.mpr (mul_ne_zero (by norm_num) (pow_ne_zero 6 hℓ))⟩

/-- `(0, 0)` is a nonsingular point of `E_ℓ`. -/
theorem curve_nonsingular_zero {ℓ : ℚ} (hℓ : ℓ ≠ 0) : (curve ℓ).toAffine.Nonsingular 0 0 := by
  have := curve_isElliptic' hℓ
  exact Affine.equation_iff_nonsingular.mp (by rw [Affine.equation_iff]; simp [curve])

/-- A function on a topological group that is constant on the left cosets of an open subgroup is
continuous. -/
lemma continuous_of_forall_mul_mem {G Y : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [TopologicalSpace Y] (U : Subgroup G) (hU : IsOpen (U : Set G))
    (f : G → Y) (hf : ∀ x, ∀ u ∈ U, f (x * u) = f x) : Continuous f := by
  rw [continuous_def]
  intro s _
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  refine ⟨x • (U : Set G), ?_, hU.leftCoset x, ⟨1, U.one_mem, by simp⟩⟩
  rintro _ ⟨u, hu, rfl⟩
  change f (x * u) ∈ s
  rw [hf x u hu]
  exact hx

/-! ### A square root of `-1` and its quadratic character -/

lemma exists_sqrtNegOne : ∃ z : SeparableClosure ℚ, z ^ 2 = -1 :=
  @IsSepClosed.exists_pow_nat_eq _ _ _ (-1) 2 ⟨by norm_num⟩

/-- A square root of `-1` in `ℚˢ`. -/
def sqrtNegOne : SeparableClosure ℚ := exists_sqrtNegOne.choose

lemma sqrtNegOne_sq : sqrtNegOne ^ 2 = -1 := exists_sqrtNegOne.choose_spec

lemma sqrtNegOne_ne_neg : sqrtNegOne ≠ -sqrtNegOne := by
  intro h
  have h2 : (2 : SeparableClosure ℚ) * sqrtNegOne = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with h2 | h2
  · exact two_ne_zero h2
  · have := sqrtNegOne_sq
    rw [h2] at this
    norm_num at this

lemma gal_sqrtNegOne (σ : AbsoluteGaloisGroup ℚ) :
    σ sqrtNegOne = sqrtNegOne ∨ σ sqrtNegOne = -sqrtNegOne := by
  have h : (σ sqrtNegOne - sqrtNegOne) * (σ sqrtNegOne + sqrtNegOne) = 0 := by
    have h1 : (σ sqrtNegOne) ^ 2 = -1 := by rw [← map_pow, sqrtNegOne_sq, map_neg, map_one]
    linear_combination h1 - sqrtNegOne_sq
  rcases mul_eq_zero.mp h with h | h
  · left; linear_combination h
  · right; linear_combination h

/-! ### The cocycle `σ ↦ χ_{-1}(σ) · (0, 0)` -/

variable {ℓ : ℚ}

/-- The rational two-torsion point `(0, 0)`. -/
def T0 (hℓ : ℓ ≠ 0) : (curve ℓ).toAffine.Point := .some 0 0 (curve_nonsingular_zero hℓ)

lemma two_nsmul_T0 (hℓ : ℓ ≠ 0) : (2 ^ 1 : ℕ) • T0 hℓ = 0 := by
  rw [pow_one, two_nsmul]
  exact Affine.Point.add_self_of_Y_eq (by simp [Affine.negY, curve])

/-- `(0, 0)` as an element of `E_ℓ(ℚˢ)[2]`. -/
def T0c (hℓ : ℓ ≠ 0) : (curve ℓ).TorsionCoeff (2 ^ 1) :=
  (curve ℓ).baseTorsionCoeff (2 ^ 1)
    ⟨T0 hℓ, AddSubgroup.torsionBy.nsmul_iff.mpr (two_nsmul_T0 hℓ)⟩

lemma T0c_add_self (hℓ : ℓ ≠ 0) : T0c hℓ + T0c hℓ = 0 := by
  have h := AddSubgroup.torsionBy.nsmul_iff.mp (T0c hℓ).2
  apply Subtype.ext
  rw [AddSubgroup.coe_add, ← two_nsmul]
  simpa using h

lemma smul_T0c (hℓ : ℓ ≠ 0) (σ : AbsoluteGaloisGroup ℚ) : σ • T0c hℓ = T0c hℓ :=
  (curve ℓ).smul_baseTorsionCoeff σ _

/-- The cocycle `σ ↦ χ_{-1}(σ) · (0, 0)`. -/
def cocyc (hℓ : ℓ ≠ 0) (σ : AbsoluteGaloisGroup ℚ) : (curve ℓ).TorsionCoeff (2 ^ 1) :=
  if σ sqrtNegOne = sqrtNegOne then 0 else T0c hℓ

lemma cocyc_continuous (hℓ : ℓ ≠ 0) : Continuous (cocyc hℓ) := by
  refine continuous_of_forall_mul_mem (MulAction.stabilizer (AbsoluteGaloisGroup ℚ) sqrtNegOne)
    (stabilizer_isOpen_of_isIntegral sqrtNegOne) _ fun x u hu => ?_
  have hu' : u sqrtNegOne = sqrtNegOne := hu
  have : (x * u) sqrtNegOne = x sqrtNegOne := by
    rw [AlgEquiv.mul_apply, hu']
  simp only [cocyc, this]

lemma cocyc_isCocycle (hℓ : ℓ ≠ 0) : groupCohomology.IsCocycle₁ (cocyc hℓ) := by
  intro g h
  have hgh : (g * h) sqrtNegOne = g (h sqrtNegOne) := AlgEquiv.mul_apply _ _ _
  have hneg := sqrtNegOne_ne_neg
  rcases gal_sqrtNegOne h with hh | hh <;> rcases gal_sqrtNegOne g with hg | hg
  · simp [cocyc, hgh, hh, hg]
  · have : (g * h) sqrtNegOne ≠ sqrtNegOne := by rw [hgh, hh, hg]; exact hneg.symm
    simp [cocyc, hgh, hh, hg, smul_zero]
  · have h1 : (g * h) sqrtNegOne ≠ sqrtNegOne := by
      rw [hgh, hh, map_neg, hg]; exact hneg.symm
    have h2 : h sqrtNegOne ≠ sqrtNegOne := by rw [hh]; exact hneg.symm
    simp only [cocyc, h1, h2, hg, ↓reduceIte, smul_T0c, add_zero]
  · have h1 : (g * h) sqrtNegOne = sqrtNegOne := by rw [hgh, hh, map_neg, hg, neg_neg]
    have h2 : h sqrtNegOne ≠ sqrtNegOne := by rw [hh]; exact hneg.symm
    have h3 : g sqrtNegOne ≠ sqrtNegOne := by rw [hg]; exact hneg.symm
    simp only [cocyc, h1, h2, h3, ↓reduceIte, smul_T0c]
    exact (T0c_add_self hℓ).symm

lemma cocyc_mem_Z1 (hℓ : ℓ ≠ 0) :
    cocyc hℓ ∈ Z1 (AbsoluteGaloisGroup ℚ) ((curve ℓ).TorsionCoeff (2 ^ 1)) :=
  mem_Z1_iff.mpr ⟨cocyc_continuous hℓ, cocyc_isCocycle hℓ⟩

/-- The class `c = [σ ↦ χ_{-1}(σ) · (0, 0)] ∈ H¹(G_ℚ, E_ℓ[2])`. -/
def cls (hℓ : ℓ ≠ 0) : H1 (AbsoluteGaloisGroup ℚ) ((curve ℓ).TorsionCoeff (2 ^ 1)) :=
  H1pi _ _ ⟨cocyc hℓ, cocyc_mem_Z1 hℓ⟩

/-! ### `x · τ(x) ≥ 0` for the nontrivial `τ ∈ G_ℝ` -/

/-- `ℂ` is an algebraic closure of `ℝ`. -/
local instance : IsAlgClosure ℝ ℂ := ⟨Complex.isAlgClosed, inferInstance⟩

/-- `ℝˢ` is an algebraic closure of `ℝ`. -/
local instance : IsAlgClosure ℝ (SeparableClosure ℝ) := ⟨inferInstance, inferInstance⟩

/-- If `τ ∈ Gal(ℝˢ/ℝ)` moves some element, then `x · τ(x)` is never a negative real. -/
lemma mul_gal_ne_neg (τ : AbsoluteGaloisGroup ℝ) {w : SeparableClosure ℝ} (hw : τ w ≠ w)
    (x : SeparableClosure ℝ) {r : ℝ} (hr : r < 0) :
    x * τ x ≠ algebraMap ℝ (SeparableClosure ℝ) r := by
  intro hx
  let e : SeparableClosure ℝ ≃ₐ[ℝ] ℂ := IsAlgClosure.equiv ℝ (SeparableClosure ℝ) ℂ
  let τ' : ℂ ≃ₐ[ℝ] ℂ := (e.symm.trans τ).trans e
  have hτ' : ∀ z, τ' z = e (τ (e.symm z)) := fun z => rfl
  rcases Complex.real_algHom_eq_id_or_conj τ'.toAlgHom with h | h
  · apply hw
    have := congrArg (fun f : ℂ →ₐ[ℝ] ℂ => f (e w)) h
    simp only [AlgEquiv.coe_toAlgHom, AlgHom.coe_id, id_eq] at this
    rw [hτ', AlgEquiv.symm_apply_apply] at this
    exact e.injective this
  · have hconj : e (τ x) = (starRingEnd ℂ) (e x) := by
      have := congrArg (fun f : ℂ →ₐ[ℝ] ℂ => f (e x)) h
      simp only [AlgEquiv.coe_toAlgHom] at this
      rw [hτ', AlgEquiv.symm_apply_apply] at this
      exact this
    have h1 : e x * (starRingEnd ℂ) (e x) = (r : ℂ) := by
      rw [← hconj, ← map_mul, hx, AlgEquiv.commutes, Complex.coe_algebraMap]
    rw [Complex.mul_conj'] at h1
    have h2 : ‖e x‖ ^ 2 = r := by exact_mod_cast h1
    nlinarith [sq_nonneg ‖e x‖]

/-! ### The class is not locally trivial at the real place -/

lemma exists_moves_sqrtNegOne :
    ∃ τ : AbsoluteGaloisGroup ℝ, τ (embInf () sqrtNegOne) ≠ embInf () sqrtNegOne := by
  by_contra hcon
  push Not at hcon
  obtain ⟨r, hr⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed
    (embInf () sqrtNegOne)).mpr hcon
  have h : algebraMap ℝ (SeparableClosure ℝ) (r ^ 2) = algebraMap ℝ (SeparableClosure ℝ) (-1) := by
    rw [map_pow, hr, ← map_pow, sqrtNegOne_sq, map_neg, map_one, map_neg, map_one]
  have hr2 : r ^ 2 = -1 := (algebraMap ℝ (SeparableClosure ℝ)).injective h
  nlinarith [sq_nonneg r]

/-- **The class `c` is not in `Sel₂(E_ℓ/ℚ)` (main's `selmerAt`)**: its image in
`H¹(G_ℝ, E_ℓ(ℝˢ))` is not zero. -/
theorem cls_not_mem_selmerAt (hℓ : ℓ ≠ 0) : cls hℓ ∉ selmerAt (curve ℓ) 1 := by
  intro hmem
  have hInf := (AddSubgroup.mem_inf.mp hmem).2
  rw [WeierstrassCurve.mem_selmerGroup_iff, WeierstrassCurve.mem_shafarevichTateGroup_iff] at hInf
  have h0 := hInf ()
  rw [cls, H1pi, QuotientAddGroup.mk'_apply, explicitCoeff1_mk, pointRes_eq_explicitMap1,
    explicitMap1_mk, H1pi_eq_zero_iff, mem_B1_iff] at h0
  obtain ⟨R, hR⟩ := h0
  obtain ⟨τ₀, hτ₀⟩ := exists_moves_sqrtNegOne
  have hφ : absoluteGaloisGroupMap (embInf ()) τ₀ sqrtNegOne ≠ sqrtNegOne := by
    intro h
    apply hτ₀
    rw [← absoluteGaloisGroupMap_commutes, h]
  have hR0 := hR τ₀
  rw [cocyclesMap1_apply] at hR0
  erw [cocyclesMap1_apply] at hR0
  have hRτ : τ₀ • R - R = (curve ℓ).pointCoeffBaseChange (embInf ())
      ((T0c hℓ : (curve ℓ).TorsionCoeff (2 ^ 1)) : (curve ℓ).PointCoeff) := by
    rw [hR0]
    have hc : cocyc hℓ (absoluteGaloisGroupMap (embInf ()) τ₀) = T0c hℓ := by
      simp only [cocyc, hφ, ↓reduceIte]
    have : ((curve ℓ).torsionCoeffIncl (2 ^ 1) :
          (curve ℓ).TorsionCoeff (2 ^ 1) →+ (curve ℓ).PointCoeff)
        (((⟨cocyc hℓ, cocyc_mem_Z1 hℓ⟩ :
            Z1 (AbsoluteGaloisGroup ℚ) ((curve ℓ).TorsionCoeff (2 ^ 1))) :
            AbsoluteGaloisGroup ℚ → (curve ℓ).TorsionCoeff (2 ^ 1))
          ((ContinuousMonoidHom.id (AbsoluteGaloisGroup ℚ)) ((absoluteGaloisGroupMap (embInf ())) τ₀))) =
          ((T0c hℓ : (curve ℓ).TorsionCoeff (2 ^ 1)) : (curve ℓ).PointCoeff) := by
      rw [← hc]; rfl
    exact congrArg _ this
  have hB : ((T0c hℓ : (curve ℓ).TorsionCoeff (2 ^ 1)) : (curve ℓ).PointCoeff) =
      (curve ℓ).basePointCoeff (T0 hℓ) := (curve ℓ).coe_baseTorsionCoeff _
  rw [hB, pointCoeffBaseChange_basePointCoeff] at hRτ
  obtain ⟨R', rfl⟩ := ((curve ℓ)⁄(RealCompletion ())).pointCoeffEquiv.surjective R
  have h2 := congrArg ((curve ℓ)⁄(RealCompletion ())).pointCoeffEquiv.symm hRτ
  rw [map_sub, pointCoeffEquiv_symm_smul, AddEquiv.symm_apply_apply] at h2
  rw [T0, Affine.pointMap_some, basePointCoeff_some, AddEquiv.symm_apply_apply] at h2
  have hx0 : (algebraMap (RealCompletion ()) (SeparableClosure (RealCompletion ())))
      ((algebraMap ℚ (RealCompletion ())) 0) = 0 := by simp
  simp only [hx0] at h2
  rw [sub_eq_iff_eq_add] at h2
  set L : SeparableClosure (RealCompletion ()) :=
    algebraMap (RealCompletion ()) (SeparableClosure (RealCompletion ()))
      (algebraMap ℚ (RealCompletion ()) ℓ) with hL
  have ha₁ : (((curve ℓ)⁄(RealCompletion ()))⁄(SeparableClosure (RealCompletion ()))).a₁ = 0 := by
    simp [curve]
  have ha₂ : (((curve ℓ)⁄(RealCompletion ()))⁄(SeparableClosure (RealCompletion ()))).a₂ =
      2 * L := by
    show algebraMap (RealCompletion ()) (SeparableClosure (RealCompletion ()))
      (algebraMap ℚ (RealCompletion ()) (2 * ℓ)) = 2 * L
    rw [hL, map_mul, map_mul, map_ofNat, map_ofNat]
  have ha₃ : (((curve ℓ)⁄(RealCompletion ()))⁄(SeparableClosure (RealCompletion ()))).a₃ = 0 := by
    simp [curve]
  have ha₄ : (((curve ℓ)⁄(RealCompletion ()))⁄(SeparableClosure (RealCompletion ()))).a₄ =
      -3 * L ^ 2 := by
    show algebraMap (RealCompletion ()) (SeparableClosure (RealCompletion ()))
      (algebraMap ℚ (RealCompletion ()) (-3 * ℓ ^ 2)) = -3 * L ^ 2
    rw [hL, map_mul, map_mul, map_neg, map_neg, map_ofNat, map_ofNat, map_pow, map_pow]
  have ha₆ : (((curve ℓ)⁄(RealCompletion ()))⁄(SeparableClosure (RealCompletion ()))).a₆ = 0 := by
    simp [curve]
  have hr : algebraMap ℚ (RealCompletion ()) (-3 * ℓ ^ 2) < 0 := by
    have hℓr : algebraMap ℚ (RealCompletion ()) ℓ ≠ 0 := (map_ne_zero _).mpr hℓ
    rw [map_mul, map_neg, map_pow, map_ofNat]
    have := sq_pos_of_ne_zero hℓr
    linarith
  rcases R' with _ | ⟨x, y, hxy⟩
  · change Affine.Point.zero = Affine.Point.some _ _ _ at h2
    cases h2
  · rw [Affine.Point.map_some] at h2
    have heq := (Affine.equation_iff _ _).mp hxy.1
    rw [ha₁, ha₂, ha₃, ha₄, ha₆] at heq
    by_cases hx : x = 0
    · subst hx
      have hy : y = 0 := by
        have : y ^ 2 = 0 := by linear_combination heq
        exact pow_eq_zero_iff two_ne_zero |>.mp this
      subst hy
      have hnegY : (0 : SeparableClosure (RealCompletion ())) =
          (((curve ℓ)⁄(RealCompletion ()))⁄(SeparableClosure (RealCompletion ()))).toAffine.negY 0 0 := by
        rw [Affine.negY, show (((curve ℓ)⁄(RealCompletion ()))⁄
          (SeparableClosure (RealCompletion ()))).toAffine.a₃ = 0 from ha₃]
        ring
      rw [Affine.Point.add_of_Y_eq rfl hnegY] at h2
      cases h2
    · rw [Affine.Point.add_of_X_ne (Ne.symm hx), Affine.Point.some.injEq] at h2
      obtain ⟨hτx, -⟩ := h2
      rw [Affine.slope_of_X_ne (Ne.symm hx)] at hτx
      simp only [Affine.addX, ha₁, ha₂] at hτx
      have hτx' : τ₀ x = ((0 - y) / (0 - x)) ^ 2 + 0 * ((0 - y) / (0 - x)) - 2 * L - 0 - x := hτx
      have hy2 : y ^ 2 = x ^ 3 + 2 * L * x ^ 2 - 3 * L ^ 2 * x := by linear_combination heq
      have key : x * τ₀ x = -3 * L ^ 2 := by
        rw [hτx', zero_sub, zero_sub, neg_div_neg_eq, div_pow]
        field_simp
        linear_combination hy2
      apply mul_gal_ne_neg τ₀ hτ₀ x hr
      rw [key, ← ha₄]
      rfl

/-- **The image of `c` in `H¹(G_ℚ, E_ℓ[2^∞])` is not in `Sel_{2^∞}(E_ℓ/ℚ)`** (main's
`selmerTwoPower`): membership is read off the image in `H¹(G_ℚ, E_ℓ(ℚˢ))`, which is the same as
for `c`. So `selmerTwoPower (curve ℓ) ≠ ⊤`. -/
theorem cls_twoPower_not_mem_selmerTwoPower (hℓ : ℓ ≠ 0) :
    explicitCoeff1 (AbsoluteGaloisGroup ℚ) ((curve ℓ).TorsionCoeff (2 ^ 1))
      (torsionToTwoPower (curve ℓ) 1) continuous_of_discreteTopology (cls hℓ) ∉
        selmerTwoPower (curve ℓ) := by
  intro hmem
  apply cls_not_mem_selmerAt hℓ
  have hcomp : explicitCoeff1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff (curve ℓ))
      (twoPowerCoeffIncl (curve ℓ)) continuous_of_discreteTopology
      (explicitCoeff1 (AbsoluteGaloisGroup ℚ) ((curve ℓ).TorsionCoeff (2 ^ 1))
        (torsionToTwoPower (curve ℓ) 1) continuous_of_discreteTopology (cls hℓ)) =
      explicitCoeff1 (AbsoluteGaloisGroup ℚ) ((curve ℓ).TorsionCoeff (2 ^ 1))
        ((curve ℓ).torsionCoeffIncl (2 ^ 1)) continuous_of_discreteTopology (cls hℓ) := by
    rw [← twoPowerCoeffIncl_comp_torsionToTwoPower, explicitCoeff1_comp]
    rfl
  rw [selmerTwoPower, AddSubgroup.mem_comap, hcomp, sha] at hmem
  obtain ⟨h1, h2⟩ := AddSubgroup.mem_inf.mp hmem
  exact AddSubgroup.mem_inf.mpr ⟨(WeierstrassCurve.mem_selmerGroup_iff _ _ _).mpr h1,
    (WeierstrassCurve.mem_selmerGroup_iff _ _ _).mpr h2⟩


/-! ### A nonzero Selmer class -/


/-- **`(0, 0) ∉ 2 E_ℓ(ℚ)`**: `x(2Q) = 0` forces `(x(Q)² + 3ℓ²)² = 0`, impossible over `ℚ`. -/
theorem two_nsmul_ne_zeroPt {ℓ : ℚ} (hℓ : ℓ ≠ 0) (Q : (curve ℓ).toAffine.Point) :
    (2 : ℕ) • Q ≠ .some 0 0 (curve_nonsingular_zero hℓ) := by
  intro hQ
  rw [two_nsmul] at hQ
  rcases Q with _ | ⟨x, y, h⟩
  · change (0 : (curve ℓ).toAffine.Point) + 0 = _ at hQ
    rw [zero_add] at hQ
    cases hQ
  · by_cases hy : y = (curve ℓ).toAffine.negY x y
    · rw [Affine.Point.add_self_of_Y_eq hy] at hQ
      cases hQ
    · rw [Affine.Point.add_self_of_Y_ne hy, Affine.Point.some.injEq] at hQ
      obtain ⟨hx, -⟩ := hQ
      have hneg : (curve ℓ).toAffine.negY x y = -y := by simp [Affine.negY, curve]
      have hy0 : y ≠ 0 := fun h0 => hy (by rw [hneg, h0, neg_zero])
      have heq : y ^ 2 = x ^ 3 + 2 * ℓ * x ^ 2 - 3 * ℓ ^ 2 * x := by
        have := (Affine.equation_iff _ _).mp h.1
        simp only [curve] at this
        linear_combination this
      rw [Affine.slope_of_Y_ne rfl hy, hneg] at hx
      simp only [Affine.addX, curve] at hx
      have h2y : y - -y ≠ 0 := by
        intro h2; apply hy0; linarith
      have key : (3 * x ^ 2 + 2 * (2 * ℓ) * x + -3 * ℓ ^ 2 - 0 * y) ^ 2 =
          (2 * ℓ + 2 * x) * (y - -y) ^ 2 := by
        field_simp at hx
        linear_combination hx
      have hsq : (x ^ 2 + 3 * ℓ ^ 2) ^ 2 = 0 := by
        linear_combination key + 4 * (2 * ℓ + 2 * x) * heq
      have h3 : x ^ 2 + 3 * ℓ ^ 2 = 0 := pow_eq_zero_iff two_ne_zero |>.mp hsq
      have hl : 0 < ℓ ^ 2 := by positivity
      nlinarith [sq_nonneg x]

/-- **Main's `Sel₂(E_ℓ/ℚ)` is not zero**: the Kummer class of `(0, 0)` is a nonzero element. -/
theorem selmerAt_curve_exists_ne_zero {ℓ : ℚ} (hℓ : ℓ ≠ 0) :
    ∃ c ∈ selmerAt (curve ℓ) 1, c ≠ 0 := by
  have := curve_isElliptic' hℓ
  have hm : IsUnit (((2 ^ 1 : ℕ)) : ℚ) := by norm_num
  refine ⟨(curve ℓ).kummerMap (2 ^ 1) hm (.some 0 0 (curve_nonsingular_zero hℓ)), ?_, ?_⟩
  · exact AddSubgroup.mem_inf.mpr ⟨(curve ℓ).kummerMap_mem_selmerGroup embFin hm _,
      (curve ℓ).kummerMap_mem_selmerGroup embInf hm _⟩
  · intro h0
    obtain ⟨Q, hQ⟩ := (WeierstrassCurve.kummerMap_eq_zero_iff hm).mp h0
    exact two_nsmul_ne_zeroPt hℓ Q (by simpa using hQ)

end ZInQ.Manuscript.SelmerTwoPower.NonVacuity

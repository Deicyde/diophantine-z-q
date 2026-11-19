import ZInQKernel.Contrib.CloudB3RC53.NewformS13.CuspPlace

/-!
# The map from the modular function field to `A` on function fields

Translation S3 at the level of function fields: a nonconstant point `(x, y)` of `A` with
coordinates in `F = ℚ(j, j_M)` is a `ℚ`-embedding of the function field `ℚ(A)` into `F` (the
function-field form of a nonconstant map `X₀(M) → A`), and the invariant differential
`ω_A = dX/(2Y + a₁X + a₃)` of `ℚ(A)` pulls back to the differential `omegaPull` of
`QExpDifferential.lean`, whose `q`-expansion is `θx · (2y + a₁x + a₃)⁻¹`.

* `transcendental_of_nonconst`: a Laurent series with a nonzero coefficient away from `q⁰` is
  transcendental over `ℚ` (the `q`-adic valuations of the terms of a polynomial in
  `y = x − x₀` are pairwise distinct);
* `pointAlgHom_injective`: for nonconstant `x` the coordinate-ring map `ℚ[A] → F` is injective
  (`r = p + qY` maps to `0` only if the norm `p² − pq(a₁X + a₃) − q²(X³ + ⋯)` vanishes at `x`);
* **`pointFieldHom`**: the `ℚ`-algebra map `ℚ(A) → F` extending it;
* **`pullbackFF_omegaA`**: the pull-back of `ω_A ∈ Ω[ℚ(A)⁄ℚ]` along `pointFieldHom` is `omegaPull`;
  **`qExpDiff_pullbackFF_omegaA`**: its `q`-expansion is `θx · (2y + a₁x + a₃)⁻¹`;
* `modularPointFieldHom`, **`pullbackIsMultiple_iff_functionField`**: for the peer's
  `IsModularPointQ M A x y`, the field map `ℚ(A) → ℚ(j, j_M)`, and clause (iv)
  `PullbackIsMultiple A x y ĝ c` is the statement that the `q`-expansion of the pull-back of
  `ω_A` along it is `c · ĝ`.

All statements are definitions or PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.NewformS13

open ZInQ.Contrib.RC53Assist.NewformPeriods
open scoped WithZero
open Polynomial

/-! ### Nonconstant Laurent series are transcendental -/

theorem valued_lt_one_of_constantCoeff (F : PowerSeries ℚ) (h0 : PowerSeries.constantCoeff F = 0) :
    Valued.v (HahnSeries.ofPowerSeries ℤ ℚ F) < 1 := by
  obtain ⟨G, hG⟩ := PowerSeries.X_dvd_iff.2 h0
  have hG1 : Valued.v (HahnSeries.ofPowerSeries ℤ ℚ G) ≤ 1 :=
    (LaurentSeries.val_le_one_iff_eq_coe ℚ _).2 ⟨G, rfl⟩
  have hv : Valued.v (HahnSeries.ofPowerSeries ℤ ℚ F) =
      Valued.v (((PowerSeries.X : PowerSeries ℚ) : LaurentSeries ℚ) ^ 1) *
        Valued.v (HahnSeries.ofPowerSeries ℤ ℚ G) := by
    rw [hG, pow_one, map_mul, map_mul]
  rw [hv, LaurentSeries.valuation_X_pow]
  calc WithZero.exp (-((1 : ℕ) : ℤ)) * Valued.v (HahnSeries.ofPowerSeries ℤ ℚ G)
      ≤ WithZero.exp (-((1 : ℕ) : ℤ)) * 1 := by gcongr
    _ < 1 := by
      rw [mul_one, ← WithZero.exp_zero, WithZero.exp_lt_exp]
      norm_num

theorem valued_algebraMap (a : ℚ) (ha : a ≠ 0) :
    Valued.v (algebraMap ℚ (LaurentSeries ℚ) a) = 1 := by
  have h1 : Valued.v (algebraMap ℚ (LaurentSeries ℚ) a) ≤ 1 :=
    (LaurentSeries.val_le_one_iff_eq_coe ℚ _).2 ⟨PowerSeries.C a, by simp⟩
  have h2 : Valued.v (algebraMap ℚ (LaurentSeries ℚ) a⁻¹) ≤ 1 :=
    (LaurentSeries.val_le_one_iff_eq_coe ℚ _).2 ⟨PowerSeries.C a⁻¹, by simp⟩
  have hm : Valued.v (algebraMap ℚ (LaurentSeries ℚ) a) *
      Valued.v (algebraMap ℚ (LaurentSeries ℚ) a⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ ha, map_one, map_one]
  refine le_antisymm h1 ?_
  by_contra hlt
  push_neg at hlt
  have : Valued.v (algebraMap ℚ (LaurentSeries ℚ) a) *
      Valued.v (algebraMap ℚ (LaurentSeries ℚ) a⁻¹) < 1 :=
    calc _ ≤ Valued.v (algebraMap ℚ (LaurentSeries ℚ) a) * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact hlt
  exact (ne_of_lt this) hm

/-- A nonzero polynomial does not vanish at an element of valuation `≠ 0, 1`. -/
theorem aeval_ne_zero_of_valued_ne_one {y : LaurentSeries ℚ} (hy0 : Valued.v y ≠ 0)
    (hy1 : Valued.v y ≠ 1) {P : ℚ[X]} (hP : P ≠ 0) : aeval y P ≠ 0 := by
  classical
  set t : ℕ → LaurentSeries ℚ := fun i => algebraMap ℚ (LaurentSeries ℚ) (P.coeff i) * y ^ i
    with ht
  have hterm : ∀ i, P.coeff i ≠ 0 → Valued.v (t i) = Valued.v y ^ i := fun i hi => by
    rw [ht, map_mul, valued_algebraMap _ hi, one_mul, map_pow]
  have hterm0 : ∀ i, P.coeff i = 0 → Valued.v (t i) = 0 := fun i hi => by
    rw [ht]
    simp only [hi, map_zero, zero_mul]
  have hsumeq : aeval y P = ∑ i ∈ Finset.range (P.natDegree + 1), t i := by
    rw [aeval_eq_sum_range]
    exact Finset.sum_congr rfl fun i _ => Algebra.smul_def _ _
  set j := if Valued.v y < 1 then P.natTrailingDegree else P.natDegree with hj
  have hjc : P.coeff j ≠ 0 := by
    rw [hj]
    split_ifs
    · exact mt Polynomial.trailingCoeff_eq_zero.1 hP
    · exact mt Polynomial.leadingCoeff_eq_zero.1 hP
  have hjr : j ∈ Finset.range (P.natDegree + 1) := by
    rw [Finset.mem_range, Nat.lt_succ_iff, hj]
    split_ifs
    · exact Polynomial.natTrailingDegree_le_natDegree P
    · exact le_rfl
  have hvj : Valued.v (t j) ≠ 0 := by
    rw [hterm j hjc]
    exact pow_ne_zero _ hy0
  intro h0
  have hsum := (Valued.v : Valuation (LaurentSeries ℚ) ℤᵐ⁰).map_sum_eq_of_lt
    (f := t) hjr (fun i hi => ?_)
  · rw [← hsumeq, h0, map_zero] at hsum
    exact hvj hsum.symm
  · rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
    by_cases hci : P.coeff i = 0
    · rw [hterm0 i hci]
      exact lt_of_le_of_ne zero_le' (Ne.symm hvj)
    · rw [hterm i hci, hterm j hjc]
      have hy0' : 0 < Valued.v y := lt_of_le_of_ne zero_le' (Ne.symm hy0)
      by_cases hlt : Valued.v y < 1
      · have hji : j < i := by
          have hle : j ≤ i := by
            rw [hj, if_pos hlt]
            exact Polynomial.natTrailingDegree_le_of_ne_zero hci
          exact lt_of_le_of_ne hle (Ne.symm hi.2)
        exact pow_lt_pow_right_of_lt_one₀ hy0' hlt hji
      · have hgt : 1 < Valued.v y := lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hy1)
        have hij : i < j := by
          have hle : i ≤ j := by
            rw [hj, if_neg hlt]
            exact Polynomial.le_natDegree_of_ne_zero hci
          exact lt_of_le_of_ne hle hi.2
        exact pow_lt_pow_right₀ hgt hij

/-- **A Laurent series with a nonzero coefficient away from `q⁰` is transcendental over `ℚ`.** -/
theorem transcendental_of_nonconst {x : LaurentSeries ℚ} (hx : ∃ n : ℤ, n ≠ 0 ∧ x.coeff n ≠ 0) :
    Transcendental ℚ x := by
  obtain ⟨n, hn0, hxn⟩ := hx
  set c := x.coeff 0
  set y := x - algebraMap ℚ (LaurentSeries ℚ) c with hy
  have hyc0 : y.coeff 0 = 0 := by
    rw [hy, HahnSeries.coeff_sub, show algebraMap ℚ (LaurentSeries ℚ) c = HahnSeries.C c by simp,
      HahnSeries.C_apply, HahnSeries.coeff_single_same, sub_self]
  have hyn : y.coeff n ≠ 0 := by
    rw [hy, HahnSeries.coeff_sub, show algebraMap ℚ (LaurentSeries ℚ) c = HahnSeries.C c by simp,
      HahnSeries.C_apply, HahnSeries.coeff_single_of_ne hn0, sub_zero]
    exact hxn
  have hy0 : y ≠ 0 := fun h => hyn (by rw [h, HahnSeries.coeff_zero])
  have hv0 : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy0
  have hv1 : Valued.v y ≠ 1 := by
    intro h1
    obtain ⟨Y, hY⟩ := (LaurentSeries.val_le_one_iff_eq_coe ℚ y).1 h1.le
    have hY0 : PowerSeries.constantCoeff Y = 0 := by
      have := congrArg (fun z : LaurentSeries ℚ => z.coeff ((0 : ℕ) : ℤ)) hY
      simp only [HahnSeries.ofPowerSeries_apply_coeff] at this
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
      rw [this]
      exact hyc0
    have := valued_lt_one_of_constantCoeff Y hY0
    rw [hY, h1] at this
    exact lt_irrefl _ this
  rintro ⟨P, hP, hPx⟩
  have hP' : P.comp (X + C c) ≠ 0 := by
    intro h
    have := congrArg (fun Q => Q.comp (X - C c)) h
    simp only [Polynomial.comp_assoc, Polynomial.zero_comp] at this
    rw [show ((X + C c : ℚ[X])).comp (X - C c) = (X : ℚ[X]) by simp, Polynomial.comp_X] at this
    exact hP this
  apply aeval_ne_zero_of_valued_ne_one hv0 hv1 hP'
  rw [Polynomial.aeval_comp]
  simp only [map_add, aeval_X, aeval_C, hy, sub_add_cancel]
  exact hPx

/-! ### The coordinate-ring map is injective -/

section Injective

variable {M : ℕ} [NeZero M] {A : WeierstrassCurve ℚ}

theorem pointAlgHom_smul_basis {x y : FQ M} (h : OnCurve M A x y) (p q : ℚ[X]) :
    pointAlgHom h (p • (1 : A.toAffine.CoordinateRing) +
        q • WeierstrassCurve.Affine.CoordinateRing.mk A.toAffine Polynomial.X) =
      aeval x p + aeval x q * y := by
  rw [map_add, Algebra.smul_def, Algebra.smul_def, mul_one, map_mul]
  have h1 : ∀ r : ℚ[X], pointAlgHom h (algebraMap ℚ[X] A.toAffine.CoordinateRing r) = aeval x r :=
    fun r => by
      change (AdjoinRoot.lift (Polynomial.aeval x).toRingHom y (eval_polynomial h))
        (AdjoinRoot.of _ r) = _
      rw [AdjoinRoot.lift_of]
      rfl
  have h2 : pointAlgHom h (WeierstrassCurve.Affine.CoordinateRing.mk A.toAffine Polynomial.X) = y :=
    pointAlgHom_Y h
  rw [h1, h1, h2]

theorem aeval_norm_eq {x y : FQ M} (h : OnCurve M A x y) (p q : ℚ[X]) :
    aeval x (Algebra.norm ℚ[X] (p • (1 : A.toAffine.CoordinateRing) +
        q • WeierstrassCurve.Affine.CoordinateRing.mk A.toAffine Polynomial.X)) =
      (aeval x p + aeval x q * y) *
        (aeval x p + aeval x q *
          (-y - algebraMap ℚ (FQ M) A.a₁ * x - algebraMap ℚ (FQ M) A.a₃)) := by
  rw [WeierstrassCurve.Affine.CoordinateRing.norm_smul_basis]
  simp only [map_sub, map_mul, map_pow, map_add, aeval_X, aeval_C]
  simp only [OnCurve] at h
  linear_combination (aeval x q) ^ 2 * h

/-- **For nonconstant `x`, the coordinate-ring map `ℚ[A] → F` is injective.** -/
theorem pointAlgHom_injective {x y : FQ M} (h : OnCurve M A x y)
    (hx : ∃ n : ℤ, n ≠ 0 ∧ (x : LaurentSeries ℚ).coeff n ≠ 0) :
    Function.Injective (pointAlgHom h) := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  obtain ⟨p, q, rfl⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq r
  have hN : aeval x (Algebra.norm ℚ[X] (p • (1 : A.toAffine.CoordinateRing) +
      q • WeierstrassCurve.Affine.CoordinateRing.mk A.toAffine Polynomial.X)) = 0 := by
    rw [aeval_norm_eq h, ← pointAlgHom_smul_basis h, hr, zero_mul]
  have hT := transcendental_of_nonconst hx
  have hN0 : Algebra.norm ℚ[X] (p • (1 : A.toAffine.CoordinateRing) +
      q • WeierstrassCurve.Affine.CoordinateRing.mk A.toAffine Polynomial.X) = 0 := by
    by_contra hne
    apply hT
    refine ⟨_, hne, ?_⟩
    have := congrArg (fun z : FQ M => (z : LaurentSeries ℚ)) hN
    simp only [IntermediateField.coe_zero] at this
    rw [← this, Polynomial.aeval_def, Polynomial.aeval_def]
    have key := Polynomial.hom_eval₂ (Algebra.norm ℚ[X] (p • (1 : A.toAffine.CoordinateRing) +
        q • WeierstrassCurve.Affine.CoordinateRing.mk A.toAffine Polynomial.X))
      (algebraMap ℚ (FQ M)) (algebraMap (FQ M) (LaurentSeries ℚ)) x
    rw [show (algebraMap (FQ M) (LaurentSeries ℚ)).comp (algebraMap ℚ (FQ M)) =
      algebraMap ℚ (LaurentSeries ℚ) from RingHom.ext_rat _ _] at key
    exact key.symm
  have hdeg := WeierstrassCurve.Affine.CoordinateRing.degree_norm_smul_basis (W' := A.toAffine) p q
  rw [hN0, Polynomial.degree_zero] at hdeg
  have hp : p = 0 := by
    by_contra hp0
    have h1 : 2 • p.degree ≤ ⊥ := hdeg ▸ le_max_left _ _
    rw [le_bot_iff, Polynomial.degree_eq_natDegree hp0] at h1
    have e : (2 • (p.natDegree : WithBot ℕ)) = ((2 * p.natDegree : ℕ) : WithBot ℕ) := by
      rw [nsmul_eq_mul]; push_cast; rfl
    rw [e] at h1
    exact WithBot.natCast_ne_bot _ h1
  have hq : q = 0 := by
    by_contra hq0
    have h1 : 2 • q.degree + 3 ≤ ⊥ := hdeg ▸ le_max_right _ _
    rw [le_bot_iff, Polynomial.degree_eq_natDegree hq0] at h1
    have e : (2 • (q.natDegree : WithBot ℕ)) + 3 = ((2 * q.natDegree + 3 : ℕ) : WithBot ℕ) := by
      rw [nsmul_eq_mul]; push_cast; rfl
    rw [e] at h1
    exact WithBot.natCast_ne_bot _ h1
  rw [hp, hq, zero_smul, zero_smul, add_zero]

end Injective

/-! ### The map on function fields and the pull-back of `ω_A` -/

section FunctionField

variable {M : ℕ} [NeZero M] {A : WeierstrassCurve ℚ}

/-- **A nonconstant point of `A` over `F` is a field embedding `ℚ(A) → F`** (the function-field
form of the nonconstant map `X₀(M) → A`), extending `pointAlgHom`. -/
def pointFieldHom {x y : FQ M} (h : OnCurve M A x y)
    (hx : ∃ n : ℤ, n ≠ 0 ∧ (x : LaurentSeries ℚ).coeff n ≠ 0) :
    A.toAffine.FunctionField →+* FQ M :=
  IsFractionRing.lift (pointAlgHom_injective h hx)

theorem pointFieldHom_algebraMap {x y : FQ M} (h : OnCurve M A x y)
    (hx : ∃ n : ℤ, n ≠ 0 ∧ (x : LaurentSeries ℚ).coeff n ≠ 0) (r : A.toAffine.CoordinateRing) :
    pointFieldHom h hx (algebraMap _ A.toAffine.FunctionField r) = pointAlgHom h r :=
  IsFractionRing.lift_algebraMap _ r

/-- The pull-back of differentials along a field map `ψ : ℚ(A) → F`. -/
def pullbackFF (ψ : A.toAffine.FunctionField →+* FQ M) :
    Ω[A.toAffine.FunctionField⁄ℚ] →ₗ[ℚ] Ω[FQ M⁄ℚ] :=
  letI : Algebra A.toAffine.FunctionField (FQ M) := ψ.toAlgebra
  haveI : IsScalarTower ℚ A.toAffine.FunctionField (FQ M) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      rw [eq_ratCast (algebraMap ℚ (FQ M)) r, eq_ratCast (algebraMap ℚ A.toAffine.FunctionField) r,
        RingHom.algebraMap_toAlgebra, map_ratCast]
  (KaehlerDifferential.map ℚ ℚ A.toAffine.FunctionField (FQ M)).restrictScalars ℚ

theorem pullbackFF_D (ψ : A.toAffine.FunctionField →+* FQ M) (f : A.toAffine.FunctionField) :
    pullbackFF ψ (KaehlerDifferential.D ℚ _ f) = KaehlerDifferential.D ℚ (FQ M) (ψ f) := by
  let _ : Algebra A.toAffine.FunctionField (FQ M) := ψ.toAlgebra
  have : IsScalarTower ℚ A.toAffine.FunctionField (FQ M) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      rw [eq_ratCast (algebraMap ℚ (FQ M)) r, eq_ratCast (algebraMap ℚ A.toAffine.FunctionField) r,
        RingHom.algebraMap_toAlgebra, map_ratCast]
  exact KaehlerDifferential.map_D ℚ ℚ A.toAffine.FunctionField (FQ M) f

theorem pullbackFF_smul (ψ : A.toAffine.FunctionField →+* FQ M) (a : A.toAffine.FunctionField)
    (ω : Ω[A.toAffine.FunctionField⁄ℚ]) : pullbackFF ψ (a • ω) = ψ a • pullbackFF ψ ω := by
  let _ : Algebra A.toAffine.FunctionField (FQ M) := ψ.toAlgebra
  have : IsScalarTower ℚ A.toAffine.FunctionField (FQ M) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      rw [eq_ratCast (algebraMap ℚ (FQ M)) r, eq_ratCast (algebraMap ℚ A.toAffine.FunctionField) r,
        RingHom.algebraMap_toAlgebra, map_ratCast]
  change KaehlerDifferential.map ℚ ℚ A.toAffine.FunctionField (FQ M) (a • ω) = _
  rw [LinearMap.map_smul, ← algebraMap_smul (FQ M) a]
  rfl

/-- The coordinate functions `X`, `Y` of `ℚ(A)`. -/
abbrev fX (A : WeierstrassCurve ℚ) : A.toAffine.FunctionField :=
  algebraMap _ _ (WeierstrassCurve.Affine.CoordinateRing.mk A.toAffine (Polynomial.C Polynomial.X))

abbrev fY (A : WeierstrassCurve ℚ) : A.toAffine.FunctionField :=
  algebraMap _ _ (WeierstrassCurve.Affine.CoordinateRing.mk A.toAffine Polynomial.X)

/-- **The invariant differential of `A`** in `Ω[ℚ(A)⁄ℚ]`: `ω_A = dX/(2Y + a₁X + a₃)`. -/
def omegaA (A : WeierstrassCurve ℚ) : Ω[A.toAffine.FunctionField⁄ℚ] :=
  ((fY A + fY A) + algebraMap ℚ _ A.a₁ * fX A + algebraMap ℚ _ A.a₃)⁻¹ •
    KaehlerDifferential.D ℚ _ (fX A)

/-- **The pull-back of `ω_A` along the function-field map of a nonconstant point is
`omegaPull`.** -/
theorem pullbackFF_omegaA {x y : FQ M} (h : OnCurve M A x y)
    (hx : ∃ n : ℤ, n ≠ 0 ∧ (x : LaurentSeries ℚ).coeff n ≠ 0) :
    pullbackFF (pointFieldHom h hx) (omegaA A) = omegaPull A x y := by
  have hX : pointFieldHom h hx (fX A) = x := by
    rw [pointFieldHom_algebraMap]
    exact pointAlgHom_X h
  have hY : pointFieldHom h hx (fY A) = y := by
    rw [pointFieldHom_algebraMap]
    exact pointAlgHom_Y h
  have hq : ∀ a : ℚ, pointFieldHom h hx (algebraMap ℚ A.toAffine.FunctionField a) =
      algebraMap ℚ (FQ M) a := fun a => by
    rw [eq_ratCast (algebraMap ℚ A.toAffine.FunctionField), eq_ratCast (algebraMap ℚ (FQ M)),
      map_ratCast]
  rw [omegaA, pullbackFF_smul, pullbackFF_D, map_inv₀, map_add, map_add, map_add, map_mul,
    hX, hY, hq, hq]
  rfl

/-- **The `q`-expansion of the pulled-back invariant differential of `A`** along the function-field
map of a nonconstant point: `θx · (2y + a₁x + a₃)⁻¹`. -/
theorem qExpDiff_pullbackFF_omegaA {x y : FQ M} (h : OnCurve M A x y)
    (hx : ∃ n : ℤ, n ≠ 0 ∧ (x : LaurentSeries ℚ).coeff n ≠ 0) :
    qExpDiff M (pullbackFF (pointFieldHom h hx) (omegaA A)) =
      ((denomF A x y : LaurentSeries ℚ))⁻¹ * eulerOp (x : LaurentSeries ℚ) := by
  rw [pullbackFF_omegaA, qExpDiff_omegaPull]

end FunctionField

/-! ### From the peer's `IsModularPointQ` -/

section Modular

variable {M : ℕ} [NeZero M] {A : WeierstrassCurve ℚ}

theorem onCurve_of_isModularPointQ {x y : LaurentSeries ℚ} (h : IsModularPointQ M A x y) :
    OnCurve M A ⟨x, h.1⟩ ⟨y, h.2.1⟩ := by
  apply Subtype.ext
  simp only [IntermediateField.coe_add, IntermediateField.coe_mul, IntermediateField.coe_pow]
  have e : ∀ a : ℚ, ((algebraMap ℚ (FQ M) a : FQ M) : LaurentSeries ℚ) = cQ a := fun a => by
    rw [cQ, eq_ratCast (algebraMap ℚ (FQ M)), eq_ratCast (algebraMap ℚ (LaurentSeries ℚ))]
    rfl
  simp only [e]
  exact h.2.2.1

/-- **The function-field map of a modular point** (`IsModularPointQ`, the peer's form of a
nonconstant `ℚ`-morphism `X₀(M) → A`): a field embedding `ℚ(A) → ℚ(j, j_M)`. -/
def modularPointFieldHom {x y : LaurentSeries ℚ} (h : IsModularPointQ M A x y) :
    A.toAffine.FunctionField →+* FQ M :=
  pointFieldHom (onCurve_of_isModularPointQ h) h.2.2.2

/-- **Clause (iv) of the print is the `q`-expansion of the pull-back of `ω_A` along the
function-field map of the modular point**: for `2y + a₁x + a₃ ≠ 0`,
`PullbackIsMultiple A x y ĝ c` iff the `q`-expansion of the pull-back of `ω_A ∈ Ω[ℚ(A)⁄ℚ]` is
`c · ĝ` (times `dq/q`). -/
theorem pullbackIsMultiple_iff_functionField {x y : LaurentSeries ℚ} (h : IsModularPointQ M A x y)
    (hden : denomF A (⟨x, h.1⟩ : FQ M) ⟨y, h.2.1⟩ ≠ 0) (ĝ : PowerSeries ℂ) (c : ℂ) :
    PullbackIsMultiple A x y ĝ c ↔
      toComplexLaurent (qExpDiff M (pullbackFF (modularPointFieldHom h) (omegaA A))) =
        HahnSeries.C c * HahnSeries.ofPowerSeries ℤ ℂ ĝ := by
  rw [modularPointFieldHom, pullbackFF_omegaA]
  exact pullbackIsMultiple_iff (A := A) ⟨x, h.1⟩ ⟨y, h.2.1⟩ hden ĝ c

end Modular

end ZInQ.Contrib.CloudB3RC53.NewformS13

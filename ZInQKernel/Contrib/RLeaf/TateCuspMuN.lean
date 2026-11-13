import ZInQKernel.Contrib.RLeaf.TateCuspGlue
import ZInQKernel.Contrib.TauCeti.Backport.AlgebraicGeometry.EllipticCurve.TateCurve.Homomorphism
import ZInQKernel.Contrib.TauCeti.Backport.RingTheory.HahnSeries.Map

/-!
# t40-tate: the cusp `μ_N` of the Tate curve

Over `L' = K((t))`, `K = ℚ(ζ_N)`, the Tate curve `E_t` has the points `P(ζ^m)` (Tate's
uniformization of the roots of unity), and the coefficientwise action of `Gal(K/ℚ)` on `L'` is
continuous and commutes with the Tate coordinates, so it permutes the `x`-coordinates of the
generators of `⟨P(ζ)⟩` transitively. Transported to `E_j` over `\overline{L'}` (with `j ↦ j(E_t)`)
this gives the cusp statement `TateMuN` of task t40-igusa.
-/

noncomputable section

namespace ZInQ.RLeaf.TateCuspMuN

open MonoidWithZeroHom.ValueGroup₀ WithZeroMulInt TauCeti
open scoped WithZero
open LeafModCurves

/-! ### `K((t))` as a complete normed field -/

/-- The `t`-adic valuation of `K((t))` has rank one (normalized by `|t| = 1/2`). -/
@[reducible] def rankOneK (K : Type*) [Field K] :
    (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰).RankOne where
  hom' := (toNNReal (two_ne_zero)).comp embedding
  strictMono' := (toNNReal_strictMono one_lt_two).comp embedding_strictMono
  exists_val_nontrivial := ⟨HahnSeries.single 1 1, by
    rw [LaurentSeries.valuation_single_zpow]
    exact ⟨WithZero.exp_ne_zero, by
      rw [Ne, ← WithZero.exp_zero, WithZero.exp_inj]; omega⟩⟩

attribute [local instance] rankOneK

open scoped Valued

instance (K : Type*) [Field K] : CompleteSpace (LaurentSeries K) :=
  LaurentSeries.instLaurentSeriesComplete

theorem norm_eq (K : Type*) [Field K] (x : LaurentSeries K) :
    ‖x‖ = (toNNReal (two_ne_zero) (Valued.v x) : ℝ) := by
  rw [Valued.toNormedField.norm_def]
  show ((toNNReal _).comp embedding (Valued.v.restrict x) : ℝ) = _
  rw [MonoidWithZeroHom.comp_apply]
  congr 2
  exact embedding_restrict₀ x

/-- Two elements of `ℤᵐ⁰` with the same bounds `≤ exp (-D)` are equal. -/
theorem eq_of_forall_le_exp_iff {a b : ℤᵐ⁰}
    (h : ∀ D : ℤ, a ≤ WithZero.exp (-D) ↔ b ≤ WithZero.exp (-D)) : a = b := by
  have key : ∀ a b : ℤᵐ⁰, (∀ D : ℤ, a ≤ WithZero.exp (-D) → b ≤ WithZero.exp (-D)) → b ≤ a := by
    intro a b h
    by_cases ha : a = 0
    · subst ha
      by_contra hb
      have hb0 : b ≠ 0 := by rintro rfl; exact hb le_rfl
      have h1 := h (-(WithZero.log b) + 1) zero_le
      have h2 : WithZero.exp (WithZero.log b) ≤ WithZero.exp (-(-(WithZero.log b) + 1)) := by
        rwa [WithZero.exp_log hb0]
      rw [WithZero.exp_le_exp] at h2
      omega
    · have := h (-(WithZero.log a)) (by rw [neg_neg, WithZero.exp_log ha])
      rwa [neg_neg, WithZero.exp_log ha] at this
  exact le_antisymm (key b a fun D => (h D).mpr) (key a b fun D => (h D).mp)

/-- The coefficientwise image along an injective field map preserves the valuation. -/
theorem valuation_mapRingHom {K K' : Type*} [Field K] [Field K'] (f : K →+* K')
    (x : LaurentSeries K) :
    Valued.v (HahnSeries.mapRingHom f x : LaurentSeries K') = Valued.v x := by
  refine eq_of_forall_le_exp_iff fun D => ?_
  rw [LaurentSeries.valuation_le_iff_coeff_lt_eq_zero, LaurentSeries.valuation_le_iff_coeff_lt_eq_zero]
  refine forall_congr' fun n => imp_congr_right fun _ => ?_
  rw [HahnSeries.coeff_mapRingHom, map_eq_zero_iff f f.injective]

theorem norm_mapRingHom {K K' : Type*} [Field K] [Field K'] (f : K →+* K')
    (x : LaurentSeries K) :
    ‖(HahnSeries.mapRingHom f x : LaurentSeries K')‖ = ‖x‖ := by
  rw [norm_eq, norm_eq, valuation_mapRingHom]

instance {K K' : Type*} [Field K] [Field K'] (f : K →+* K') :
    RingHomIsometric (HahnSeries.mapRingHom f : LaurentSeries K →+* LaurentSeries K') :=
  ⟨fun {x} => norm_mapRingHom f x⟩

theorem continuous_mapRingHom {K K' : Type*} [Field K] [Field K'] (f : K →+* K') :
    Continuous (HahnSeries.mapRingHom f : LaurentSeries K →+* LaurentSeries K') :=
  AddMonoidHomClass.continuous_of_bound _ 1 fun x => by rw [one_mul, norm_mapRingHom]

/-! ### The uniformizer and the roots of unity -/

/-- The uniformizer `t` of `K((t))` as a unit. -/
def tK (K : Type*) [Field K] : (LaurentSeries K)ˣ := Units.mk0 (HahnSeries.single 1 1) (by simp)

theorem valuation_tK_zpow (K : Type*) [Field K] (k : ℤ) :
    Valued.v (((tK K ^ k : (LaurentSeries K)ˣ)) : LaurentSeries K) = WithZero.exp (-k) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀]
  change Valued.v (HahnSeries.single (1 : ℤ) (1 : K) : LaurentSeries K) ^ k = _
  rw [LaurentSeries.valuation_single_zpow, ← WithZero.exp_zsmul]
  simp

theorem norm_tK_lt_one (K : Type*) [Field K] : ‖((tK K : (LaurentSeries K)ˣ) : LaurentSeries K)‖ < 1 := by
  rw [Valued.toNormedField.norm_lt_one_iff]
  have := valuation_tK_zpow K 1
  rw [zpow_one] at this
  rw [this, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  omega

theorem mapRingHom_tK {K K' : Type*} [Field K] [Field K'] (f : K →+* K') :
    Units.map (HahnSeries.mapRingHom f : LaurentSeries K →+* LaurentSeries K').toMonoidHom (tK K) =
      tK K' := by
  ext n
  simp only [tK, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, Units.val_mk0,
    HahnSeries.coeff_mapRingHom, HahnSeries.coeff_single]
  split_ifs <;> simp

theorem valuation_C {K : Type*} [Field K] {a : K} (ha : a ≠ 0) :
    Valued.v (HahnSeries.C a : LaurentSeries K) = 1 := by
  have h1 : ∀ b : K, Valued.v (HahnSeries.C b : LaurentSeries K) ≤ 1 := fun b =>
    (LaurentSeries.val_le_one_iff_eq_coe K _).mpr ⟨PowerSeries.C b, HahnSeries.ofPowerSeries_C (Γ := ℤ) b⟩
  have h2 : Valued.v (HahnSeries.C a : LaurentSeries K) * Valued.v (HahnSeries.C a⁻¹ : LaurentSeries K) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ ha, map_one, map_one]
  refine le_antisymm (h1 a) ?_
  by_contra hlt
  push_neg at hlt
  have := mul_lt_one_of_lt_of_le hlt (h1 a⁻¹)
  rw [h2] at this
  exact lt_irrefl _ this

/-! ### Generic transport lemmas -/

/-- Points along an equality of curves. -/
def castEquiv {F : Type*} [Field F] [DecidableEq F] {W₁ W₂ : WeierstrassCurve F} (h : W₁ = W₂) :
    W₁.toAffine.Point ≃+ W₂.toAffine.Point := h ▸ AddEquiv.refl _

theorem xCoord_castEquiv {F : Type*} [Field F] [DecidableEq F] {W₁ W₂ : WeierstrassCurve F}
    (h : W₁ = W₂) (P : W₁.toAffine.Point) : xCoord (castEquiv h P) = xCoord P := by
  subst h; rfl

theorem xCoord_addEquivVariableChange {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve F) (C : WeierstrassCurve.VariableChange F)
    (P : (C • W).toAffine.Point) (hP : P ≠ 0) :
    xCoord (WeierstrassCurve.Affine.Point.addEquivVariableChange W C P) =
      (C.u : F) ^ 2 * xCoord P + C.r := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl hP
  · show xCoord (WeierstrassCurve.Affine.Point.equivVariableChange W C (.some x y h)) = _
    rw [WeierstrassCurve.Affine.Point.equivVariableChange_some]; rfl

theorem xCoord_tate {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
    [DecidableEq K] (q : Kˣ) (hq : ‖(q : K)‖ < 1) (u : Kˣ)
    (hne : tateUniformizationHom q hq (Additive.ofMul (u : Kˣ ⧸ Subgroup.zpowers q)) ≠ 0) :
    xCoord (tateUniformizationHom q hq (Additive.ofMul (u : Kˣ ⧸ Subgroup.zpowers q))) =
      tateUniformizationX q u := by
  have h1 : (u : Kˣ ⧸ Subgroup.zpowers q) ≠ 1 := fun h => hne (by
    rw [tateUniformizationHom_apply, toMul_ofMul, h, tateUniformization_one])
  rw [tateUniformizationHom_apply, toMul_ofMul, tateUniformization_of_ne_one q hq h1]
  rfl

theorem tateCurveAt_congr {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
    {q q' : Kˣ} (h : q = q') (hq : ‖(q : K)‖ < 1) (hq' : ‖(q' : K)‖ < 1) :
    tateCurveAt q hq = tateCurveAt q' hq' := by
  subst h; rfl

/-- The `x`-coordinate transformation between a curve and `E_j` over a common field is defined
over `ℚ((t))` (copy of the computation in `TateCuspGlue`). -/
theorem uR_mem {Ω : Type*} [Field Ω] [CharZero Ω] (ι : LaurentSeries ℚ →+* Ω)
    {W : WeierstrassCurve (LaurentSeries ℚ)} [W.IsElliptic]
    (hj : W.j ∉ Set.range (HahnSeries.ofPowerSeries ℤ ℚ)) (T : WeierstrassCurve Ω)
    {x4 x6 x2 : LaurentSeries ℚ} (hT4 : T.c₄ = ι x4) (hT6 : T.c₆ = ι x6) (hT2 : T.b₂ = ι x2)
    (C : WeierstrassCurve.VariableChange Ω) (hC : C • T = W.map ι) :
    ((C.u : Ω) ^ 2 ∈ ι.fieldRange) ∧ C.r ∈ ι.fieldRange := by
  have hιR : ∀ z, ι z ∈ ι.fieldRange := fun z => ⟨z, rfl⟩
  have h4 := congrArg WeierstrassCurve.c₄ hC
  have h6 := congrArg WeierstrassCurve.c₆ hC
  have h2 := congrArg WeierstrassCurve.b₂ hC
  rw [WeierstrassCurve.variableChange_c₄, WeierstrassCurve.map_c₄ W ι] at h4
  rw [WeierstrassCurve.variableChange_c₆, WeierstrassCurve.map_c₆ W ι] at h6
  rw [WeierstrassCurve.variableChange_b₂, WeierstrassCurve.map_b₂ W ι] at h2
  set a : Ω := ((C.u⁻¹ : Ωˣ) : Ω) with ha
  have ha0 : a ≠ 0 := Units.ne_zero _
  have hc4 : ι W.c₄ ≠ 0 := (map_ne_zero ι).mpr (TateCuspGlue.c₄_ne_zero hj)
  have hc6 : ι W.c₆ ≠ 0 := (map_ne_zero ι).mpr (TateCuspGlue.c₆_ne_zero hj)
  have hT4' : T.c₄ ≠ 0 := fun h0 => hc4 (by rw [← h4, h0, mul_zero])
  have hT6' : T.c₆ ≠ 0 := fun h0 => hc6 (by rw [← h6, h0, mul_zero])
  have ha2 : a ^ 2 = ι W.c₆ * T.c₄ / (ι W.c₄ * T.c₆) := by
    rw [← h4, ← h6]; field_simp
  have ha2R : a ^ 2 ∈ ι.fieldRange := by
    rw [ha2, hT4, hT6]
    exact div_mem (mul_mem (hιR _) (hιR _)) (mul_mem (hιR _) (hιR _))
  refine ⟨?_, ?_⟩
  · have : ((C.u : Ωˣ) : Ω) ^ 2 = (a ^ 2)⁻¹ := by
      rw [ha, Units.val_inv_eq_inv_val, inv_pow, inv_inv]
    rw [this]; exact inv_mem ha2R
  · have : C.r = (ι W.b₂ / a ^ 2 - T.b₂) / 12 := by
      rw [← h2]; field_simp; ring
    rw [this, hT2]
    exact div_mem (sub_mem (div_mem (hιR _) ha2R) (hιR _)) ⟨12, map_ofNat ι 12⟩

end ZInQ.RLeaf.TateCuspMuN

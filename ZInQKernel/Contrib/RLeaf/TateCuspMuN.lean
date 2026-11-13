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

end ZInQ.RLeaf.TateCuspMuN

import ZInQKernel.Contrib.RLeaf.TateCuspGlue
import ZInQKernel.Contrib.TauCeti.Backport.AlgebraicGeometry.EllipticCurve.TateCurve.Homomorphism

/-!
# t40-tate: the Tate curve over `ℚ((t))` has a rational point of exact order `N`

`ℚ((t))` with its `t`-adic valuation is a complete non-archimedean normed field
(`Valued.toNormedField`, with the rank-one structure `|t| = 1/2`). For `N ≥ 2` put `q = t^N`.
Tau Ceti's Tate uniformization `ℚ((t))^× / q^ℤ → E_q(ℚ((t)))` is an injective group homomorphism
(`TauCeti.tateUniformizationHom`, `TauCeti.tateUniformizationHom_injective`, backported from Tau
Ceti main under `ZInQKernel/Contrib/TauCeti/Backport/`), so the image of the class of `t` has the
order of that class, which is `N`. And `|j(E_q)| = 1/|q| > 1` (`TauCeti.norm_tateCurveAt_j`), so
`j(E_q)` is not a power series. This proves `TateLaurentTorsion`.
-/

noncomputable section

namespace ZInQ.RLeaf.TateCuspTorsion

open MonoidWithZeroHom.ValueGroup₀ WithZeroMulInt TauCeti
open scoped WithZero

/-- The `t`-adic valuation of `ℚ((t))` has rank one (normalized by `|t| = 1/2`). -/
@[reducible] def rankOne : (Valued.v : Valuation (LaurentSeries ℚ) ℤᵐ⁰).RankOne where
  hom' := (toNNReal (two_ne_zero)).comp embedding
  strictMono' := (toNNReal_strictMono one_lt_two).comp embedding_strictMono
  exists_val_nontrivial := ⟨HahnSeries.single 1 1, by
    rw [LaurentSeries.valuation_single_zpow]
    exact ⟨WithZero.exp_ne_zero, by
      rw [Ne, ← WithZero.exp_zero, WithZero.exp_inj]; omega⟩⟩

attribute [local instance] rankOne

/-! `ℚ((t))` is a normed field through its rank-one `t`-adic valuation (`Valued.toNormedField`,
a scoped instance). -/
open scoped Valued

instance : IsUltrametricDist (LaurentSeries ℚ) := inferInstance

instance : CompleteSpace (LaurentSeries ℚ) := LaurentSeries.instLaurentSeriesComplete

/-- The uniformizer `t` as a unit. -/
def tU : (LaurentSeries ℚ)ˣ := Units.mk0 (HahnSeries.single 1 1) (by simp)

theorem valuation_tU_zpow (k : ℤ) :
    Valued.v (((tU ^ k : (LaurentSeries ℚ)ˣ)) : LaurentSeries ℚ) = WithZero.exp (-k) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀]
  change Valued.v (HahnSeries.single (1 : ℤ) (1 : ℚ) : LaurentSeries ℚ) ^ k = _
  rw [LaurentSeries.valuation_single_zpow, ← WithZero.exp_zsmul]
  simp

theorem norm_q_lt_one (N : ℕ) (hN : 1 ≤ N) : ‖((tU ^ N : (LaurentSeries ℚ)ˣ) : LaurentSeries ℚ)‖ < 1 := by
  rw [Valued.toNormedField.norm_lt_one_iff]
  have := valuation_tU_zpow (N : ℤ)
  rw [zpow_natCast] at this
  rw [this, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  omega

/-- The class of `t` in `ℚ((t))^× / (t^N)^ℤ` has order `N`. -/
theorem orderOf_mk_tU (N : ℕ) (hN : 1 ≤ N) :
    orderOf ((tU : (LaurentSeries ℚ)ˣ) : (LaurentSeries ℚ)ˣ ⧸ Subgroup.zpowers (tU ^ N)) = N := by
  rw [orderOf_eq_iff (by omega)]
  refine ⟨?_, fun m hm hm0 h => ?_⟩
  · rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_zpowers _
  · rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_zpowers_iff] at h
    obtain ⟨k, hk⟩ := h
    rw [← zpow_natCast, ← zpow_mul, ← zpow_natCast] at hk
    have hv := congrArg (fun u : (LaurentSeries ℚ)ˣ => Valued.v (u : LaurentSeries ℚ)) hk
    simp only [valuation_tU_zpow, WithZero.exp_inj, neg_inj] at hv
    have : (N : ℤ) ∣ m := ⟨k, by rw [← hv]⟩
    have := Int.le_of_dvd (by omega) this
    omega

open Classical in
/-- **`TateLaurentTorsion` holds**: the Tate curve `E_{t^N}` over `ℚ((t))` with the point `t`. -/
theorem tateLaurentTorsion : TateLaurentTorsion := by
  intro N hN
  have hq := norm_q_lt_one N (by omega)
  refine ⟨tateCurveAt (tU ^ N) hq, inferInstance,
    tateUniformizationHom (tU ^ N) hq (Additive.ofMul (tU : _ ⧸ Subgroup.zpowers (tU ^ N))),
    ?_, ?_⟩
  · have h := addOrderOf_injective (tateUniformizationHom (tU ^ N) hq)
      (tateUniformizationHom_injective (tU ^ N) hq)
      (Additive.ofMul (tU : _ ⧸ Subgroup.zpowers (tU ^ N)))
    rw [addOrderOf_ofMul_eq_orderOf, orderOf_mk_tU N (by omega)] at h
    convert h using 2
  · rintro ⟨F, hF⟩
    have h1 : Valued.v (tateCurveAt (tU ^ N) hq).j ≤ 1 :=
      (LaurentSeries.val_le_one_iff_eq_coe ℚ _).mpr ⟨F, hF⟩
    rw [← Valued.toNormedField.norm_le_one_iff, norm_tateCurveAt_j] at h1
    have hpos : 0 < ‖((tU ^ N : (LaurentSeries ℚ)ˣ) : LaurentSeries ℚ)‖ :=
      norm_pos_iff.mpr (Units.ne_zero _)
    have := (one_lt_inv₀ hpos).mpr hq
    linarith

end ZInQ.RLeaf.TateCuspTorsion

#print axioms ZInQ.RLeaf.TateCuspTorsion.tateLaurentTorsion

import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.PrimitiveEisensteinGcdData

/-!
# Same-level primitive gcd normalization

Dividing a genuine gcd-d integer vector normalizes its gcd to one. When d
is coprime to the level, its residue is an actual unit and the normalized
residue is the inverse-unit translate at the same level. The actual
unrestricted series is decomposed into these actual primitive series.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

open Complex Filter Set ModularForm
open scoped Topology Real UpperHalfPlane MatrixGroups

namespace ZInQ.Contrib.HeckePrimeRationality.PrimitiveEisensteinNormalization

open ZInQ.Contrib.HeckePrimeRationality
open PrimitiveEisensteinGcdData

/-- Scale the residue coordinates by an actual level unit. -/
def scaleResidue {N : ℕ} (u : (ZMod N)ˣ) (a : Fin 2 → ZMod N) : Fin 2 → ZMod N :=
  fun i => (u : ZMod N) * a i

/-- Actual finite primitive residue rows, independently of any spanning predicate. -/
abbrev PrimitiveRow (N : ℕ) := {a : Fin 2 → ZMod N // IsCoprime (a 0) (a 1)}

/-- Unit multiplication is an actual permutation of the primitive residue rows. -/
def primitiveUnitEquiv (N : ℕ) (u : (ZMod N)ˣ) : Equiv.Perm (PrimitiveRow N) where
  toFun a := ⟨scaleResidue u a.1, (isCoprime_mul_unit_left u.isUnit _ _).mpr a.2⟩
  invFun a := ⟨scaleResidue u⁻¹ a.1, (isCoprime_mul_unit_left u⁻¹.isUnit _ _).mpr a.2⟩
  left_inv a := by
    apply Subtype.ext
    funext i
    change u.inv * (u.val * a.1 i) = a.1 i
    rw [← mul_assoc, u.inv_val, one_mul]
  right_inv a := by
    apply Subtype.ext
    funext i
    change u.val * (u.inv * a.1 i) = a.1 i
    rw [← mul_assoc, u.val_inv, one_mul]

/-- The actual summand is homogeneous under positive integer scaling. -/
lemma eisSummand_nsmul (d : ℕ) (k : ℕ) (v : Fin 2 → ℤ) (τ : ℍ) :
    EisensteinSeries.eisSummand (k : ℤ) (d • v) τ =
      (d : ℂ) ^ (-(k : ℤ)) * EisensteinSeries.eisSummand (k : ℤ) v τ := by
  simp only [EisensteinSeries.eisSummand, Pi.smul_apply, nsmul_eq_mul,
    Int.cast_mul, Int.cast_natCast]
  rw [show (d : ℂ) * (v 0 : ℂ) * (τ : ℂ) + (d : ℂ) * (v 1 : ℂ) =
    (d : ℂ) * ((v 0 : ℂ) * (τ : ℂ) + (v 1 : ℂ)) by ring, mul_zpow]

/-- Genuine gcd division and residue normalization at exactly the same level. -/
def sameLevelDivGcdEquiv (N d : ℕ) (hd : 0 < d) (a : Fin 2 → ZMod N)
    (u : (ZMod N)ˣ) (hu : (u : ZMod N) = (d : ZMod N)) :
    EisensteinSeries.gammaSet N d a ≃ EisensteinSeries.gammaSet N 1 (scaleResidue u⁻¹ a) where
  toFun v := ⟨EisensteinSeries.divIntMap d v.1, by
    let _ : NeZero d := ⟨hd.ne'⟩
    refine ⟨?_, Int.isCoprime_iff_gcd_eq_one.mp (EisensteinSeries.finGcdMap_div v.1 v.2.2)⟩
    have hbase : v.1 ∈ EisensteinSeries.gammaSet 1 d 0 := ⟨Subsingleton.eq_zero _,v.2.2⟩
    have hv := EisensteinSeries.gammaSet_eq_gcd_mul_divIntMap hbase
    funext i
    have hvi := congrFun hv i
    simp only [Pi.smul_apply, nsmul_eq_mul] at hvi
    have hcast : a i = (d : ZMod N) * (EisensteinSeries.divIntMap d v.1 i : ZMod N) := by
      rw [← congrFun v.2.1 i]
      simp only [Function.comp_apply]
      rw [hvi, Int.cast_mul, Int.cast_natCast]
    change (EisensteinSeries.divIntMap d v.1 i : ZMod N) = u.inv * a i
    rw [hcast, ← hu, ← mul_assoc, u.inv_val, one_mul]⟩
  invFun v := ⟨d • v.1, by
    refine ⟨?_, ?_⟩
    · funext i
      have hvi := congrFun v.2.1 i
      change (v.1 i : ZMod N) = u.inv * a i at hvi
      simp only [Function.comp_apply, Pi.mul_apply, Pi.natCast_apply, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast]
      rw [hvi, ← hu, ← mul_assoc, u.val_inv, one_mul]
    · simp only [Pi.smul_apply, nsmul_eq_mul, Int.gcd_mul_left, Int.natAbs_natCast, v.2.2, mul_one]⟩
  left_inv v := by
    apply Subtype.ext
    have hbase : v.1 ∈ EisensteinSeries.gammaSet 1 d 0 := ⟨Subsingleton.eq_zero _,v.2.2⟩
    exact (EisensteinSeries.gammaSet_eq_gcd_mul_divIntMap hbase).symm
  right_inv v := by
    apply Subtype.ext
    funext i
    have hdI : (d : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
    change (d : ℤ) * v.1 i / (d : ℤ) = v.1 i
    exact Int.mul_ediv_cancel_left _ hdI

lemma sameLevelDivGcdEquiv_apply (N d : ℕ) (hd : 0 < d) (a : Fin 2 → ZMod N)
    (u : (ZMod N)ˣ) (hu : (u : ZMod N) = (d : ZMod N))
    (v : EisensteinSeries.gammaSet N d a) :
    ((sameLevelDivGcdEquiv N d hd a u hu) v).1 = EisensteinSeries.divIntMap d v.1 := rfl

/-- The actual gcd-d row equals d^-k times the actual primitive inverse-unit row. -/
theorem gammaSet_tsum_eq_primitive (N d : ℕ) (hd : 0 < d) (a : Fin 2 → ZMod N)
    (u : (ZMod N)ˣ) (hu : (u : ZMod N) = (d : ZMod N))
    (k : ℕ) (τ : ℍ) :
    (∑' v : EisensteinSeries.gammaSet N d a, EisensteinSeries.eisSummand (k : ℤ) v.1 τ) =
      (d : ℂ) ^ (-(k : ℤ)) * eisensteinSeries (scaleResidue u⁻¹ a) (k : ℤ) τ := by
  let e := sameLevelDivGcdEquiv N d hd a u hu
  have hterm (v : EisensteinSeries.gammaSet N d a) :
      EisensteinSeries.eisSummand (k : ℤ) v.1 τ =
      (d : ℂ) ^ (-(k : ℤ)) * EisensteinSeries.eisSummand (k : ℤ) (e v).1 τ := by
    have hbase : v.1 ∈ EisensteinSeries.gammaSet 1 d 0 := ⟨Subsingleton.eq_zero _,v.2.2⟩
    rw [sameLevelDivGcdEquiv_apply]
    rw [← eisSummand_nsmul, ← EisensteinSeries.gammaSet_eq_gcd_mul_divIntMap hbase]
  change (∑' v : EisensteinSeries.gammaSet N d a, EisensteinSeries.eisSummand (k : ℤ) v.1 τ) =
    (d : ℂ) ^ (-(k : ℤ)) * ∑' w : EisensteinSeries.gammaSet N 1 (scaleResidue u⁻¹ a),
      EisensteinSeries.eisSummand (k : ℤ) w.1 τ
  rw [← tsum_mul_left]
  calc
    _ = ∑' v : EisensteinSeries.gammaSet N d a,
        (d : ℂ) ^ (-(k : ℤ)) * EisensteinSeries.eisSummand (k : ℤ) (e v).1 τ := tsum_congr hterm
    _ = ∑' w : EisensteinSeries.gammaSet N 1 (scaleResidue u⁻¹ a),
        (d : ℂ) ^ (-(k : ℤ)) * EisensteinSeries.eisSummand (k : ℤ) w.1 τ := by
      simpa only [Function.comp_apply] using!
        e.tsum_eq (fun w : EisensteinSeries.gammaSet N 1 (scaleResidue u⁻¹ a) =>
          (d : ℂ) ^ (-(k : ℤ)) * EisensteinSeries.eisSummand (k : ℤ) w.1 τ)

/-- Actual primitive-row gcd decomposition, with every unit supplied canonically by coprimality. -/
theorem unrestrictedSeries_eq_unit_series (N : ℕ) (hN : 3 ≤ N) (a : Fin 2 → ZMod N)
    (ha : IsCoprime (a 0) (a 1)) (k : ℕ) (hk : 3 ≤ k) (τ : ℍ) :
    unrestrictedSeries N a k τ = ∑' d : ℕ, if hd : d.Coprime N then
      (d : ℂ) ^ (-(k : ℤ)) *
        eisensteinSeries (scaleResidue (ZMod.unitOfCoprime d hd)⁻¹ a) (k : ℤ) τ else 0 := by
  rw [unrestrictedSeries_eq_tsum_gcd N a k hk τ]
  refine tsum_congr fun d => ?_
  split_ifs with hd
  · have hdpos : 0 < d := by
      by_contra h
      have hd0 : d = 0 := by omega
      subst d
      simp only [Nat.coprime_zero_left] at hd
      omega
    exact gammaSet_tsum_eq_primitive N d hdpos a (ZMod.unitOfCoprime d hd) (by rfl) k τ
  · let _ : IsEmpty (EisensteinSeries.gammaSet N d a) := gammaSet_isEmpty_nonunit_gcd ha hd
    simp

end ZInQ.Contrib.HeckePrimeRationality.PrimitiveEisensteinNormalization

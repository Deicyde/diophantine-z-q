import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic

/-!
# Actual primitive Eisenstein congruence and gcd data

The primitive object is Mathlib's gcd-one gamma set and Eisenstein modular
form. Unrestricted congruence rows are kept separate. Absolute convergence
permits their genuine gcd-fiber decomposition, with the zero gcd summand
handled explicitly and nonprimitive residue rows proved empty.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

open Complex Filter Set ModularForm
open scoped Topology Real UpperHalfPlane MatrixGroups

namespace ZInQ.Contrib.HeckePrimeRationality.PrimitiveEisensteinGcdData

open ZInQ.Contrib.HeckePrimeRationality

/-- A genuine primitive integer vector has coprime residue coordinates. -/
lemma residue_coprime_of_gammaSet_one {N : ℕ} {a : Fin 2 → ZMod N}
    (v : EisensteinSeries.gammaSet N 1 a) : IsCoprime (a 0) (a 1) := by
  have hc : IsCoprime (v.1 0) (v.1 1) := Int.isCoprime_iff_gcd_eq_one.mpr v.2.2
  have hm : IsCoprime (v.1 0 : ZMod N) (v.1 1 : ZMod N) := hc.intCast
  have h0 : (v.1 0 : ZMod N) = a 0 := congrFun v.2.1 0
  have h1 : (v.1 1 : ZMod N) = a 1 := congrFun v.2.1 1
  rwa [h0, h1] at hm

/-- Nonprimitive residue coordinates give a genuinely empty primitive gamma set. -/
lemma gammaSet_one_isEmpty {N : ℕ} (a : Fin 2 → ZMod N) (ha : ¬ IsCoprime (a 0) (a 1)) :
    IsEmpty (EisensteinSeries.gammaSet N 1 a) :=
  ⟨fun v => ha (residue_coprime_of_gammaSet_one v)⟩

/-- The actual Mathlib primitive modular form is zero on a nonprimitive residue row. -/
theorem eisensteinSeriesMF_eq_zero_nonprimitive {N : ℕ} [NeZero N] {k : ℤ} (hk : 3 ≤ k)
    (a : Fin 2 → ZMod N) (ha : ¬ IsCoprime (a 0) (a 1)) :
    ModularForm.eisensteinSeriesMF hk a = 0 := by
  let _ : IsEmpty (EisensteinSeries.gammaSet N 1 a) := gammaSet_one_isEmpty a ha
  apply DFunLike.ext
  intro τ
  change eisensteinSeries a k τ = 0
  simp [eisensteinSeries]

/-- A gcd divisor of an integer vector in a primitive residue row is an actual residue unit. -/
lemma gcd_isUnit_of_primitive_row {N r : ℕ} {a : Fin 2 → ZMod N}
    (ha : IsCoprime (a 0) (a 1)) (v : EisensteinSeries.gammaSet N r a) :
    IsUnit (r : ZMod N) := by
  have hbase : v.1 ∈ EisensteinSeries.gammaSet 1 r 0 := ⟨Subsingleton.eq_zero _, v.2.2⟩
  have hdvd (i : Fin 2) : (r : ZMod N) ∣ a i := by
    obtain ⟨c, hc⟩ := EisensteinSeries.gammaSet_div_gcd hbase i
    refine ⟨(c : ZMod N), ?_⟩
    rw [← congrFun v.2.1 i]
    change (v.1 i : ZMod N) = (r : ZMod N) * (c : ZMod N)
    rw [hc, Int.cast_mul, Int.cast_natCast]
  exact ha.isUnit_of_dvd' (hdvd 0) (hdvd 1)

/-- The possible positive gcd divisors in a primitive residue row are coprime to N. -/
lemma gcd_coprime_level_of_primitive_row {N r : ℕ} {a : Fin 2 → ZMod N}
    (ha : IsCoprime (a 0) (a 1)) (v : EisensteinSeries.gammaSet N r a) : r.Coprime N :=
  (ZMod.isUnit_iff_coprime r N).mp (gcd_isUnit_of_primitive_row ha v)

/-- Nonunit gcd fibers in a primitive residue row are empty. -/
lemma gammaSet_isEmpty_nonunit_gcd {N r : ℕ} {a : Fin 2 → ZMod N}
    (ha : IsCoprime (a 0) (a 1)) (hr : ¬ r.Coprime N) :
    IsEmpty (EisensteinSeries.gammaSet N r a) :=
  ⟨fun v => hr (gcd_coprime_level_of_primitive_row ha v)⟩

/-- Gcd zero forces the zero vector, whose actual positive-weight summand is zero. -/
lemma eisSummand_zero_gcd (N : ℕ) (a : Fin 2 → ZMod N) (k : ℕ) (hk : 3 ≤ k)
    (τ : ℍ) (v : EisensteinSeries.gammaSet N 0 a) :
    EisensteinSeries.eisSummand (k : ℤ) v.1 τ = 0 := by
  have hv := Int.gcd_eq_zero_iff.mp v.2.2
  have hk0 : k ≠ 0 := by omega
  simp [EisensteinSeries.eisSummand, hv.1, hv.2, _root_.zpow_neg, _root_.zpow_natCast, hk0]

lemma tsum_zero_gcd (N : ℕ) (a : Fin 2 → ZMod N) (k : ℕ) (hk : 3 ≤ k) (τ : ℍ) :
    (∑' v : EisensteinSeries.gammaSet N 0 a, EisensteinSeries.eisSummand (k : ℤ) v.1 τ) = 0 := by
  simp only [eisSummand_zero_gcd N a k hk τ, tsum_zero]

/-- The actual full integer-vector summands are absolutely summable in the target weight range. -/
lemma summable_eisSummand_vector (k : ℕ) (hk : 3 ≤ k) (τ : ℍ) :
    Summable (fun v : Fin 2 → ℤ => EisensteinSeries.eisSummand (k : ℤ) v τ) := by
  have hkR : (2 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 2 < k)
  have hs := (EisensteinSeries.summable_one_div_norm_rpow hkR).mul_left
    (EisensteinSeries.r τ ^ (-(k : ℝ)))
  have hn : Summable (fun v : Fin 2 → ℤ => ‖EisensteinSeries.eisSummand (k : ℤ) v τ‖) := by
    apply hs.of_nonneg_of_le (fun v => norm_nonneg _)
    intro v
    simpa only [EisensteinSeries.eisSummand, norm_zpow, ← Real.rpow_intCast,
      Int.cast_neg, Int.cast_natCast] using EisensteinSeries.summand_bound τ (by positivity : (0 : ℝ) ≤ k) v
  exact hn.of_norm

lemma summable_gammaSet (N r : ℕ) (a : Fin 2 → ZMod N) (k : ℕ) (hk : 3 ≤ k) (τ : ℍ) :
    Summable (fun v : EisensteinSeries.gammaSet N r a => EisensteinSeries.eisSummand (k : ℤ) v.1 τ) :=
  (summable_eisSummand_vector k hk τ).subtype (EisensteinSeries.gammaSet N r a)

/-- The unrestricted residue class, without a gcd filter. -/
def congruenceSet (N : ℕ) (a : Fin 2 → ZMod N) : Set (Fin 2 → ℤ) :=
  {v | (↑) ∘ v = a}

/-- The actual unrestricted vector series is independent of the primitive-series definition. -/
def unrestrictedSeries (N : ℕ) (a : Fin 2 → ZMod N) (k : ℕ) (τ : ℍ) : ℂ :=
  ∑' v : congruenceSet N a, EisensteinSeries.eisSummand (k : ℤ) v.1 τ

/-- Restrict the actual gcd-fiber map to a genuine unrestricted congruence row. -/
def congruenceGcdEquiv (N : ℕ) (a : Fin 2 → ZMod N) :
    congruenceSet N a ≃ (Σ r : ℕ, EisensteinSeries.gammaSet N r a) :=
  (Equiv.sigmaFiberEquiv (fun v : congruenceSet N a => EisensteinSeries.finGcdMap v.1)).symm.trans
    (Equiv.sigmaCongrRight fun r =>
      { toFun := fun v => ⟨v.1.1, v.1.2, v.2⟩
        invFun := fun v => ⟨⟨v.1, v.2.1⟩, v.2.2⟩
        left_inv := fun v => by cases v; rfl
        right_inv := fun v => by cases v; rfl })

lemma congruenceGcdEquiv_symm_val (N : ℕ) (a : Fin 2 → ZMod N)
    (v : Σ r : ℕ, EisensteinSeries.gammaSet N r a) :
    ((congruenceGcdEquiv N a).symm v).1 = v.2.1 := rfl

/-- Absolute gcd decomposition of the actual unrestricted congruence series. -/
theorem unrestrictedSeries_eq_tsum_gcd (N : ℕ) (a : Fin 2 → ZMod N) (k : ℕ) (hk : 3 ≤ k) (τ : ℍ) :
    unrestrictedSeries N a k τ =
      ∑' r : ℕ, ∑' v : EisensteinSeries.gammaSet N r a, EisensteinSeries.eisSummand (k : ℤ) v.1 τ := by
  have hs := (summable_eisSummand_vector k hk τ).subtype (congruenceSet N a)
  have hg := (congruenceGcdEquiv N a).symm.hasSum_iff.mpr hs.hasSum
  have ht := hg.summable.tsum_sigma
  rw [hg.tsum_eq] at ht
  simpa only [Function.comp_apply, congruenceGcdEquiv_symm_val, unrestrictedSeries] using! ht

end ZInQ.Contrib.HeckePrimeRationality.PrimitiveEisensteinGcdData

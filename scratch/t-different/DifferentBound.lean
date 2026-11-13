import Mathlib

/-!
# t-different: Serre's bound for the different (T21, local = `PkgI6.DifferentBound`)
# reduced to the trace statement `e ∈ Tr_{B/A}(B)`

Check with `lake env lean scratch/t-different/DifferentBound.lean`.
-/

open IsLocalRing

namespace TDifferent

section DVR

variable {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]

theorem span_eq_maximalIdeal_pow {a : B} (ha : a ≠ 0) :
    ∃ n, Ideal.span {a} = maximalIdeal B ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible B
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (s := Ideal.span {a}) (by simpa using ha) hϖ
  exact ⟨n, by rw [hn, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]⟩

theorem maximalIdeal_pow_le_iff {m n : ℕ} :
    maximalIdeal B ^ m ≤ maximalIdeal B ^ n ↔ n ≤ m :=
  (Ideal.pow_right_strictAnti _ (IsDiscreteValuationRing.not_a_field B)
    (maximalIdeal.isMaximal B).ne_top).le_iff_ge

/-- An element of `𝔪 \ 𝔪²` generates `𝔪`. -/
theorem maximalIdeal_eq_span_of_mem_of_notMem {t : B} (ht : t ∈ maximalIdeal B)
    (ht2 : t ∉ maximalIdeal B ^ 2) : maximalIdeal B = Ideal.span {t} := by
  have ht0 : t ≠ 0 := by rintro rfl; exact ht2 (Ideal.zero_mem _)
  obtain ⟨n, hn⟩ := span_eq_maximalIdeal_pow ht0
  have h1 : 1 ≤ n := by
    rw [← maximalIdeal_pow_le_iff (B := B), ← hn, pow_one, Ideal.span_singleton_le_iff_mem]; exact ht
  have h2 : ¬ 2 ≤ n := by
    rw [← maximalIdeal_pow_le_iff (B := B), ← hn, Ideal.span_singleton_le_iff_mem]; exact ht2
  rw [hn, show n = 1 by omega, pow_one]

end DVR

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- `𝔪_A B = 𝔪_B ^ e` with `e` Mathlib's `Ideal.ramificationIdx`. -/
theorem map_maximalIdeal_eq_pow (A B : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B]
    [Module.IsTorsionFree A B] :
    (maximalIdeal A).map (algebraMap A B) =
      maximalIdeal B ^ Ideal.ramificationIdx (maximalIdeal B) A := by
  have hinjAB : Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B
  have : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  have : IsLocalHom (algebraMap A B) := Algebra.IsIntegral.isLocalHom A B
  have hmA : (maximalIdeal A).map (algebraMap A B) ≠ ⊥ := by
    rw [ne_eq, Ideal.map_eq_bot_iff_of_injective hinjAB]
    exact IsDiscreteValuationRing.not_a_field A
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible B
  obtain ⟨j, hj⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hmA hπ
  rw [← Ideal.span_singleton_pow, ← hπ.maximalIdeal_eq] at hj
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (maximalIdeal A) (maximalIdeal B)
    (IsDiscreteValuationRing.not_a_field A)]
  rw [Ideal.ramificationIdx'_spec (n := j) (by rw [hj]) (by rw [hj, maximalIdeal_pow_le_iff]; omega)]
  exact hj

end TDifferent

namespace PkgI6

open IsLocalRing

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- Verbatim copy of `PkgI6.DifferentBound` (Leaves.lean line 5080). -/
def DifferentBound : Prop :=
  ∀ (A B : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A] [PerfectField (ResidueField A)]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B]
    [Module.IsTorsionFree A B] [Algebra.IsSeparable (FractionRing A) (FractionRing B)],
    differentIdeal A B ∣
      maximalIdeal B ^ (Ideal.ramificationIdx (maximalIdeal B) A - 1) *
        Ideal.span {((Ideal.ramificationIdx (maximalIdeal B) A : ℕ) : B)}

/-- **The trace statement (equivalent content of T21).** In the setting of `DifferentBound`, the
ramification index `e` lies in the trace ideal `Tr_{B/A}(B)`.  (Standard proof: `e = Tr(u)` for
`u` in the maximal unramified subring `U = A[u]` with `Tr_{U/A}(u) = 1`, since
`Tr_{B/A}(u) = Tr_{U/A}(e·u)`; Serre, *Corps locaux*, III §5-§6, UNVERIFIED locator.) -/
def TraceContainsRamificationIdx : Prop :=
  ∀ (A B : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A] [PerfectField (ResidueField A)]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B]
    [Module.IsTorsionFree A B] [Algebra.IsSeparable (FractionRing A) (FractionRing B)],
    ∃ z : B, Algebra.intTrace A B z = ((Ideal.ramificationIdx (maximalIdeal B) A : ℕ) : A)

/-- **T21 (local) from the trace statement.** -/
theorem differentBound_of_trace (h : TraceContainsRamificationIdx) : DifferentBound := by
  intro A B _ _ _ _ _ _ _ _ _ _ _ _
  obtain ⟨z, hz⟩ := h A B
  set e := Ideal.ramificationIdx (maximalIdeal B) A with he_def
  have hinjAB : Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B
  have hmap := TDifferent.map_maximalIdeal_eq_pow A B
  rw [← he_def] at hmap
  by_cases heB : ((e : ℕ) : B) = 0
  · rw [heB, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mul_bot]
    exact dvd_zero _
  have heA : ((e : ℕ) : A) ≠ 0 := by
    intro h; apply heB; rw [← map_natCast (algebraMap A B), h, map_zero]
  have he1 : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h0 | h0
    · exact absurd (by rw [h0, Nat.cast_zero]) heB
    · exact h0
  obtain ⟨k, hk⟩ := TDifferent.span_eq_maximalIdeal_pow heA
  have hkB : Ideal.span {((e : ℕ) : B)} = maximalIdeal B ^ (e * k) := by
    rw [← map_natCast (algebraMap A B), ← Set.image_singleton, ← Ideal.map_span, hk, Ideal.map_pow, hmap, pow_mul]
  have hD0 : differentIdeal A B ≠ ⊥ := differentIdeal_ne_bot
  obtain ⟨d, hd⟩ : ∃ d, differentIdeal A B = maximalIdeal B ^ d := by
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible B
    obtain ⟨d, hd⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hD0 hπ
    exact ⟨d, by rw [hd, hπ.maximalIdeal_eq, Ideal.span_singleton_pow]⟩
  rw [hkB, ← pow_add, hd, Ideal.dvd_iff_le, TDifferent.maximalIdeal_pow_le_iff]
  by_contra hlt
  rw [not_le] at hlt
  -- `𝔪_B ^ (e (k+1)) = (𝔪_A ^ (k+1)) B` divides `𝔇`, contradicting `Tr z = e ∉ 𝔪_A ^ (k+1)`.
  have hP : maximalIdeal B ^ (e * (k + 1)) * ⊤ = (maximalIdeal A ^ (k + 1)).map (algebraMap A B) := by
    rw [Ideal.mul_top, Ideal.map_pow, hmap, pow_mul]
  apply not_dvd_differentIdeal_of_intTrace_notMem A _ ⊤ hP z Submodule.mem_top
  · rw [hz]
    intro hmem
    have : maximalIdeal A ^ k ≤ maximalIdeal A ^ (k + 1) := by
      rw [← hk, Ideal.span_singleton_le_iff_mem]; exact hmem
    rw [TDifferent.maximalIdeal_pow_le_iff] at this
    omega
  · rw [hd, Ideal.dvd_iff_le, TDifferent.maximalIdeal_pow_le_iff]
    have : e * (k + 1) = e + e * k := by ring
    omega

end PkgI6

#print axioms PkgI6.differentBound_of_trace

/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ValuationSubring_ringKrullDim_le_toENat_trdeg_rat_add_one (git blob d078002ef80a2e2958209db94fd60cdcf46a3c31, sha256 0bbb22eb238a101dadb5766b24e27189a9cf91a98343dbc62fda375d078efc6c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ValuationSubring_ringKrullDim_le_ringKrullDim_comap_add_trdeg

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ValuationSubring_ringKrullDim_le_toENat_trdeg_rat_add_one.AbhRatSol
end P2MW.S_ValuationSubring_ringKrullDim_le_toENat_trdeg_rat_add_one.AbhRatSol

namespace P2MW.S_ValuationSubring_ringKrullDim_le_toENat_trdeg_rat_add_one

namespace AbhRatSol

open ValuationSubring

def unitInts (B : ValuationSubring ℚ) : Submonoid ℤ :=
  (IsUnit.submonoid B).comap (algebraMap ℤ B)

lemma mem_unitInts {B : ValuationSubring ℚ} {n : ℤ} :
    n ∈ unitInts B ↔ IsUnit (algebraMap ℤ B n) := Iff.rfl

lemma unitInts_le_nonZeroDivisors (B : ValuationSubring ℚ) : unitInts B ≤ nonZeroDivisors ℤ := by
  intro n hn
  rw [mem_nonZeroDivisors_iff_ne_zero]
  rintro rfl
  rw [mem_unitInts, map_zero] at hn
  exact not_isUnit_zero hn

lemma isUnit_den (B : ValuationSubring ℚ) (x : B) : IsUnit (algebraMap ℤ B ((x : ℚ).den : ℤ)) := by
  set r : ℚ := (x : ℚ) with hr
  have hcop : IsCoprime r.num (r.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs, Int.natAbs_natCast]
    exact r.reduced
  obtain ⟨u, v, huv⟩ := hcop
  have hden0 : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_ne_zero

  have hinv : ((r.den : ℚ))⁻¹ = u * r + v := by
    have h1 : (u : ℚ) * r.num + v * r.den = 1 := by exact_mod_cast huv
    have h2 : (r.num : ℚ) = r * r.den := by rw [Rat.mul_den_eq_num]
    rw [h2] at h1
    field_simp
    linarith [h1]
  have hmem : ((r.den : ℚ))⁻¹ ∈ B := by
    rw [hinv]
    exact B.add_mem _ _ (B.mul_mem _ _ (intCast_mem B u) x.2) (intCast_mem B v)
  refine ⟨⟨algebraMap ℤ B (r.den : ℤ), ⟨_, hmem⟩, ?_, ?_⟩, rfl⟩
  · apply Subtype.ext
    simp [hden0]
  · apply Subtype.ext
    simp [hden0]

scoped instance isLocalization (B : ValuationSubring ℚ) : IsLocalization (unitInts B) B := by
  rw [isLocalization_iff]
  refine ⟨fun n => n.2, fun z => ?_, fun {a b} h => ⟨1, by
    have : (a : ℚ) = b := by
      have h' := congrArg (fun t : B => (t : ℚ)) h
      simpa using h'
    exact_mod_cast congrArg (fun t => 1 * t) (show a = b by exact_mod_cast this)⟩⟩
  refine ⟨⟨(z : ℚ).num, ⟨((z : ℚ).den : ℤ), isUnit_den B z⟩⟩, ?_⟩
  apply Subtype.ext
  simp [Rat.mul_den_eq_num]

theorem ringKrullDim_le_one (B : ValuationSubring ℚ) : ringKrullDim B ≤ 1 := by
  have h : Ring.DimensionLEOne B :=
    Ring.DimensionLEOne.localization B (unitInts_le_nonZeroDivisors B)
  have : Ring.KrullDimLE 1 B := inferInstance
  exact (Ring.krullDimLE_iff).mp this

end AbhRatSol
open scoped _root_.P2MW.S_ValuationSubring_ringKrullDim_le_toENat_trdeg_rat_add_one.AbhRatSol

open AbhRatSol in
theorem solution
    {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L) :
    ringKrullDim A ≤ (Cardinal.toENat (Algebra.trdeg ℚ L) : WithBot ℕ∞) + 1 := by
  have h := ValuationSubring.ringKrullDim_le_ringKrullDim_comap_add_trdeg (K := ℚ) A
  have h0 := ringKrullDim_le_one (A.comap (algebraMap ℚ L))
  calc ringKrullDim A ≤ ringKrullDim (A.comap (algebraMap ℚ L)) +
        (Cardinal.toENat (Algebra.trdeg ℚ L) : WithBot ℕ∞) := h
    _ ≤ 1 + (Cardinal.toENat (Algebra.trdeg ℚ L) : WithBot ℕ∞) := add_le_add h0 le_rfl
    _ = _ := add_comm _ _

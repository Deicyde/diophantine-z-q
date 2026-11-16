/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_PadicAlgCl_norm_apply_sub_le_norm_apply_sub_of_mem_cyclotomicTower
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W11Cyclotomic.TowerDefinition
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Theorems.Thm_PadicAlgCl_isIntegral_padicInt_iff_norm_le_one
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Theorems.Thm_IsCyclotomicExtension_Padic_isIntegralClosure_adjoin_singleton_of_prime_pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_PadicAlgCl_norm_apply_sub_le_norm_apply_sub_of_mem_cyclotomicTower

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

namespace TW6

open Polynomial

variable (p : ℕ) [Fact p.Prime]

-- [port T8] local notation "Ω" expanded in place
-- [port T8] local notation "Γ" expanded in place

private lemma _root_.TW6.exists_isPrimitiveRoot (n : ℕ) : ∃ ζ : (PadicAlgCl p), IsPrimitiveRoot ζ (p ^ n) := by
  have hne : p ^ n ≠ 0 := pow_ne_zero n (Fact.out : p.Prime).ne_zero
  haveI : NeZero ((p ^ n : ℕ) : (PadicAlgCl p)) := ⟨by exact_mod_cast hne⟩
  haveI : IsCyclotomicExtension {p ^ n} (PadicAlgCl p) (PadicAlgCl p) := IsSepClosedOfCharZero.isCyclotomicExtension _ _
  exact IsCyclotomicExtension.exists_isPrimitiveRoot (PadicAlgCl p) (PadicAlgCl p) (S := {p ^ n}) rfl hne

-- [port T6] export of private `TW6` names replaced by qualified uses below: exists_isPrimitiveRoot
lemma cyclotomicTower_eq_adjoin (n : ℕ) {ζ : (PadicAlgCl p)} (hζ : IsPrimitiveRoot ζ (p ^ n)) :
    PadicAlgCl.cyclotomicTower p n = IntermediateField.adjoin ℚ_[p] {ζ} := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  apply le_antisymm
  · unfold PadicAlgCl.cyclotomicTower
    rw [IntermediateField.adjoin_le_iff]
    intro ξ (hξ : ξ ^ (p ^ n) = 1)
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hξ
    exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ_[p] ζ) i
  · exact IntermediateField.adjoin.mono ℚ_[p] _ _ (Set.singleton_subset_iff.mpr hζ.pow_eq_one)

lemma norm_eq_one_of_pow_eq_one {ζ : (PadicAlgCl p)} {k : ℕ} (h : ζ ^ k = 1) (hk : k ≠ 0) : ‖ζ‖ = 1 := by
  have h1 : ‖ζ‖ ^ k = 1 := by rw [← norm_pow, h, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hk).mp h1

lemma norm_algEquiv (σ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) (x : (PadicAlgCl p)) : ‖σ x‖ = ‖x‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm,
    minpoly.algEquiv_eq]

section Level

variable (n : ℕ)

-- [port T8] local notation "K" expanded in place

theorem norm_le_one_iff_mem_adjoin {ζ : (PadicAlgCl.cyclotomicTower p n)} (hζ : IsPrimitiveRoot ζ (p ^ n))
    [IsCyclotomicExtension {p ^ n} ℚ_[p] (PadicAlgCl.cyclotomicTower p n)] (x : (PadicAlgCl.cyclotomicTower p n)) :
    ‖(x : (PadicAlgCl p))‖ ≤ 1 ↔ x ∈ Algebra.adjoin ℤ_[p] ({ζ} : Set (PadicAlgCl.cyclotomicTower p n)) := by
  haveI : IsIntegralClosure (Algebra.adjoin ℤ_[p] ({ζ} : Set (PadicAlgCl.cyclotomicTower p n))) ℤ_[p] (PadicAlgCl.cyclotomicTower p n) :=
    IsCyclotomicExtension.Padic.isIntegralClosure_adjoin_singleton_of_prime_pow p n (PadicAlgCl.cyclotomicTower p n) hζ
  haveI : IsScalarTower ℤ_[p] (PadicAlgCl.cyclotomicTower p n) (PadicAlgCl p) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  rw [← PadicAlgCl.isIntegral_padicInt_iff_norm_le_one p (x : (PadicAlgCl p)),
    show ((x : (PadicAlgCl.cyclotomicTower p n)) : (PadicAlgCl p)) = algebraMap (PadicAlgCl.cyclotomicTower p n) (PadicAlgCl p) x from rfl,
    isIntegral_algebraMap_iff,  -- [port] `isIntegral_algebraMap_iff` takes `FaithfulSMul` instead of an injectivity argument in Mathlib 56a0
    IsIntegralClosure.isIntegral_iff (A := Algebra.adjoin ℤ_[p] ({ζ} : Set (PadicAlgCl.cyclotomicTower p n)))]
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

theorem main {ζ : (PadicAlgCl p)} (hζΩ : IsPrimitiveRoot ζ (p ^ n)) (σ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) {y : (PadicAlgCl p)} (hy : y ∈ (PadicAlgCl.cyclotomicTower p n))
    (hy1 : ‖y‖ ≤ 1) : ‖σ y - y‖ ≤ ‖σ ζ - ζ‖ := by
  have hp : p.Prime := Fact.out
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hζmem : ζ ∈ (PadicAlgCl.cyclotomicTower p n) := PadicAlgCl.mem_cyclotomicTower_of_pow_eq_one p hζΩ.pow_eq_one
  set ζ' : (PadicAlgCl.cyclotomicTower p n) := ⟨ζ, hζmem⟩ with hζ'def
  have hinj : Function.Injective (algebraMap (PadicAlgCl.cyclotomicTower p n) (PadicAlgCl p)) := (algebraMap (PadicAlgCl.cyclotomicTower p n) (PadicAlgCl p)).injective
  have hζ' : IsPrimitiveRoot ζ' (p ^ n) := IsPrimitiveRoot.of_map_of_injective hζΩ hinj
  haveI hcyc : IsCyclotomicExtension {p ^ n} ℚ_[p] (PadicAlgCl.cyclotomicTower p n) := by
    rw [cyclotomicTower_eq_adjoin p n hζΩ]
    exact hζΩ.intermediateField_adjoin_isCyclotomicExtension ℚ_[p]

  have hy' : (⟨y, hy⟩ : (PadicAlgCl.cyclotomicTower p n)) ∈ Algebra.adjoin ℤ_[p] ({ζ'} : Set (PadicAlgCl.cyclotomicTower p n)) :=
    (norm_le_one_iff_mem_adjoin p n hζ' ⟨y, hy⟩).mp hy1

  suffices H : ∀ u : (PadicAlgCl.cyclotomicTower p n), u ∈ Algebra.adjoin ℤ_[p] ({ζ'} : Set (PadicAlgCl.cyclotomicTower p n)) →
      ‖(u : (PadicAlgCl p))‖ ≤ 1 ∧ ‖σ u - u‖ ≤ ‖σ ζ - ζ‖ from (H ⟨y, hy⟩ hy').2
  intro u hu
  induction hu using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨(norm_eq_one_of_pow_eq_one p hζΩ.pow_eq_one (NeZero.ne _)).le, le_rfl⟩
  | algebraMap r =>
    refine ⟨?_, ?_⟩
    · change ‖algebraMap ℤ_[p] (PadicAlgCl p) r‖ ≤ 1
      rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (PadicAlgCl p), norm_algebraMap']
      exact r.2
    · change ‖σ (algebraMap ℤ_[p] (PadicAlgCl p) r) - algebraMap ℤ_[p] (PadicAlgCl p) r‖ ≤ _
      rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (PadicAlgCl p), AlgEquiv.commutes, sub_self, norm_zero]
      exact norm_nonneg _
  | add u v _ _ ihu ihv =>
    refine ⟨?_, ?_⟩
    · rw [AddMemClass.coe_add]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ihu.1 ihv.1)
    · rw [AddMemClass.coe_add, map_add, add_sub_add_comm]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ihu.2 ihv.2)
  | mul u v _ _ ihu ihv =>
    refine ⟨?_, ?_⟩
    · rw [MulMemClass.coe_mul, norm_mul]
      exact mul_le_one₀ ihu.1 (norm_nonneg _) ihv.1
    · have hsplit : σ ((u : (PadicAlgCl p)) * v) - (u : (PadicAlgCl p)) * v = σ u * (σ v - v) + (σ u - u) * v := by
        rw [map_mul]; ring
      rw [MulMemClass.coe_mul, hsplit]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · rw [norm_mul, norm_algEquiv]
        calc ‖(u : (PadicAlgCl p))‖ * ‖σ v - v‖ ≤ 1 * ‖σ ζ - ζ‖ :=
              mul_le_mul ihu.1 ihv.2 (norm_nonneg _) zero_le_one
          _ = ‖σ ζ - ζ‖ := one_mul _
      · rw [norm_mul]
        calc ‖σ u - u‖ * ‖(v : (PadicAlgCl p))‖ ≤ ‖σ ζ - ζ‖ * 1 :=
              mul_le_mul ihu.2 ihv.1 (norm_nonneg _) (norm_nonneg _)
          _ = ‖σ ζ - ζ‖ := mul_one _

end Level

end TW6

end

theorem solution
    (p : ℕ) [Fact p.Prime] {n : ℕ} {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ (p ^ n))
    (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) {y : PadicAlgCl p}
    (hy : y ∈ PadicAlgCl.cyclotomicTower p n) (hy1 : ‖y‖ ≤ 1) :
    ‖σ y - y‖ ≤ ‖σ ζ - ζ‖ :=
  TW6.main p n hζ σ hy hy1

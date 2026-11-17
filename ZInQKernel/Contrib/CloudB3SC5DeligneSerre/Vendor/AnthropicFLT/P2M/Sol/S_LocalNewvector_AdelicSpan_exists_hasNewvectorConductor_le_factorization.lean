/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_LocalNewvector_AdelicSpan_exists_hasNewvectorConductor_le_factorization (git blob 5ac431b9aa9545234021479739b9c9f3c324c4a3, sha256 ef61588a466ab7add4591b86c47db1ce7de580e07dc4bde87884539beb67ed83).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LocalNewvector_AdelicSpanCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_LocalNewvector_AdelicSpan_exists_hasNewvectorConductor_le_factorization

set_option autoImplicit false

namespace P63DockRows

open IsDedekindDomain NumberField

theorem exists_hasNewvectorConductor_le_factorization_impl (φ : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hφ : φ ≠ 0) {N : ℕ} (hN : N ≠ 0)
    (hlev : ∀ g ∈ AdelicLevel.finiteLevelOne (𝓞 ℚ) ℚ (AdelicDock.ratLevel N), ∀ x, φ (x * AdelicDock.finEmbed (𝓞 ℚ) ℚ g) = φ x)
    (p : ℕ) [Fact p.Prime] :
    ∃ c : ℕ, c ≤ N.factorization p ∧ LocalNewvector.HasNewvectorConductor p (LocalNewvector.AdelicSpan φ) c := by
  classical
  have hfix : LocalNewvector.AdelicSpan.self φ ∈
      LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 p (N.factorization p)) (LocalNewvector.AdelicSpan φ) := by
    rw [LocalNewvector.mem_fixedSubmodule_iff]
    intro k hk
    rw [LocalNewvector.AdelicSpan.padic_smul_def]
    apply LocalNewvector.AdelicSpan.ext
    rw [LocalNewvector.AdelicSpan.toFn_smul, LocalNewvector.AdelicSpan.toFn_self]
    apply LocalNewvector.AdelicFnCarrier.ext
    intro x
    rw [LocalNewvector.AdelicFnCarrier.toFn_smul, LocalNewvector.AdelicFnCarrier.toFn_mk]
    exact hlev _ ((AdelicDock.localEmbed_mem_finiteLevelOne_iff _ _ _ _).mpr
      (AdelicDock.padicGL_mem_localLevelOne p hN le_rfl hk)) x
  have hne : ∃ n, LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 p n) (LocalNewvector.AdelicSpan φ) ≠ ⊥ :=
    ⟨N.factorization p, fun hbot => LocalNewvector.AdelicSpan.self_ne_zero_of_ne_zero φ hφ
      ((Submodule.mem_bot ℂ).mp (hbot ▸ hfix))⟩
  refine ⟨Nat.find hne, Nat.find_min' hne ?_, Nat.find_spec hne, fun m hm => ?_⟩
  · exact fun hbot => LocalNewvector.AdelicSpan.self_ne_zero_of_ne_zero φ hφ ((Submodule.mem_bot ℂ).mp (hbot ▸ hfix))
  · by_contra hmb
    exact Nat.find_min hne hm hmb

theorem hasNewvectorConductor_zero_of_not_dvd_impl (φ : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hφ : φ ≠ 0) {N : ℕ} (hN : N ≠ 0)
    (hlev : ∀ g ∈ AdelicLevel.finiteLevelOne (𝓞 ℚ) ℚ (AdelicDock.ratLevel N), ∀ x, φ (x * AdelicDock.finEmbed (𝓞 ℚ) ℚ g) = φ x)
    (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ N) :
    LocalNewvector.HasNewvectorConductor p (LocalNewvector.AdelicSpan φ) 0 := by
  obtain ⟨c, hc, h⟩ := exists_hasNewvectorConductor_le_factorization_impl φ hφ hN hlev p
  rw [Nat.factorization_eq_zero_of_not_dvd hp, Nat.le_zero] at hc
  exact hc ▸ h

end P63DockRows

#print axioms P63DockRows.exists_hasNewvectorConductor_le_factorization_impl
#print axioms P63DockRows.hasNewvectorConductor_zero_of_not_dvd_impl

theorem solution
    (φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hφ : φ ≠ 0) {N : ℕ} (hN : N ≠ 0)
    (hlev : ∀ g ∈ NumberField.AdelicLevel.finiteLevelOne (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.ratLevel N),
      ∀ x, φ (x * AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ g) = φ x)
    (p : ℕ) [Fact p.Prime] :
    ∃ c : ℕ, c ≤ N.factorization p ∧
      LocalNewvector.HasNewvectorConductor p (LocalNewvector.AdelicSpan φ) c := by
  apply P63DockRows.exists_hasNewvectorConductor_le_factorization_impl <;> assumption

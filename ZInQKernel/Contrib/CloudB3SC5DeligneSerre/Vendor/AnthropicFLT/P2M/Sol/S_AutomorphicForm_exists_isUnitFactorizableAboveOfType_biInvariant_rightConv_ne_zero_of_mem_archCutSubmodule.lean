/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_exists_isUnitFactorizableAboveOfType_biInvariant_rightConv_ne_zero_of_mem_archCutSubmodule (git blob 6bb192bd5171cc8a3d6c6a49987b8ef00062308d, sha256 3e6a3e0411270f091c4f6838459b4fa88cb5c658c92946075c6e20aa47da9ac9).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RightConvolution
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_TwistedOrbital
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_LocalOrbitalBase
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_exists_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_IsUnitFactorizableAbove_finComponent_glFin_mem_localIntegralSet_of_apply_ne_zero
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_exists_eq_mul_mem_levelOne_inf_finiteAdelicGL2Subgroup_commute_placeEmbed_of_forall_mem_localIntegralSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_exists_isUnitFactorizableAboveOfType_biInvariant_rightConv_ne_zero_of_mem_archCutSubmodule

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm Filter Topology

theorem solution
    (K : Type) [Field K] [NumberField K]
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tys : AutomorphicForm.ArchTypeFamily K)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hcont : Continuous φ) (hne : ∃ g, φ g ≠ 0)
    (hlev : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
      φ (g * k) = φ g)
    (hφt : φ ∈ archCutSubmodule K tys) :
    ∃ f : AdelicGL2 (𝓞 K) K → ℂ,
      IsFactorizableTestFn K f ∧ IsArchBiFinite K tys f ∧
      (∀ k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ∀ x, f (k * x) = f x ∧ f (x * k) = f x) ∧
      (∃ S : Finset (HeightOneSpectrum (𝓞 K)), (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ S) ∧
        IsUnitFactorizableAboveOfType K K tys (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) S f ∧
        ∀ z, f z ≠ 0 →
          (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
            finComponent (𝓞 K) K v (glFin (𝓞 K) K z) ∈ localIntegralSet K v) ∧
          ∃ z₁ z₂ : AdelicGL2 (𝓞 K) K, z = z₁ * z₂ ∧
            z₂ ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K ∧
            ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ xv : GL (Fin 2) (v.adicCompletion K),
              z₁ * UnramifiedWhittaker.placeEmbed K v xv = UnramifiedWhittaker.placeEmbed K v xv * z₁) ∧
      ∃ g, rightConv K φ f g ≠ 0 := by
  classical

  set S : Finset (HeightOneSpectrum (𝓞 K)) :=
    (Ideal.finite_factors (I := N) (by rw [Ne, Ideal.zero_eq_bot]; exact hN)).toFinset with hS
  have hNS : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ S := fun v hv =>
    (Set.Finite.mem_toFinset _).mpr hv

  have hmapI : ∀ (f : 𝓞 K →+* 𝓞 K), (∀ x, f x = x) → Ideal.map f N = N := by
    intro f hf
    have h : f = RingHom.id (𝓞 K) := RingHom.ext hf
    rw [h, Ideal.map_id]

  have key₁ : ∀ I : Ideal (𝓞 K), I = N →
      ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ levelOne (𝓞 K) K I ⊓ finiteAdelicGL2Subgroup K, φ (g * k) = φ g := by
    rintro I rfl; exact hlev
  have key₂ : ∀ I : Ideal (𝓞 K), I = N → ∀ f : AdelicGL2 (𝓞 K) K → ℂ,
      IsUnitFactorizableAboveOfType K K tys (levelOne (𝓞 K) K I ⊓ finiteAdelicGL2Subgroup K) S f →
      IsUnitFactorizableAboveOfType K K tys (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) S f := by
    rintro I rfl f h; exact h
  obtain ⟨φn, hφn', htend⟩ :=
    AutomorphicForm.exists_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule
      K K N S hNS tys φ hcont (key₁ _ (hmapI _ fun x => rfl)) hφt
  have hφn : ∀ n, IsUnitFactorizableAboveOfType K K tys (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) S (φn n) :=
    fun n => key₂ _ (hmapI _ fun x => rfl) _ (hφn' n)
  obtain ⟨g₀, hg₀⟩ := hne
  obtain ⟨n, hn⟩ := ((htend g₀).eventually (isOpen_compl_singleton.mem_nhds hg₀)).exists
  have hf := hφn n
  obtain ⟨⟨hbi, φa, φf, φS, hsl⟩, hbf⟩ := hf
  refine ⟨φn n, ⟨φa, φf, hsl.1, hsl.2.1, hsl.2.2.2.2.2⟩, hbf, fun k hk x => hbi k hk x,
    ⟨S, hNS, hφn n, fun z hz => ?_⟩, g₀, hn⟩
  have hint : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      finComponent (𝓞 K) K v (glFin (𝓞 K) K z) ∈ localIntegralSet K v := fun v hv =>
    AutomorphicForm.IsUnitFactorizableAbove.finComponent_glFin_mem_localIntegralSet_of_apply_ne_zero K _ S (φn n)
      (hφn n).1 z hz v hv
  exact ⟨hint, AutomorphicForm.exists_eq_mul_mem_levelOne_inf_finiteAdelicGL2Subgroup_commute_placeEmbed_of_forall_mem_localIntegralSet
    K N S hNS z hint⟩

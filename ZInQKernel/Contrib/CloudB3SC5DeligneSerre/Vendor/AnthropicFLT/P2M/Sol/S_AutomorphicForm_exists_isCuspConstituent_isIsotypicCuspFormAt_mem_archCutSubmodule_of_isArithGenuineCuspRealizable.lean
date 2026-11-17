/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_exists_isCuspConstituent_isIsotypicCuspFormAt_mem_archCutSubmodule_of_isArithGenuineCuspRealizable (git blob 3b29b56fbd40ff7f948d0867b249f52f5c9e9b58, sha256 822a6e0f2fbcb42b10bba7404bca9dea5c0a8473549e7cc55cb5114aef818b2f).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalConstituent
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_exists_archTypeFamily_isotypicCuspSubmodule_inf_archCutSubmodule_ne_bot
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_isotypicCuspSubmodule_inf_archCutSubmodule_le_iSup_isCuspConstituent
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_exists_finset_isCuspConstituent_le_iSup_of_cuspConstituentMeets
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_LanglandsTunnell_exists_mem_finset_inf_isotypicCuspSubmodule_inf_archCutSubmodule_ne_bot_of_mem_sup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_exists_isCuspConstituent_isIsotypicCuspFormAt_mem_archCutSubmodule_of_isArithGenuineCuspRealizable

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem solution
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (Θ : HeckeEigensystem K ℂ)
    (hΘ : IsArithGenuineCuspRealizable K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ) :
    ∃ (ξ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
      (S : Finset (HeightOneSpectrum (𝓞 K))) (tys : AutomorphicForm.ArchTypeFamily K)
      (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ)) (φ : AdelicGL2 (𝓞 K) K → ℂ),
      IsCuspConstituent K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ V ∧ φ ∈ V ∧ φ ≠ 0 ∧
        IsIsotypicCuspFormAt K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ Θ.level S Θ φ ∧ φ ∈ archCutSubmodule K tys := by

  obtain ⟨R, hR⟩ := hΘ
  have hne := R.isotypicCuspSubmodule_ne_bot hR

  obtain ⟨tys, htys⟩ :=
    AutomorphicForm.exists_archTypeFamily_isotypicCuspSubmodule_inf_archCutSubmodule_ne_bot K c u d₁ d₂ T
      hc hd₁ hcov R.centralChar Θ.level Θ.level_ne_bot R.exceptionalSet Θ hne
  obtain ⟨ψ, hψmem, hψ0⟩ := (Submodule.ne_bot_iff _).1 htys
  obtain ⟨hψI, hψT⟩ := Submodule.mem_inf.1 hψmem

  have hdict := AutomorphicForm.isotypicCuspSubmodule_inf_archCutSubmodule_le_iSup_isCuspConstituent K
    c u d₁ d₂ T hd hcov R.centralChar Θ.level R.exceptionalSet tys Θ
  obtain ⟨𝒱, h𝒱, hle⟩ := AutomorphicForm.exists_finset_isCuspConstituent_le_iSup_of_cuspConstituentMeets K
    c u d₁ d₂ T hd hcov R.centralChar Θ.level Θ.level_ne_bot R.exceptionalSet Θ
  have hsupeq : (⨆ W ∈ 𝒱, W) ≤ 𝒱.sup id := by
    rw [Finset.sup_eq_iSup]
    exact le_rfl
  have h2 := hdict.trans (iSup_le fun V => iSup_le fun hV => (hle V hV.1 hV.2.1).trans hsupeq)
  have hmem : ψ ∈ 𝒱.sup id := h2 hψmem

  obtain ⟨V, hV𝒱, hVne⟩ :=
    LanglandsTunnell.exists_mem_finset_inf_isotypicCuspSubmodule_inf_archCutSubmodule_ne_bot_of_mem_sup K
      c u d₁ d₂ T R.centralChar Θ.level R.exceptionalSet Θ tys 𝒱 h𝒱 ψ hmem hψI hψT hψ0
  obtain ⟨φ, hφmem, hφ0⟩ := (Submodule.ne_bot_iff _).1 hVne
  obtain ⟨hφVI, hφT⟩ := Submodule.mem_inf.1 hφmem
  obtain ⟨hφV, hφI⟩ := Submodule.mem_inf.1 hφVI

  have hiso := AutomorphicForm.isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule K _ _ _
    R.centralChar Θ.level R.exceptionalSet Θ φ hφI hφ0
  exact ⟨R.centralChar, R.exceptionalSet, tys, V, φ, h𝒱 V hV𝒱, hφV, hφ0, hiso, hφT⟩

/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AdicCompletion_isNoetherianRing_and_exists_isLocalRing_maximalIdeal_eq_map_of_isMaximal
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`; 1 `#print axioms` audit command(s) (with their `#guard_msgs` expectations) are removed (diagnostics only, no declaration).
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AdicCompletionLocalRing
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Theorems.Thm_AdicCompletion_isNoetherianRing_of_isNoetherianRing
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AdicCompletion_isNoetherianRing_and_exists_isLocalRing_maximalIdeal_eq_map_of_isMaximal

set_option autoImplicit false

theorem solution
    {C : Type*} [CommRing C] [IsNoetherianRing C] (𝔫 : Ideal C) [𝔫.IsMaximal] :
    IsNoetherianRing (AdicCompletion 𝔫 C) ∧
    ∃ _ : IsLocalRing (AdicCompletion 𝔫 C),
      IsLocalRing.maximalIdeal (AdicCompletion 𝔫 C) = 𝔫.map (algebraMap C (AdicCompletion 𝔫 C)) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal (AdicCompletion 𝔫 C)) (AdicCompletion 𝔫 C) ∧
      (IsLocalRing.maximalIdeal (AdicCompletion 𝔫 C)).comap (algebraMap C (AdicCompletion 𝔫 C)) = 𝔫 ∧
      Function.Surjective ((IsLocalRing.residue (AdicCompletion 𝔫 C)).comp (algebraMap C (AdicCompletion 𝔫 C))) := by
  classical

  have hfg : 𝔫.FG := IsNoetherian.noetherian 𝔫
  haveI hN : IsNoetherianRing (AdicCompletion 𝔫 C) :=
    AdicCompletion.isNoetherianRing_of_isNoetherianRing 𝔫

  haveI hcM : IsAdicComplete (𝔫.map (algebraMap C (AdicCompletion 𝔫 C))) (AdicCompletion 𝔫 C) :=
    (IsAdicComplete.map_algebraMap_iff 𝔫 (AdicCompletion 𝔫 C)).mpr (AdicCompletion.isAdicComplete hfg)

  have hker : RingHom.ker ((Ideal.quotEquivOfEq (pow_one 𝔫)).toRingHom.comp
      (AdicCompletion.evalₐ 𝔫 1).toRingHom) = 𝔫.map (algebraMap C (AdicCompletion 𝔫 C)) := by
    rw [← RingHom.comap_ker, RingEquiv.toRingHom_eq_coe, RingHom.ker_coe_equiv, ← RingHom.ker,
      show RingHom.ker (AdicCompletion.evalₐ 𝔫 1).toRingHom = RingHom.ker (AdicCompletion.evalₐ 𝔫 1)
        from rfl,
      AdicCompletion.ker_evalₐ_eq_map_pow 𝔫 hfg 1, pow_one]
  have hsurj1 : Function.Surjective ((Ideal.quotEquivOfEq (pow_one 𝔫)).toRingHom.comp
      (AdicCompletion.evalₐ 𝔫 1).toRingHom) :=
    (Ideal.quotEquivOfEq (pow_one 𝔫)).surjective.comp (AdicCompletion.surjective_evalₐ 𝔫 1)
  haveI hmaxM : (𝔫.map (algebraMap C (AdicCompletion 𝔫 C))).IsMaximal := by
    letI := Ideal.Quotient.field 𝔫
    rw [← hker]
    exact RingHom.ker_isMaximal_of_surjective _ hsurj1

  haveI hloc : IsLocalRing (AdicCompletion 𝔫 C) :=
    isLocalRing_of_isAdicComplete_maximal (𝔫.map (algebraMap C (AdicCompletion 𝔫 C)))
  have hmax : IsLocalRing.maximalIdeal (AdicCompletion 𝔫 C)
      = 𝔫.map (algebraMap C (AdicCompletion 𝔫 C)) :=
    (IsLocalRing.eq_maximalIdeal hmaxM).symm
  refine ⟨hN, hloc, hmax, hmax ▸ hcM, ?_, ?_⟩
  ·
    rw [hmax]
    refine (Ideal.IsMaximal.eq_of_le inferInstance ?_ Ideal.le_comap_map).symm
    exact Ideal.comap_ne_top _ hmaxM.ne_top
  ·
    intro q
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨c, y, hy, rfl⟩ := AdicCompletion.exists_eq_algebraMap_add 𝔫 hfg 1 x
    refine ⟨c, ?_⟩
    rw [RingHom.comp_apply, IsLocalRing.residue_def]
    refine Ideal.Quotient.eq.mpr ?_
    rw [sub_add_cancel_left, neg_mem_iff, hmax]
    simpa only [pow_one] using hy

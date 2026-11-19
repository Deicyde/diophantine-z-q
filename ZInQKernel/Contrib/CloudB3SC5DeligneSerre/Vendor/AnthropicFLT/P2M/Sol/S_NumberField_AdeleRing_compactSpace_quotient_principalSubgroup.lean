/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_NumberField_AdeleRing_compactSpace_quotient_principalSubgroup (git blob 41ae33ed80e8eeb93068150c8d5195e75eee1e27, sha256 d1af1e0e6e9e7ba37030085080cd7f52bfdc986302100bab6da8c072e02086d5).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_NumberField_AdeleRing_compactSpace_quotient_principalSubgroup

set_option Elab.async false
set_option autoImplicit false

open NumberField NumberField.AdelicBox

theorem solution (F : Type) [Field F] [NumberField F] :
    CompactSpace (AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F) := by
  obtain ⟨C, hC, hsub⟩ := exists_isCompact_adelicBox_subset F
  rw [← isCompact_univ_iff]

  have hcont : Continuous
      (QuotientAddGroup.mk (s := AdeleRing.principalSubgroup (𝓞 F) F)) :=
    continuous_quot_mk
  have hsurj : (QuotientAddGroup.mk (s := AdeleRing.principalSubgroup (𝓞 F) F)) '' C
      = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro y

    obtain ⟨x, rfl⟩ := Quot.exists_rep y
    obtain ⟨k, hk, -⟩ := existsUnique_algebraMap_add_mem_adelicBox F x
    refine ⟨algebraMap F (AdeleRing (𝓞 F) F) k + x, hsub hk, ?_⟩

    refine (QuotientAddGroup.eq (s := AdeleRing.principalSubgroup (𝓞 F) F)).mpr ?_
    refine ⟨-k, ?_⟩
    simp only [map_neg]
    abel
  rw [← hsurj]
  exact hC.image hcont

/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_AlgebraicCurve_RegularDifferentials (git blob 1f5af49d5c62203b175bb837c4f1a81293a25a0b, sha256 634da3fc59c6d4ad98f791efad145447cb34350f786d6a5c1cafa687002591a8).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_CanonicalDivisor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

namespace Place

variable {K F}

theorem exists_ord_eq_one_and_dCoord_eq (v : Place K F) :
    ∃ π : F, v.ord π = 1 ∧ v.dCoord = D K F π := by
  refine ⟨((IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose : F), ?_, rfl⟩
  exact v.ord_coe_irreducible
    (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose_spec

end Place

def regularDifferentials : Submodule K Ω[F⁄K] where
  carrier := {ω | ∀ v : Place K F, ∃ f ∈ v.toValuationSubring, ω = f • v.dCoord}
  zero_mem' v := ⟨0, v.toValuationSubring.zero_mem, by rw [zero_smul]⟩
  add_mem' {ω η} hω hη v := by
    obtain ⟨f, hf, rfl⟩ := hω v
    obtain ⟨g, hg, hη'⟩ := hη v
    exact ⟨f + g, v.toValuationSubring.add_mem _ _ hf hg, by rw [hη', add_smul]⟩
  smul_mem' c {ω} hω v := by
    obtain ⟨f, hf, rfl⟩ := hω v
    refine ⟨algebraMap K F c * f, v.toValuationSubring.mul_mem _ _ (v.algebraMap_mem' c) hf, ?_⟩
    rw [mul_smul, algebraMap_smul]

variable {K F} in
theorem mem_regularDifferentials_iff {ω : Ω[F⁄K]} :
    ω ∈ regularDifferentials K F ↔
      ∀ v : Place K F, ∃ f ∈ v.toValuationSubring, ω = f • v.dCoord :=
  Iff.rfl

end AlgebraicCurve

end

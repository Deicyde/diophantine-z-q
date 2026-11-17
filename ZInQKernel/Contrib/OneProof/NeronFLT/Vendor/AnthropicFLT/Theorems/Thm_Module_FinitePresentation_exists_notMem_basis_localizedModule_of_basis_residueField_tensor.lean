/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Module_FinitePresentation_exists_notMem_basis_localizedModule_of_basis_residueField_tensor
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_Module_FinitePresentation_exists_notMem_basis_localizedModule_of_basis_residueField_tensor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open TensorProduct

universe u

theorem Module.FinitePresentation.exists_notMem_basis_localizedModule_of_basis_residueField_tensor
    {T : Type u} [CommRing T] {M : Type u} [AddCommGroup M] [Module T M] [Module.FinitePresentation T M]
    (p : Ideal T) [hp : p.IsPrime] (hfree : (⟨p, hp⟩ : PrimeSpectrum T) ∈ Module.freeLocus T M)
    {ι : Type} [Finite ι] (m : ι → M)
    (b : Module.Basis ι p.ResidueField (p.ResidueField ⊗[T] M)) (hb : ∀ i, b i = (1 : p.ResidueField) ⊗ₜ[T] m i) :
    ∃ (t : T) (_ : t ∉ p)
      (b' : Module.Basis ι (Localization.Away t) (LocalizedModule (Submonoid.powers t) M)),
      ∀ i, b' i = LocalizedModule.mkLinearMap (Submonoid.powers t) M (m i) := by p2m_exact_reverting @_root_.P2MW.S_Module_FinitePresentation_exists_notMem_basis_localizedModule_of_basis_residueField_tensor.solution

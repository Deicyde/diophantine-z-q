/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_KaehlerDifferential_nonempty_baseChange_linearEquiv_quotient_span_tmul_D_of_surjective
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_KaehlerDifferential_nonempty_baseChange_linearEquiv_quotient_span_tmul_D_of_surjective

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open TensorProduct KaehlerDifferential

universe u

theorem KaehlerDifferential.nonempty_baseChange_linearEquiv_quotient_span_tmul_D_of_surjective
    {R C A R' : Type u} [CommRing R] [CommRing C] [CommRing A] [CommRing R']
    [Algebra R C] [Algebra R A] [Algebra C A] [IsScalarTower R C A]
    (hsurj : Function.Surjective (algebraMap C A))
    [Algebra A R'] [Algebra C R'] [IsScalarTower C A R'] :
    Nonempty ((R' ⊗[A] Ω[A⁄R]) ≃ₗ[R']
      ((R' ⊗[C] Ω[C⁄R]) ⧸ Submodule.span R'
        (Set.range fun f : RingHom.ker (algebraMap C A) => (1 : R') ⊗ₜ[C] D R C (f : C)))) := by p2m_exact_reverting @_root_.P2MW.S_KaehlerDifferential_nonempty_baseChange_linearEquiv_quotient_span_tmul_D_of_surjective.solution

/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NeronModelInfra_le_sq_of_linearIndependent_tmul_D_of_forall_indexOne
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_NeronModelInfra_WeakNeronModel
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_NeronModelInfra_le_sq_of_linearIndependent_tmul_D_of_forall_indexOne

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open TensorProduct KaehlerDifferential NeronModelInfra

universe u

theorem NeronModelInfra.le_sq_of_linearIndependent_tmul_D_of_forall_indexOne
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π})
    {C A : Type u} [CommRing C] [CommRing A] [Algebra R C] [Algebra R A] [Algebra C A] [IsScalarTower R C A]
    (hsurj : Function.Surjective (algebraMap C A))
    {n : ℕ} (z : Fin n → C)
    (hIJ : RingHom.ker (algebraMap C A) ≤ Ideal.span (insert (algebraMap R C π) (Set.range z)))
    (hlin : LinearIndependent (C ⧸ Ideal.span (insert (algebraMap R C π) (Set.range z)))
      fun j : Fin n => (1 : C ⧸ Ideal.span (insert (algebraMap R C π) (Set.range z))) ⊗ₜ[C]
        D R A (algebraMap C A (z j)))
    (hN : ∀ g : C,
      (∀ (R'' : Type u) [CommRing R''] [IsDomain R''] [IsDiscreteValuationRing R''] [Algebra R R'']
        [IsLocalHom (algebraMap R R'')], IsIndexOneExtension R R'' →
        ∀ c : C →ₐ[R] R'', RingHom.ker (algebraMap C A) ≤ RingHom.ker c.toRingHom →
          Ideal.span (insert (algebraMap R C π) (Set.range z)) ≤ (IsLocalRing.maximalIdeal R'').comap c →
          g ∈ (IsLocalRing.maximalIdeal R'').comap c) →
      g ∈ Ideal.span (insert (algebraMap R C π) (Set.range z))) :
    RingHom.ker (algebraMap C A) ≤ Ideal.span (insert (algebraMap R C π) (Set.range z)) ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_le_sq_of_linearIndependent_tmul_D_of_forall_indexOne.solution

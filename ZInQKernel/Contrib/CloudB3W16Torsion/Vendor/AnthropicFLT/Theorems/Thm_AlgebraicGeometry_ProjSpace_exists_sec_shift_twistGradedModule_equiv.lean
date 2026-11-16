/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.exists_sec_shift_twistGradedModule_equiv
    {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
    (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) [IsAffineHom φ]
    (π : X ⟶ Spec (.of A)) (m : ℕ) :
    ∃ e : ∀ (I : Finset (Fin (N + 1))), I.Nonempty →
        (ProjSpaceCech.GradedModule.sec ((ProjSpace.twistGradedModule φ π).shift (m : ℤ)) I
          ≃ₗ[A] ProjSpace.twistObj π φ m (⨅ i ∈ I, ProjSpace.pullbackChart φ i)),
      ∀ (I J : Finset (Fin (N + 1))) (hI : I.Nonempty) (hIJ : I ⊆ J)
        (x : ProjSpaceCech.GradedModule.sec ((ProjSpace.twistGradedModule φ π).shift (m : ℤ)) I),
        e J (hI.mono hIJ) (ProjSpaceCech.GradedModule.secIncl _ hIJ x)
          = ProjSpace.twistRes π φ m
              (le_iInf fun i => le_iInf fun hi => (iInf_le _ i).trans (iInf_le _ (hIJ hi)) :
                (⨅ i ∈ J, ProjSpace.pullbackChart φ i) ≤ ⨅ i ∈ I, ProjSpace.pullbackChart φ i)
              (e I hI x) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.solution

/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_twoTermComplex_kerMapBaseChange_bijective_ofModules. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCech
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_twoTermComplex_kerMapBaseChange_bijective_ofModules

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.OModulePresheaf.exists_twoTermComplex_kerMapBaseChange_bijective_ofModules
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [IsProper f] [Flat f] (M : X.Modules)
    (htriv : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))
    (𝒰 : X.OrderedAffineCover) :
    ∃ (G : CoherentBaseChange.TwoTermComplex.{u, u} R)
      (ι0 : G.C0 →ₗ[R] (OModulePresheaf.ofModules f M).cochain 𝒰 0)
      (ι1 : G.C1 →ₗ[R] (OModulePresheaf.ofModules f M).cochain 𝒰 1)
      (comm : (OModulePresheaf.ofModules f M).d 𝒰 0 ∘ₗ ι0 = ι1 ∘ₗ G.d),
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        Function.Bijective
          (TwoChartCech.kerMapBaseChange G.d ((OModulePresheaf.ofModules f M).d 𝒰 0) ι0 ι1 comm A) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_twoTermComplex_kerMapBaseChange_bijective_ofModules.solution

/-
# H-76: the surjective Néron mapping property for abelian schemes over a DVR

The fixed statement is `ZInQ.Contrib.NeronC.NeronMappingAbelianSchemeSurj`
at cba8157f7d5d09a4a3c8462aba2f3245494a870e. This file does not change it.

Proof source: anthropics/fermats-last-theorem,
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_NeronModelInfra_NeronModelPropertyBundle_of_abelianSchemePropertyBundle.lean
and its complete extension-proof dependency closure, ported in `Vendor/`.
That source proves the full mapping property over an arbitrary DVR, for
arbitrary smooth test schemes and arbitrary generic-fibre scheme morphisms.
Its proof uses properness at codimension one and Weil's extension argument
(Bosch–Lütkebohmert–Raynaud, Néron Models, §1.2 Prop. 8 and §4.4 Thm. 1).

Changes (2026-11-14): bridged the source's scheme-morphism subtype to Mathlib
`Over` morphisms, supplied its group law from the existing `GrpObj`, and
specialized its stronger theorem to the exact fixed H-76 statement.
See NOTICE, ATTRIBUTION.md and LICENSE for source attribution and licenses.
-/
import ZInQKernel.Contrib.NeronC.NMPInjective
import ZInQKernel.Contrib.CloudW03NeronSurj.Basic
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.P2M.Sol.S_NeronModelInfra_NeronModelPropertyBundle_of_abelianSchemePropertyBundle

set_option autoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace ZInQ.Contrib.NeronC

/-- The exact fixed H-76 proposition, with no additional hypotheses. -/
theorem NeronMappingAbelianSchemeSurj_proof : NeronMappingAbelianSchemeSurj.{u} := by
  intro K _ O _ 𝒜 ℬ _ _
  haveI : Smooth 𝒜.X.hom := PkgI2.IsAbelianScheme.smooth
  haveI : Smooth ℬ.X.hom := PkgI2.IsAbelianScheme.smooth
  haveI : IsProper ℬ.X.hom := PkgI2.IsAbelianScheme.proper
  haveI : GeometricallyConnected ℬ.X.hom := PkgI2.IsAbelianScheme.geomConnected
  haveI : GrpObj (Over.mk ℬ.X.hom) := by
    change GrpObj ℬ.X
    infer_instance
  let hℬ : GoodReductionJacobian.AbelianSchemePropertyBundle O ℬ.X.hom :=
    { smooth := inferInstance
      proper := inferInstance
      connectedFibres := fun s => ℬ.X.hom.isConnected_preimage_singleton s
      hasGroupLaw := ⟨GoodReductionJacobian.relativeGroupLawOfGrpObj O ℬ.X.hom⟩ }
  have hN := P2MW.S_NeronModelInfra_NeronModelPropertyBundle_of_abelianSchemePropertyBundle.solution
    O K hℬ
  intro uK
  let uK' : NeronModelInfra.SchemeHomOver
      (pullback.snd 𝒜.X.hom (NeronModelInfra.specGenericFibreInclusion O K))
      (pullback.snd ℬ.X.hom (NeronModelInfra.specGenericFibreInclusion O K)) :=
    ⟨uK.left, Over.w uK⟩
  obtain ⟨φ, hφ⟩ := (hN.neronMapping 𝒜.X.left 𝒜.X.hom inferInstance).2 uK'
  refine ⟨Over.homMk φ.1 φ.2, ?_⟩
  ext1
  exact congrArg Subtype.val hφ

end ZInQ.Contrib.NeronC

#print axioms ZInQ.Contrib.NeronC.NeronMappingAbelianSchemeSurj_proof

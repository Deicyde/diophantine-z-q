/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_GoodReductionJacobian_abelianSchemePropertyBundle_fibreStr
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_JacJ1Iface
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_GoodReductionJacobian_RelativeGroupLawFibre
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SchemeFibreEndo
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_GoodReductionJacobian_abelianSchemePropertyBundle_fibreStr

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem solution
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (hA : AbelianSchemePropertyBundle R f) (s : (Spec (CommRingCat.of R) : Scheme.{u})) :
    AbelianSchemePropertyBundle (RelativeGroupLaw.baseResidueField s) (RelativeGroupLaw.fibreStr f s) := by
  haveI : Smooth f := hA.smooth
  haveI : IsProper f := hA.proper
  refine ⟨inferInstance, inferInstance, ?_, ⟨(Classical.choice hA.hasGroupLaw).fibre s⟩⟩
  intro s'

  have huniv : (RelativeGroupLaw.fibreStr f s).base ⁻¹' {s'} = Set.univ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  rw [huniv]

  have hconn : _root_.IsConnected (f.base ⁻¹' {s}) := hA.connectedFibres s
  haveI : ConnectedSpace (f.base ⁻¹' {s}) := isConnected_iff_connectedSpace.mp hconn
  have h1 : _root_.IsConnected (Set.univ : Set (f.fiber s)) := by
    have h := (isConnected_univ (α := f.base ⁻¹' {s})).image _ (f.fiberHomeo s).symm.continuous.continuousOn
    rwa [Set.image_univ_of_surjective (f.fiberHomeo s).symm.surjective] at h
  exact h1

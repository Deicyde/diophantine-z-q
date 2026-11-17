/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_GoodReductionJacobian_AbelianSchemePropertyBundle_isIntegral_of_field. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_JacJ1Iface
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_IsRegularLocalRing_isDomain
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_isIntegral_of_field

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
universe u

theorem solution {k : Type u} [Field k] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of k)}
    (hJ : AbelianSchemePropertyBundle k f) : IsIntegral J := by
  haveI := hJ.smooth
  haveI : LocallyOfFiniteType f := inferInstance
  haveI : IsLocallyNoetherian (Spec (CommRingCat.of k)) := inferInstance
  haveI : IsLocallyNoetherian J := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : ConnectedSpace J := by
    rw [connectedSpace_iff_univ]
    have hc := hJ.connectedFibres default
    have heq : f.base ⁻¹' {(default : Spec (CommRingCat.of k))} = Set.univ := by
      ext y; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      exact Subsingleton.elim _ _
    rwa [heq] at hc
  exact AlgebraicGeometry.isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk J
    fun x => by
      haveI := AlgebraicGeometry.Smooth.isRegularLocalRing_stalkFLT (f := f) x
      exact IsRegularLocalRing.isDomain _

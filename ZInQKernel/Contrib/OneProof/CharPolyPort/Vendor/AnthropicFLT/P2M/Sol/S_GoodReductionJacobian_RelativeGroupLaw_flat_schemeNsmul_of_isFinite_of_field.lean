/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_flat_schemeNsmul_of_isFinite_of_field. Apache-2.0.
Modification notice (CloudB3 Worker13, 2026-11-15/16): ported to Lean 4.35.0 / Mathlib v4.35.0
(namespace-wrapped port on origin/cloud-b3/w13-recovery).
Modified for the Z-in-Q kernel (charpoly-port, 2026-11-17): the Worker13 port unwrapped into the
CloudB3W16Torsion conventions (original declaration namespaces; imports relocated to the
CloudB3W16Torsion vendor; the FLT-suffixed renames of CloudB3W16Torsion/NOTICE.md applied; port
shim commands removed). Mathematical statements and proofs retained, subject to Lean 4.35 adaptations
listed in scratch/charpoly-port/log.md.
Full original notices/credits: LICENSE, NOTICE.upstream, ATTRIBUTION.upstream.md in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_JacJ1Iface
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_Module_Flat_of_isLocalHom_of_isRegularLocalRing_of_ringKrullDim_quotient_eq_zero
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_IsFinite_ringKrullDim_stalk_quotient_eq_zero
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ringKrullDim_stalk_eq_of_isFinite_endomorphism
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_isIntegral_of_field
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_flat_schemeNsmul_of_isFinite_of_field

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing
universe u

theorem solution
    {k : Type u} [Field k] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of k)}
    (L : RelativeGroupLaw k f) (hJ : AbelianSchemePropertyBundle k f)
    (n : ℕ) (hn : 0 < n) (hfin : IsFinite (L.schemeNsmul n)) :
    Flat (L.schemeNsmul n) := by
  haveI := hJ.smooth
  haveI : LocallyOfFiniteType f := inferInstance
  haveI : IsLocallyNoetherian (Spec (CommRingCat.of k)) := inferInstance
  haveI hnoeth : IsLocallyNoetherian J := LocallyOfFiniteType.isLocallyNoetherian f
  haveI hint : IsIntegral J := hJ.isIntegral_of_field
  rw [AlgebraicGeometry.Flat.iff_flat_stalkMap]
  intro x
  algebraize [((L.schemeNsmul n).stalkMap x).hom]
  haveI : IsRegularLocalRing (J.presheaf.stalk x) :=
    AlgebraicGeometry.Smooth.isRegularLocalRing_stalkFLT (f := f) x
  haveI : IsRegularLocalRing (J.presheaf.stalk ((L.schemeNsmul n).base x)) :=
    AlgebraicGeometry.Smooth.isRegularLocalRing_stalkFLT (f := f) ((L.schemeNsmul n).base x)
  haveI : IsNoetherianRing (J.presheaf.stalk x) := inferInstance
  haveI : IsLocalHom (algebraMap
      ↑(J.presheaf.stalk ((L.schemeNsmul n).base x)) ↑(J.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom ((L.schemeNsmul n).stalkMap x).hom)

  have hfib : ringKrullDim (↑(J.presheaf.stalk x) ⧸
      (maximalIdeal ↑(J.presheaf.stalk ((L.schemeNsmul n).base x))).map
        (algebraMap ↑(J.presheaf.stalk ((L.schemeNsmul n).base x)) ↑(J.presheaf.stalk x))) = 0 :=
    AlgebraicGeometry.IsFinite.ringKrullDim_stalk_quotient_eq_zero (L.schemeNsmul n) x

  have hdim : ringKrullDim (J.presheaf.stalk x) =
      ringKrullDim (J.presheaf.stalk ((L.schemeNsmul n).base x)) :=
    AlgebraicGeometry.ringKrullDim_stalk_eq_of_isFinite_endomorphism
      (f := f) (L.schemeNsmul n) (L.schemeNsmul_over n) x

  exact Module.Flat.of_isLocalHom_of_isRegularLocalRing_of_ringKrullDim_quotient_eq_zero
      ↑(J.presheaf.stalk ((L.schemeNsmul n).base x)) ↑(J.presheaf.stalk x) hfib hdim

end S_GoodReductionJacobian_RelativeGroupLaw_flat_schemeNsmul_of_isFinite_of_field
end P2MW


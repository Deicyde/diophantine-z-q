/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_schemeNsmul_of_isUnit. Apache-2.0.
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
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_GoodReductionJacobian_RelativeGroupLawFibre
import ZInQKernel.Contrib.OneProof.CharPolyPort.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SchemeFibreEndo
import ZInQKernel.Contrib.OneProof.CharPolyPort.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_locallyQuasiFinite_of_forall_locallyQuasiFinite_schemeFibreEndo
import ZInQKernel.Contrib.OneProof.CharPolyPort.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_fibre_schemeNsmul_eq_schemeFibreEndo
import ZInQKernel.Contrib.OneProof.CharPolyPort.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_abelianSchemePropertyBundle_fibreStr
import ZInQKernel.Contrib.OneProof.CharPolyPort.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_fibre_mul_comm
import ZInQKernel.Contrib.OneProof.CharPolyPort.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_schemeNsmul_of_isUnit
import ZInQKernel.Contrib.OneProof.CharPolyPort.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_flat_schemeNsmul_of_isFinite_of_abelianSchemePropertyBundle
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_schemeNsmul_of_isUnit

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (hJ : AbelianSchemePropertyBundle R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    (n : ℕ) (hn : IsUnit (n : R)) :
    IsFinite (L.schemeNsmul n) ∧ Flat (L.schemeNsmul n) := by
  haveI : IsProper f := hJ.proper

  have hlqf : LocallyQuasiFinite (L.schemeNsmul n) := by
    refine AlgebraicGeometry.locallyQuasiFinite_of_forall_locallyQuasiFinite_schemeFibreEndo f
      (L.schemeNsmul n) (L.schemeNsmul_over n) ?_
    intro s
    rw [← RelativeGroupLaw.fibre_schemeNsmul_eq_schemeFibreEndo L s n]
    have hfib := GoodReductionJacobian.abelianSchemePropertyBundle_fibreStr hJ s
    haveI : Smooth (RelativeGroupLaw.fibreStr f s) := hfib.smooth
    haveI : LocallyOfFiniteType (RelativeGroupLaw.fibreStr f s) := inferInstance
    have hu : IsUnit ((n : ℕ) : RelativeGroupLaw.baseResidueField s) := by
      have h := hn.map (((Spec (CommRingCat.of R)).Γevaluation s).hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
      simpa only [map_natCast] using h
    exact RelativeGroupLaw.locallyQuasiFinite_schemeNsmul_of_isUnit (L.fibre s)
      (fun t' x y => RelativeGroupLaw.fibre_mul_comm L hcomm s t' x y) n hu
  haveI := hlqf
  haveI : IsProper (L.schemeNsmul n) := by
    have : IsProper (L.schemeNsmul n ≫ f) := by rw [L.schemeNsmul_over]; infer_instance
    exact IsProper.of_comp _ f
  have hfin : IsFinite (L.schemeNsmul n) := IsFinite.of_isProper_of_locallyQuasiFinite _
  refine ⟨hfin, ?_⟩

  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · have h01 : (0 : R) = 1 := isUnit_zero_iff.mp (by simpa using hn)
    haveI : Subsingleton R := subsingleton_of_zero_eq_one h01
    haveI : IsEmpty (Spec (CommRingCat.of R) : Scheme.{u}) :=
      inferInstanceAs (IsEmpty (PrimeSpectrum R))
    haveI : IsEmpty J := Function.isEmpty f.base
    infer_instance
  · exact RelativeGroupLaw.flat_schemeNsmul_of_isFinite_of_abelianSchemePropertyBundle L hJ
      (fun t x y => hcomm t x y) n hpos hfin

end S_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_schemeNsmul_of_isUnit
end P2MW


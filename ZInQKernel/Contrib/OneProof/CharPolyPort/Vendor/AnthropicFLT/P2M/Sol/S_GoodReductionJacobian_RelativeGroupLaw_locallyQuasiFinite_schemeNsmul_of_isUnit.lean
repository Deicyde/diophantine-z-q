/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_schemeNsmul_of_isUnit. Apache-2.0.
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
import ZInQKernel.Contrib.OneProof.CharPolyPort.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_LocallyQuasiFinite_of_formallyUnramified_of_locallyOfFiniteType
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_schemeNsmul_of_forall_sqZero
import ZInQKernel.Contrib.OneProof.CharPolyPort.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_eq_one_of_sqZero_of_nsmul_eq_one_of_isUnit
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_schemeNsmul_of_isUnit

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem solution
    {R : Type u} [Field R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    [LocallyOfFiniteType f] (G : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (n : ℕ) (hn : IsUnit (n : R)) :
    LocallyQuasiFinite (G.schemeNsmul n) := by
  haveI : FormallyUnramified (G.schemeNsmul n) :=
    GoodReductionJacobian.RelativeGroupLaw.formallyUnramified_schemeNsmul_of_forall_sqZero G hcomm n
      (fun R' S' φ hφ hker t k hk hnk =>
        GoodReductionJacobian.RelativeGroupLaw.eq_one_of_sqZero_of_nsmul_eq_one_of_isUnit
          G n hn R' S' φ hφ hker t k hk hnk)
  haveI : LocallyOfFiniteType (G.schemeNsmul n) := by
    haveI h : LocallyOfFiniteType (G.schemeNsmul n ≫ f) := by
      rw [G.schemeNsmul_over]
      infer_instance
    exact AlgebraicGeometry.locallyOfFiniteType_of_comp (G.schemeNsmul n) f
  exact AlgebraicGeometry.LocallyQuasiFinite.of_formallyUnramified_of_locallyOfFiniteType _

end S_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_schemeNsmul_of_isUnit
end P2MW


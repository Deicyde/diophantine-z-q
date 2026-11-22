/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_endDegree_schemeHomOverComp_of_isFinite_of_flat. Apache-2.0.
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
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_finrank_comp_of_finrank_eq_const
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_endDegree_schemeHomOverComp_of_isFinite_of_flat

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace P2mDegMul

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}

theorem endDegree_eq_finrank_unit (L : RelativeGroupLaw K f) (β : SchemeHomOver f f)
    [IsFinite β.1] [Flat β.1] :
    L.endDegree β =
      β.1.finrank ((L.one (𝟙 (Spec (CommRingCat.of K)))).1 (IsLocalRing.closedPoint K)) := by
  haveI : IsFinite (L.endKerStr β) := inferInstance
  rw [RelativeGroupLaw.endDegree_of_isFinite]
  exact Scheme.Hom.finrank_pullback_snd β.1 _ _

theorem finrank_eq_finrank [LocallyOfFiniteType f] (β : SchemeHomOver f f) [IsFinite β.1]
    [Flat β.1] [PreconnectedSpace A] (x y : A) : β.1.finrank x = β.1.finrank y := by
  haveI : IsLocallyNoetherian A := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : LocallyOfFinitePresentation β.1 := inferInstance
  exact (Scheme.Hom.isLocallyConstant_finrank β.1).apply_eq_of_preconnectedSpace x y

theorem endDegree_eq_finrank [LocallyOfFiniteType f] (L : RelativeGroupLaw K f)
    (β : SchemeHomOver f f) [IsFinite β.1] [Flat β.1] [PreconnectedSpace A] (x : A) :
    L.endDegree β = β.1.finrank x := by
  rw [endDegree_eq_finrank_unit L β]
  exact finrank_eq_finrank β _ x

theorem main [LocallyOfFiniteType f] [PreconnectedSpace A] (L : RelativeGroupLaw K f)
    (β γ : SchemeHomOver f f) [IsFinite β.1] [Flat β.1] [IsFinite γ.1] [Flat γ.1] :
    L.endDegree (NeronModelInfra.schemeHomOverComp β γ) = L.endDegree β * L.endDegree γ := by

  haveI hfin : IsFinite (NeronModelInfra.schemeHomOverComp β γ).1 :=
    inferInstanceAs (IsFinite (β.1 ≫ γ.1))
  haveI hfl : Flat (NeronModelInfra.schemeHomOverComp β γ).1 :=
    inferInstanceAs (Flat (β.1 ≫ γ.1))

  let x : A := (L.one (𝟙 (Spec (CommRingCat.of K)))).1 (IsLocalRing.closedPoint K)
  rw [endDegree_eq_finrank L (NeronModelInfra.schemeHomOverComp β γ) x,
    endDegree_eq_finrank L γ x]
  have h := Scheme.Hom.finrank_comp_of_finrank_eq_const β.1 γ.1 (L.endDegree β)
    (fun y => (endDegree_eq_finrank L β y).symm) x
  exact h

end P2mDegMul

theorem solution
    (K : Type u) [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f]
    [PreconnectedSpace A] (L : RelativeGroupLaw K f) (β γ : SchemeHomOver f f)
    [IsFinite β.1] [Flat β.1] [IsFinite γ.1] [Flat γ.1] :
    L.endDegree (NeronModelInfra.schemeHomOverComp β γ) = L.endDegree β * L.endDegree γ :=
  P2mDegMul.main L β γ

end

end S_GoodReductionJacobian_RelativeGroupLaw_endDegree_schemeHomOverComp_of_isFinite_of_flat
end P2MW


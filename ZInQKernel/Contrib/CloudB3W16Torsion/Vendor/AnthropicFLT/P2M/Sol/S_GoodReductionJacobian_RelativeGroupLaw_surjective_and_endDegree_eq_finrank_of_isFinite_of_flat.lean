/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_surjective_and_endDegree_eq_finrank_of_isFinite_of_flat. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_JacJ1Iface
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_surjective_and_endDegree_eq_finrank_of_isFinite_of_flat

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace P2mKerRank

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}

theorem endDegree_eq_finrank_unit (L : RelativeGroupLaw K f) (β : SchemeHomOver f f)
    [IsFinite β.1] [Flat β.1] :
    L.endDegree β =
      β.1.finrank ((L.one (𝟙 (Spec (CommRingCat.of K)))).1 (IsLocalRing.closedPoint K)) := by
  haveI : IsFinite (L.endKerStr β) := inferInstance
  rw [RelativeGroupLaw.endDegree_of_isFinite]
  exact Scheme.Hom.finrank_pullback_snd β.1 _ _

theorem finrank_eq_finrank [LocallyOfFiniteType f] (β : SchemeHomOver f f) [IsFinite β.1] [Flat β.1]
    [PreconnectedSpace A] (x y : A) : β.1.finrank x = β.1.finrank y := by
  haveI : IsLocallyNoetherian A := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : LocallyOfFinitePresentation β.1 := inferInstance
  have h := Scheme.Hom.isLocallyConstant_finrank β.1
  exact h.apply_eq_of_preconnectedSpace x y

theorem endDegree_eq_finrank [LocallyOfFiniteType f] (L : RelativeGroupLaw K f) (β : SchemeHomOver f f)
    [IsFinite β.1] [Flat β.1] [PreconnectedSpace A] (x : A) : L.endDegree β = β.1.finrank x := by
  rw [endDegree_eq_finrank_unit L β]
  exact finrank_eq_finrank β _ x

theorem one_le_finrank [LocallyOfFiniteType f] (β : SchemeHomOver f f) [IsFinite β.1] [Flat β.1]
    [PreconnectedSpace A] (x : A) : 1 ≤ β.1.finrank x := by
  rw [finrank_eq_finrank β x (β.1 x)]
  exact Scheme.Hom.one_le_finrank_map β.1 x

theorem surjective [LocallyOfFiniteType f] (β : SchemeHomOver f f) [IsFinite β.1] [Flat β.1]
    [PreconnectedSpace A] : Function.Surjective β.1 := by
  have h : Surjective β.1 := (Scheme.Hom.one_le_finrank_iff_surjective β.1).mp fun x =>
    one_le_finrank β x
  exact h.surj

theorem main [LocallyOfFiniteType f] (L : RelativeGroupLaw K f) (β : SchemeHomOver f f)
    [IsFinite β.1] [Flat β.1] [PreconnectedSpace A] :
    Function.Surjective β.1 ∧ 0 < L.endDegree β ∧ ∀ x : A, L.endDegree β = β.1.finrank x := by
  refine ⟨surjective β, ?_, endDegree_eq_finrank L β⟩
  rw [endDegree_eq_finrank_unit L β]
  exact one_le_finrank β _

end P2mKerRank

theorem solution
    (K : Type u) [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f]
    [PreconnectedSpace A] (L : RelativeGroupLaw K f) (β : SchemeHomOver f f)
    [IsFinite β.1] [Flat β.1] :
    Function.Surjective β.1 ∧ 0 < L.endDegree β ∧
      ∀ x : A, L.endDegree β = Scheme.Hom.finrank β.1 x :=
  P2mKerRank.main L β

end

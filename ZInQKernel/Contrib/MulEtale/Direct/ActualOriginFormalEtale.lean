/-
Multiplication-etale construction: ActualOriginFormalEtale.
The mathematical declarations below are part of the checked H-101 contribution.
-/
import ZInQKernel.Contrib.MulEtale.Direct.ActualOriginRelativeTransport
import ZInQKernel.Contrib.MulEtale.Direct.LocalJoinChain
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.RingTheory.RingHom.EssFiniteType
import Mathlib.RingTheory.EssentialFiniteness

open CategoryTheory AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj H101DirectFieldRoute.ActualTransport

noncomputable section

namespace H101DirectFieldRoute.ActualTransport

universe u
variable {X B : Scheme.{u}}

/-- Actual native smoothness of the structural stalk map. -/
theorem structuralStalk_formallySmooth (p : X ⟶ B) [Smooth p] (x : X) :
    (p.stalkMap x).hom.FormallySmooth := by
  have hx : x ∈ p.smoothLocus := by rw [p.smoothLocus_eq_top]; trivial
  exact (Scheme.Hom.mem_smoothLocus).1 hx

/-- Actual composed structural map equals the native structural map after
precomposition with the canonical base-stalk iso. -/
theorem baseTargetHom_eq_iso_comp (p : X ⟶ B) (f : X ⟶ X) (x : X)
    (hbase : f ≫ p = p) :
    baseTargetHom p f x = (p.stalkMap x).hom.comp
      (baseStalkIso p f x hbase).hom.hom := by
  ext r
  exact baseComposite_apply p f x hbase r

/-- Formal smoothness for the ACTUAL composed R0 -> T0 algebra, not an
unrelated or assumed smooth multiplication map. -/
theorem composedBase_formallySmooth (p : X ⟶ B) [Smooth p]
    (f : X ⟶ X) (x : X) (hbase : f ≫ p = p) :
    (baseTargetHom p f x).FormallySmooth := by
  rw [baseTargetHom_eq_iso_comp p f x hbase]
  exact (RingHom.FormallySmooth.of_bijective
    (baseStalkIso p f x hbase).commRingCatIsoToRingEquiv.bijective).comp
      (structuralStalk_formallySmooth p x)

/-- Essential finite type for the ACTUAL composed base algebra. Finiteness of
the structural stalk map is native; the only preceding map is the canonical
base-stalk isomorphism, whose smoothness/finiteness is native and proved. -/
theorem composedBase_essFiniteType (p : X ⟶ B) [LocallyOfFiniteType p]
    (f : X ⟶ X) (x : X) (hbase : f ≫ p = p) :
    (baseTargetHom p f x).EssFiniteType := by
  rw [baseTargetHom_eq_iso_comp p f x hbase]
  let b : BaseStalk p f x →+* B.presheaf.stalk (p x) :=
    (baseStalkIso p f x hbase).hom.hom
  let a : B.presheaf.stalk (p x) →+* TargetStalk x := (p.stalkMap x).hom
  have hb : b.EssFiniteType :=
    (RingHom.FiniteType.of_surjective b
      (baseStalkIso p f x hbase).commRingCatIsoToRingEquiv.surjective).essFiniteType
  have ha : a.EssFiniteType := LocallyOfFiniteType.stalkMap p x
  change (a.comp b).EssFiniteType
  exact RingHom.EssFiniteType.comp hb ha

/-- The native actual stalk-map endpoint. The structural smoothness, essential
finite type, local-ring and cotangent-freeness inputs are all derived from p;
the final unit-multiplication theorem supplies H by the completed actual
canonical tangent/relative derivation transport. -/
theorem actualStalk_formallyEtale_of_restrictionBijection
    (p : X ⟶ B) [Smooth p] (f : X ⟶ X) (x : X) (hbase : f ≫ p = p)
    (H : Function.Bijective (actualRelativeRestriction p f x)) :
    (f.stalkMap x).hom.FormallyEtale := by
  haveI : Algebra.FormallySmooth (BaseStalk p f x) (SourceStalk f x) :=
    structuralStalk_formallySmooth p (f x)
  haveI : Algebra.FormallySmooth (BaseStalk p f x) (TargetStalk x) :=
    composedBase_formallySmooth p f x hbase
  haveI : Algebra.EssFiniteType (BaseStalk p f x) (SourceStalk f x) :=
    LocallyOfFiniteType.stalkMap p (f x)
  haveI : Algebra.EssFiniteType (BaseStalk p f x) (TargetStalk x) :=
    composedBase_essFiniteType p f x hbase
  change Algebra.FormallyEtale (SourceStalk f x) (TargetStalk x)
  exact H101DirectFieldRoute.formallyEtale_of_bijective_derivationRestriction
    (BaseStalk p f x) (SourceStalk f x) (TargetStalk x) H

/-- Exact source-only closed origin supplier for multiplication over ALL
fields, on the same given group scheme and its actual unit section. The native
output is RingHom.FormallyEtale on the ACTUAL f.stalkMap e, directly consumable
by LocalPromotion. No positive-index, char-zero, perfect-field, Noetherian-base,
Flat, wanted square or wanted cotangent-bijection assumption is added. -/
theorem unit_actualStalkMap_formallyEtale
    (k : Type u) [Field k] (G : Over (Spec (.of k))) [GrpObj G] [Smooth G.hom]
    (m : ℕ) (hm : IsUnit (m : k)) (s : Spec (.of k)) :
    ((𝟙 G ^ m : G ⟶ G).left.stalkMap ((η[G]).left s)).hom.FormallyEtale := by
  exact actualStalk_formallyEtale_of_restrictionBijection G.hom
    (𝟙 G ^ m : G ⟶ G).left ((η[G]).left s) (Over.w _)
    (unit_relativeDerivationRestriction_bijective k G m hm s)

end H101DirectFieldRoute.ActualTransport

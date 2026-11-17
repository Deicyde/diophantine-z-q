import ZInQKernel.Contrib.OneProof.Y3FineModuli.GrpObjRelativeGroupLaw
import ZInQKernel.Contrib.OneProof.Y3FineModuli.CharZeroTrace

/-!
# Actual affine group-object action clauses for the source tangent trace

Separate new work after the frozen trace helper. The entry and seven files of
that draft are not changed. Pointwise homomorphism/addition clauses are proved
from actual `Over` group-object endomorphisms via Mathlib's `MonObj.mul_comp`
and `MonObj.comp_mul`; composition has the target's `act y ≫ act x` orientation.
This file alone retains the full source-style compatible tangent-map inputs.
A concrete tangent model is constructed separately, not postulated here.
No target QMAbScheme, full level, global family or R1 witness is asserted.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace ZInQ.Contrib.OneProof.Y3FineModuli.Source

open CategoryTheory AlgebraicGeometry
open _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.NeronModelInfra
open _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.GoodReductionJacobian
open CerednikDrinfeld.QM
open scoped CategoryTheory.MonObj

/-- Pushing an actual scheme point is composition in the actual over category. -/
theorem pushPt_eq_over_comp {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (a : A ⟶ A) (ha : a ≫ f = f)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) :
    pushPt a ha P = overHomToSchemeHomOver
      (schemeHomOverToOverHom P ≫ (Over.homMk a ha : Over.mk f ⟶ Over.mk f)) := by
  apply Subtype.ext
  rfl

/-- The source's all-test-scheme action-hom clause follows from the actual
monoid-homomorphism property over the affine base. -/
theorem pushPt_mul_of_isMonHom {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} [GrpObj (Over.mk f)]
    (a : A ⟶ A) (ha : a ≫ f = f)
    [IsMonHom (Over.homMk a ha : Over.mk f ⟶ Over.mk f)]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f) :
    pushPt a ha ((relativeGroupLawOfGrpObj R f).mul t P Q) =
      (relativeGroupLawOfGrpObj R f).mul t (pushPt a ha P) (pushPt a ha Q) := by
  simp only [relativeGroupLawOfGrpObj_mul, pushPt_eq_over_comp,
    schemeHomOverToOverHom_overHomToSchemeHomOver]
  rw [MonObj.mul_comp]

/-- Pointwise addition of the order action is derived from the actual addition
clause in the group of over-category endomorphisms. -/
theorem pushPt_add_of_over_add {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} [GrpObj (Over.mk f)]
    (act : LeafQM.O → (A ⟶ A)) (act_over : ∀ a, act a ≫ f = f)
    (act_add : ∀ a b : LeafQM.O,
      (Over.homMk (act (a + b)) (act_over _) : Over.mk f ⟶ Over.mk f) =
        Over.homMk (act a) (act_over a) * Over.homMk (act b) (act_over b))
    (a b : LeafQM.O) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (P : SchemeHomOver t f) :
    pushPt (act (a + b)) (act_over _) P =
      (relativeGroupLawOfGrpObj R f).mul t
        (pushPt (act a) (act_over a) P) (pushPt (act b) (act_over b) P) := by
  simp only [pushPt_eq_over_comp, relativeGroupLawOfGrpObj_mul,
    schemeHomOverToOverHom_overHomToSchemeHomOver]
  rw [act_add, MonObj.comp_mul]

/-- A genuine affine group object supplies the source group-law/action clauses.
This theorem still quantifies over a compatible tangent model as in the source;
it is not a full target-object projection or a moduli existence theorem. -/
theorem over_group_object_tangent_trace
    {R : Type} [CommRing R] {A : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of R)} [GrpObj (Over.mk f)]
    [SmoothOfRelativeDimension 2 f]
    (act : LeafQM.O → (A ⟶ A)) (act_over : ∀ a, act a ≫ f = f)
    (act_hom : ∀ a : LeafQM.O,
      IsMonHom (Over.homMk (act a) (act_over a) : Over.mk f ⟶ Over.mk f))
    (act_one : act 1 = 𝟙 A)
    (act_mul : ∀ a b : LeafQM.O, act (a * b) = act b ≫ act a)
    (act_add : ∀ a b : LeafQM.O,
      (Over.homMk (act (a + b)) (act_over _) : Over.mk f ⟶ Over.mk f) =
        Over.homMk (act a) (act_over a) * Over.homMk (act b) (act_over b))
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (sk : R →+* k)
    (V : Type) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (τ : V → SchemeHomOver (tangentBase k sk) f)
    (hinj : Function.Injective τ)
    (hrange : ∀ P : SchemeHomOver (tangentBase k sk) f,
      P ∈ Set.range τ ↔ IsTangentVector (relativeGroupLawOfGrpObj R f) k sk P)
    (hadd : ∀ v w, τ (v + w) = (relativeGroupLawOfGrpObj R f).mul (tangentBase k sk) (τ v) (τ w))
    (hsmul : ∀ (c : k) v, (τ (c • v)).1 = tangentScale k c ≫ (τ v).1)
    (m : LeafQM.O) (Φ : V →ₗ[k] V)
    (hΦ : ∀ v, τ (Φ v) = pushPt (act m) (act_over m) (τ v))
    (n : ℤ) (hn : (m : LeafQM.B) + star (m : LeafQM.B) = ((n : ℚ) : LeafQM.B)) :
    LinearMap.trace k V Φ = (n : k) := by
  have hhom : ∀ (a : LeafQM.O) {T : Scheme.{0}}
      (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      pushPt (act a) (act_over a) ((relativeGroupLawOfGrpObj R f).mul t P Q) =
        (relativeGroupLawOfGrpObj R f).mul t
          (pushPt (act a) (act_over a) P) (pushPt (act a) (act_over a) Q) := by
    intro a T t P Q
    letI := act_hom a
    exact pushPt_mul_of_isMonHom (act a) (act_over a) t P Q
  exact _root_.ZInQ.Contrib.OneProof.Y3FineModuli.literal_order_charZero_tangent_trace
    (relativeGroupLawOfGrpObj R f) act act_over hhom act_one act_mul
    (pushPt_add_of_over_add act act_over act_add) k sk V τ hinj hrange hadd hsmul m Φ hΦ n hn

end ZInQ.Contrib.OneProof.Y3FineModuli.Source

import ZInQKernel.Contrib.OneProof.Y3FineModuli.GrpObjActionTrace
import ZInQKernel.Contrib.OneProof.Y3FineModuli.CanonicalTangentModel

/-!
# Constructed tangent representation of an actual affine group object

Separate new work after the frozen trace draft. The carrier is the actual
cotangent-dual space of the geometric fibre at its identity. The tangent map,
its complete range, addition/scalar compatibility, finiteness and dimension
are constructed/proved in CanonicalTangentModel; the order action is transported
through that actual map. No vector model, rank, operator representation or
trace condition is an additional input. The original source proof bodies are
reused at FLT6e837e75355538c7f80bab5b956861e86c4eacc2, with notices/license
retained under Vendor/AnthropicFLT. This is an affine object-action bridge,
not a target QMAbScheme projection, global family or R1 witness.
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

/-- The ring representation on the concrete cotangent-dual model is constructed
from the actual group object and scheme action; it is not assumed. -/
theorem exists_canonical_tangent_representation
    {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} [GrpObj (Over.mk f)]
    (act : LeafQM.O → (A ⟶ A)) (act_over : ∀ a, act a ≫ f = f)
    (act_hom : ∀ a : LeafQM.O,
      IsMonHom (Over.homMk (act a) (act_over a) : Over.mk f ⟶ Over.mk f))
    (act_one : act 1 = 𝟙 A)
    (act_mul : ∀ a b : LeafQM.O, act (a * b) = act b ≫ act a)
    (act_add : ∀ a b : LeafQM.O,
      (Over.homMk (act (a + b)) (act_over _) : Over.mk f ⟶ Over.mk f) =
        Over.homMk (act a) (act_over a) * Over.homMk (act b) (act_over b))
    (k : Type u) [Field k] (sk : R →+* k) :
    ∃ ρ : LeafQM.O →+* Module.End k (CanonicalTangent.Space (relativeGroupLawOfGrpObj R f) k sk),
      (∀ (a : LeafQM.O) (v : CanonicalTangent.Space (relativeGroupLawOfGrpObj R f) k sk),
        CanonicalTangent.pointMap (relativeGroupLawOfGrpObj R f) k sk (ρ a v) =
          pushPt (act a) (act_over a)
            (CanonicalTangent.pointMap (relativeGroupLawOfGrpObj R f) k sk v)) ∧
      (∀ (m : LeafQM.O)
        (Φ : Module.End k (CanonicalTangent.Space (relativeGroupLawOfGrpObj R f) k sk)),
        (∀ v, CanonicalTangent.pointMap (relativeGroupLawOfGrpObj R f) k sk (Φ v) =
          pushPt (act m) (act_over m)
            (CanonicalTangent.pointMap (relativeGroupLawOfGrpObj R f) k sk v)) → ρ m = Φ) := by
  let L := relativeGroupLawOfGrpObj R f
  have hhom : ∀ (a : LeafQM.O) {T : Scheme.{u}}
      (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      pushPt (act a) (act_over a) (L.mul t P Q) =
        L.mul t (pushPt (act a) (act_over a) P) (pushPt (act a) (act_over a) Q) := by
    intro a T t P Q
    haveI := act_hom a
    exact pushPt_mul_of_isMonHom (act a) (act_over a) t P Q
  exact literal_order_tangent_operators L act act_over hhom act_one act_mul
    (pushPt_add_of_over_add act act_over act_add) k sk (CanonicalTangent.Space L k sk)
    (CanonicalTangent.pointMap L k sk) (CanonicalTangent.pointMap_injective L k sk)
    (CanonicalTangent.pointMap_range L k sk) (CanonicalTangent.pointMap_add L k sk)
    (CanonicalTangent.pointMap_smul L k sk)

/-- With actual smooth relative dimension two, this concrete representation has
rank two and integer reduced trace. Finiteness, rank and action are conclusions,
not hidden hypotheses. IsAlgClosed/CharZero retain the source trace field scope. -/
theorem exists_canonical_tangent_representation_and_trace
    {R : Type u} [CommRing R] {A : Scheme.{u}}
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
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k] (sk : R →+* k) :
    ∃ ρ : LeafQM.O →+* Module.End k (CanonicalTangent.Space (relativeGroupLawOfGrpObj R f) k sk),
      (∀ (a : LeafQM.O) (v : CanonicalTangent.Space (relativeGroupLawOfGrpObj R f) k sk),
        CanonicalTangent.pointMap (relativeGroupLawOfGrpObj R f) k sk (ρ a v) =
          pushPt (act a) (act_over a)
            (CanonicalTangent.pointMap (relativeGroupLawOfGrpObj R f) k sk v)) ∧
      Module.finrank k (CanonicalTangent.Space (relativeGroupLawOfGrpObj R f) k sk) = 2 ∧
      (∀ (m : LeafQM.O) (n : ℤ),
        (m : LeafQM.B) + star (m : LeafQM.B) = ((n : ℚ) : LeafQM.B) →
          LinearMap.trace k (CanonicalTangent.Space (relativeGroupLawOfGrpObj R f) k sk) (ρ m) = (n : k)) := by
  let L := relativeGroupLawOfGrpObj R f
  haveI := CanonicalTangent.space_finite L k sk 2
  obtain ⟨ρ, hρ, huniq⟩ := exists_canonical_tangent_representation
    act act_over act_hom act_one act_mul act_add k sk
  refine ⟨ρ, hρ, CanonicalTangent.space_finrank L k sk 2, ?_⟩
  intro m n hn
  exact _root_.ZInQ.Contrib.OneProof.Y3FineModuli.literal_order_trace_eq_intCast
    ρ (CanonicalTangent.space_finrank L k sk 2) m n hn

end ZInQ.Contrib.OneProof.Y3FineModuli.Source

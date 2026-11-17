import ZInQKernel.Contrib.OneProof.Y3FineModuli.GrpObjCanonicalTrace
import ZInQKernel.Contrib.OneProof.Y3FineModuli.GrpObjActionCommutative

/-!
# Generic over-objects and actual rational-base field hypotheses

These are new object/field bridges, not an R1 witness or a replacement target.
An arbitrary `F : Over (Spec R)` is the genuine categorical over-object; its
eta equality with `Over.mk F.hom` is definitional. Characteristic zero of each
field is proved using the ACTUAL unital composite ℚ→R→k, not inferred from
CharZero R (which would be false for ℤ→Fp). The universal trace clause keeps
all of the source's finite-model/range/addition/scalar/intertwining quantifiers;
no canonical tangent map is added as a new object hypothesis.
-/

set_option autoImplicit false
noncomputable section

namespace ZInQ.Contrib.OneProof.Y3FineModuli.Source

open CategoryTheory AlgebraicGeometry
open _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.NeronModelInfra
open _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.GoodReductionJacobian
open CerednikDrinfeld.QM
open scoped CategoryTheory.MonObj

/-- The actual rational algebra map into a field proves its characteristic zero. -/
theorem charZero_of_rat_algebra_map {R : Type} [CommRing R] [Algebra ℚ R]
    (k : Type) [Field k] (sk : R →+* k) : CharZero k := by
  let qk : ℚ →+* k := sk.comp (algebraMap ℚ R)
  refine ⟨fun m n hmn => ?_⟩
  apply (Nat.cast_injective (R := ℚ))
  apply qk.injective
  simpa only [map_natCast] using hmn

/-- The genuine over-object's group structure supplies the source law. The
eta transport is constructed here, not required as a separate instance input. -/
def relativeGroupLawOfOver {R : Type} [CommRing R]
    (F : Over (Spec (CommRingCat.of R))) [GrpObj F] : RelativeGroupLaw R F.hom := by
  letI : GrpObj (Over.mk F.hom) := by
    change GrpObj F
    infer_instance
  exact relativeGroupLawOfGrpObj R F.hom

/-- The actual source-style universal tangent trace over a rational affine base,
with the field characteristic DERIVED from the base map and every source
model/action/range/scalar hypothesis retained in its proper quantifier scope. -/
theorem over_rat_algebra_tangent_trace
    {R : Type} [CommRing R] [Algebra ℚ R]
    (F : Over (Spec (CommRingCat.of R))) [GrpObj F]
    [SmoothOfRelativeDimension 2 F.hom]
    (act : LeafQM.O → (F.left ⟶ F.left)) (act_over : ∀ a, act a ≫ F.hom = F.hom)
    (act_hom : ∀ a : LeafQM.O,
      IsMonHom (Over.homMk (act a) (act_over a) : F ⟶ F))
    (act_one : act 1 = 𝟙 F.left)
    (act_mul : ∀ a b : LeafQM.O, act (a * b) = act b ≫ act a)
    (act_add : ∀ a b : LeafQM.O,
      (Over.homMk (act (a + b)) (act_over _) : F ⟶ F) =
        Over.homMk (act a) (act_over a) * Over.homMk (act b) (act_over b))
    (k : Type) [Field k] [IsAlgClosed k] (sk : R →+* k)
    (V : Type) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (τ : V → SchemeHomOver (tangentBase k sk) F.hom)
    (hinj : Function.Injective τ)
    (hrange : ∀ P : SchemeHomOver (tangentBase k sk) F.hom,
      P ∈ Set.range τ ↔ IsTangentVector (relativeGroupLawOfOver F) k sk P)
    (hadd : ∀ v w, τ (v + w) = (relativeGroupLawOfOver F).mul (tangentBase k sk) (τ v) (τ w))
    (hsmul : ∀ (c : k) v, (τ (c • v)).1 = tangentScale k c ≫ (τ v).1)
    (m : LeafQM.O) (Φ : V →ₗ[k] V)
    (hΦ : ∀ v, τ (Φ v) = pushPt (act m) (act_over m) (τ v))
    (n : ℤ) (hn : (m : LeafQM.B) + star (m : LeafQM.B) = ((n : ℚ) : LeafQM.B)) :
    LinearMap.trace k V Φ = (n : k) := by
  letI : GrpObj (Over.mk F.hom) := by
    change GrpObj F
    infer_instance
  haveI := charZero_of_rat_algebra_map k sk
  exact over_group_object_tangent_trace act act_over act_hom act_one act_mul act_add
    k sk V τ hinj hrange hadd hsmul m Φ hΦ n hn

end ZInQ.Contrib.OneProof.Y3FineModuli.Source

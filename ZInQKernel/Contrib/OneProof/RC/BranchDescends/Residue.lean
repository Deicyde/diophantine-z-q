import ZInQKernel.Contrib.OneProof.RC.PreparedParam.Prints
import Mathlib.AlgebraicGeometry.ResidueField

/-! Descent from values of regular rational functions (on the spot, c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory
open ZInQ.Manuscript.RC.PreparedParam

namespace ZInQ.Manuscript.RC.BranchDescends

/-- The embedded residue field at the image of a complex point consists
exactly of the values of the local ring. For an integral scheme the local
ring is a subring of the function field, so these are the values of all
rational functions regular there. No closedness of the image is needed. -/
theorem residueField_range_eq_stalkValue_range {X : Scheme.{0}}
    (x : Spec (.of ℂ) ⟶ X) :
    Set.range (X.descResidueField (Scheme.stalkClosedPointTo x)).hom =
      Set.range (Scheme.stalkClosedPointTo x).hom := by
  let q := x (IsLocalRing.closedPoint ℂ)
  let t := Scheme.stalkClosedPointTo x
  let a := X.descResidueField t
  have he : X.residue q ≫ a = t := X.residue_descResidueField t
  calc
    Set.range a.hom = Set.range (a.hom ∘ (X.residue q).hom) := by
      rw [Set.range_comp, (X.residue_surjective q).range_eq, Set.image_univ]
    _ = Set.range t.hom := congrArg (fun f => Set.range (CommRingCat.Hom.hom f)) he

/-- If all regular rational functions at the image of a complex point
take values in `ι(H)`, the point descends to `H`. The hypothesis tests the
local ring, which on an integral scheme represents precisely those functions. -/
theorem fieldPoint_of_stalk_values {X : Scheme.{0}} {p : X ⟶ Spec (.of ℚ)}
    (x : FieldPoint p ℂ) {H : Type} [Field H] [Algebra ℚ H] (ι : H →ₐ[ℚ] ℂ)
    (h : ∀ r, Scheme.stalkClosedPointTo x.val r ∈ Set.range ι) :
    ∃ y : FieldPoint p H, y.map ι = x := by
  let q := x.val (IsLocalRing.closedPoint ℂ)
  let a := X.descResidueField (Scheme.stalkClosedPointTo x.val)
  have ha (z : X.residueField q) : a z ∈ ι.toRingHom.fieldRange := by
    have hz : a z ∈ Set.range a.hom := ⟨z, rfl⟩
    rw [residueField_range_eq_stalkValue_range x.val] at hz
    obtain ⟨r, hr⟩ := hz
    exact hr ▸ h r
  let b := ι.toRingHom.rangeRestrictFieldEquiv.symm.toRingHom.comp (a.hom.codRestrict _ ha)
  have hab : CommRingCat.ofHom b ≫ CommRingCat.ofHom ι.toRingHom = a := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    exact ι.toRingHom.rangeRestrictFieldEquiv_apply_symm_apply ⟨a z, ha z⟩
  let y := Spec.map (CommRingCat.ofHom b) ≫ X.fromSpecResidueField q
  have hy : y ≫ p = Spec.map (CommRingCat.ofHom (algebraMap ℚ H)) := by
    apply Spec.homEquiv.injective
    exact CommRingCat.hom_ext (Subsingleton.elim _ _)
  refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
  change Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ y = x.val
  rw [show y = _ from rfl, ← Category.assoc, ← Spec.map_comp, hab]
  exact Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField ℂ X x.val

end ZInQ.Manuscript.RC.BranchDescends

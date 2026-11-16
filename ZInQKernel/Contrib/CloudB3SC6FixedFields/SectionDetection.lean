import ZInQKernel.Contrib.CloudB3SC6FixedFields.GeometricPointDensity
import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Sections and generic germs are detected by algebraic-closure point values

This uses the geometric-point density proof extracted in `GeometricPointDensity`.
All objects are Mathlib schemes, sections, residue fields, and generic stalks.
The evaluation map below is the usual residue-field evaluation followed by the
embedding associated to a field point. No moduli or curve existence is assumed.
-/

namespace CloudB3SC6FixedFields

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

/-- The value of a section at a field point, through its residue-field embedding. -/
noncomputable def geometricValue {Z : Scheme.{u}} {L : Type u} [Field L]
    (A : Z.Opens) (y : Spec (CommRingCat.of L) ⟶ Z)
    (hA : (Scheme.SpecToEquivOfField L Z y).1 ∈ A) : Γ(Z, A) →+* L :=
  ((Scheme.SpecToEquivOfField L Z y).2).hom.comp (Z.evaluation A _ hA).hom

/-- Restriction of a section does not change its value at a field point. -/
theorem geometricValue_res {Z : Scheme.{u}} {L : Type u} [Field L]
    {A A' : Z.Opens} (i : A' ⟶ A) (y : Spec (CommRingCat.of L) ⟶ Z)
    (hA' : (Scheme.SpecToEquivOfField L Z y).1 ∈ A') (s : Γ(Z, A)) :
    geometricValue A' y hA' (Z.presheaf.map i.op s) = geometricValue A y (i.le hA') s := by
  simp only [geometricValue, RingHom.comp_apply, Scheme.evaluation, CommRingCat.comp_apply]
  rw [TopCat.Presheaf.germ_res_apply]

section Detection

variable {R L : Type u} [Field R] [Field L] [IsAlgClosed L] [Algebra R L]
variable {Z : Scheme.{u}} [IsIntegral Z]

/-- A section on an integral flat finite-type scheme vanishing at every algebraic-closure point
of its open domain is zero. The generic point is required to lie in the open. -/
theorem section_eq_zero_of_geometric_values (hinj : Function.Injective (algebraMap R L))
    (t : Z ⟶ Spec (CommRingCat.of R)) [Flat t] [LocallyOfFiniteType t]
    (A : Z.Opens) (hηA : genericPoint Z ∈ A) (s : Γ(Z, A))
    (H : ∀ (y : Spec (CommRingCat.of L) ⟶ Z), y ≫ t = geometricBaseMap R L →
      ∀ hy : (Scheme.SpecToEquivOfField L Z y).1 ∈ A, geometricValue A y hy s = 0) : s = 0 := by
  by_contra hs
  have hηD : genericPoint Z ∈ Z.basicOpen s := by
    rw [Scheme.mem_basicOpen Z s (genericPoint Z) hηA]
    apply isUnit_iff_ne_zero.mpr
    intro h0
    apply hs
    apply germ_injective_of_isIntegral Z (genericPoint Z) hηA
    simpa only [map_zero] using h0
  obtain ⟨y, hy, hyD⟩ := exists_geometric_point_mem hinj t (Z.basicOpen s) ⟨_, hηD⟩
  have hyA : (Scheme.SpecToEquivOfField L Z y).1 ∈ A := Z.basicOpen_le s hyD
  have h0 := H y hy hyA
  have hn : Z.evaluation A (Scheme.SpecToEquivOfField L Z y).1 hyA s ≠ 0 :=
    (Z.evaluation_ne_zero_iff_mem_basicOpen _ hyA s).mpr hyD
  apply hn
  exact (map_eq_zero_iff ((Scheme.SpecToEquivOfField L Z y).2).hom
    (RingHom.injective _)).mp h0

/-- Sections with the same algebraic-closure point values are equal. -/
theorem section_eq_of_geometric_values (hinj : Function.Injective (algebraMap R L))
    (t : Z ⟶ Spec (CommRingCat.of R)) [Flat t] [LocallyOfFiniteType t]
    (A : Z.Opens) (hηA : genericPoint Z ∈ A) (a b : Γ(Z, A))
    (H : ∀ (y : Spec (CommRingCat.of L) ⟶ Z), y ≫ t = geometricBaseMap R L →
      ∀ hy : (Scheme.SpecToEquivOfField L Z y).1 ∈ A,
        geometricValue A y hy a = geometricValue A y hy b) : a = b := by
  apply sub_eq_zero.mp
  apply section_eq_zero_of_geometric_values hinj t A hηA (a - b)
  intro y hy hyA
  rw [map_sub, H y hy hyA, sub_self]

/-- Sections on two generic-point neighbourhoods with matching geometric values have equal
function-field germs. The values need only match where both sections are defined. -/
theorem germ_eq_of_geometric_values (hinj : Function.Injective (algebraMap R L))
    (t : Z ⟶ Spec (CommRingCat.of R)) [Flat t] [LocallyOfFiniteType t]
    {A B : Z.Opens} (hηA : genericPoint Z ∈ A) (hηB : genericPoint Z ∈ B)
    (a : Γ(Z, A)) (b : Γ(Z, B))
    (H : ∀ (y : Spec (CommRingCat.of L) ⟶ Z), y ≫ t = geometricBaseMap R L →
      ∀ (hyA : (Scheme.SpecToEquivOfField L Z y).1 ∈ A)
        (hyB : (Scheme.SpecToEquivOfField L Z y).1 ∈ B),
        geometricValue A y hyA a = geometricValue B y hyB b) :
    Z.presheaf.germ A _ hηA a = Z.presheaf.germ B _ hηB b := by
  have hηAB : genericPoint Z ∈ A ⊓ B := ⟨hηA, hηB⟩
  have e : Z.presheaf.map (homOfLE (inf_le_left : A ⊓ B ≤ A)).op a =
      Z.presheaf.map (homOfLE (inf_le_right : A ⊓ B ≤ B)).op b := by
    apply section_eq_of_geometric_values hinj t (A ⊓ B) hηAB
    intro y hy hyAB
    rw [geometricValue_res, geometricValue_res]
    exact H y hy hyAB.1 hyAB.2
  have eg := congrArg (Z.presheaf.germ (A ⊓ B) _ hηAB) e
  rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at eg
  exact eg

end Detection

end CloudB3SC6FixedFields

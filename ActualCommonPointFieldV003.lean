import ActualDivisionFieldV004

/-!
# A common defining field for every point of an actual finite torsion level

The finite supremum of the individual genuine point fields carries
native points whose scalar extensions are the original points. Fixing
that scalar field therefore fixes every point, not a supplied model.
-/

noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry

namespace ActualCommonPointField
open ActualFiniteLevel ActualDivisionField
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

def pointExtensionHom (L E : FiniteGaloisIntermediateField K Ω) (h : L ≤ E) :
    PkgI3.AbVar.ptObj (K := K) E ⟶ PkgI3.AbVar.ptObj (K := K) L :=
  Over.homMk (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom)) (by
    change Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K L)) =
        Spec.map (CommRingCat.ofHom (algebraMap K E))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1)

lemma extension_to_original (A : PkgI3.AbVar K) (L E : FiniteGaloisIntermediateField K Ω)
    (h : L ≤ E) (y : A.Pt L) :
    Spec.map (CommRingCat.ofHom E.toIntermediateField.val.toRingHom) ≫
      (pointExtensionHom L E h ≫ y).left =
        Spec.map (CommRingCat.ofHom L.toIntermediateField.val.toRingHom) ≫ y.left := by
  let y0 : Spec (CommRingCat.of L) ⟶ A.X.left := y.left
  change Spec.map (CommRingCat.ofHom E.toIntermediateField.val.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom) ≫ y0 =
      Spec.map (CommRingCat.ofHom L.toIntermediateField.val.toRingHom) ≫ y0
  rw [← Category.assoc, ← Spec.map_comp]
  have he : CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom ≫
      CommRingCat.ofHom E.toIntermediateField.val.toRingHom =
        CommRingCat.ofHom L.toIntermediateField.val.toRingHom := by
    ext a
    rfl
  rw [he]

lemma exists_common_defining_field [CharZero K] [IsAlgClosure K Ω]
    (A : PkgI3.AbVar K) (m : ℕ) [Finite (torsionSubgroup A Ω m)] :
    ∃ E : FiniteGaloisIntermediateField K Ω,
      (∀ x : torsionSubgroup A Ω m, ∃ y : A.Pt E,
        Spec.map (CommRingCat.ofHom E.toIntermediateField.val.toRingHom) ≫ y.left = x.1.left) ∧
      E.fixingSubgroup ≤ (action (Ω := Ω) A m).ker := by
  classical
  letI := Fintype.ofFinite (torsionSubgroup A Ω m)
  choose L y hy using fun x : torsionSubgroup A Ω m =>
    SchemePointField.exists_finiteGalois_point A.X x.1
  let E : FiniteGaloisIntermediateField K Ω := Finset.univ.sup L
  have hE (x : torsionSubgroup A Ω m) : L x ≤ E := Finset.le_sup (Finset.mem_univ x)
  have hpoints (x : torsionSubgroup A Ω m) : ∃ z : A.Pt E,
      Spec.map (CommRingCat.ofHom E.toIntermediateField.val.toRingHom) ≫ z.left = x.1.left :=
    ⟨pointExtensionHom (L x) E (hE x) ≫ y x,
      (extension_to_original A (L x) E (hE x) (y x)).trans (hy x)⟩
  refine ⟨E, hpoints, ?_⟩
  intro σ hσ
  apply (mem_action_ker A m σ).mpr
  intro x hx
  obtain ⟨yE, hyE⟩ := hpoints ⟨x, hx⟩
  exact point_fixed_of_field A E x yE hyE σ hσ

end ActualCommonPointField

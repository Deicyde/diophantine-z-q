
namespace X6Kummer

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM.AV LeafQM.AV.Pin PkgI3 FS5NoCM

/-! ## §F `PairBaseChangeUnique` is a theorem (pullback uniqueness and rigidity) -/

/-- The identity `ℚ̄`-point of an abelian variety over `ℚ̄`, as a morphism of schemes, is the
underlying morphism of the unit `η`. -/
theorem one_pt_left (A : AbVar Qbar) :
    (1 : A.Pt Qbar).left = (η[A.X]).left := by
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
  change Spec.map (CommRingCat.ofHom (algebraMap Qbar Qbar)) ≫ _ = _
  rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]

/-- **`PairBaseChangeUnique` holds.** The two pullback squares give `e : Q.A ≅ Q'.A` over
`Spec ℚ̄` (`IsPullback.isoIsPullback`); `e` and `e⁻¹` fix the identity sections and commute with
`ι` (checked after the pullback projections, `IsPullback.hom_ext`); by rigidity
(`G0FibreSimple.rigidityHom`, mul-rigidity) both are homomorphisms. -/
theorem pairBaseChangeUnique : PairBaseChangeUnique := by
  intro σ P Q Q' ⟨g, hpb, hι, h1⟩ ⟨g', hpb', hι', h1'⟩
  rw [one_pt_left, one_pt_left] at h1 h1'
  let e := hpb.isoIsPullback _ _ hpb'
  have ehf : e.hom ≫ g' = g := by simp [e]
  have ehs : e.hom ≫ Q'.A.X.hom = Q.A.X.hom := by simp [e]
  have eif : e.inv ≫ g = g' := by simp [e]
  have eis : e.inv ≫ Q.A.X.hom = Q'.A.X.hom := by simp [e]
  let eH : Q.A.X ⟶ Q'.A.X := Over.homMk e.hom ehs
  let eI : Q'.A.X ⟶ Q.A.X := Over.homMk e.inv eis
  have hη : η[Q.A.X] ≫ eH = η[Q'.A.X] := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left]
    apply hpb'.hom_ext
    · change ((η[Q.A.X]).left ≫ e.hom) ≫ g' = (η[Q'.A.X]).left ≫ g'
      rw [Category.assoc, ehf]
      exact h1.trans h1'.symm
    · change ((η[Q.A.X]).left ≫ e.hom) ≫ Q'.A.X.hom = (η[Q'.A.X]).left ≫ Q'.A.X.hom
      rw [Category.assoc, ehs, Over.w, Over.w]
  have hη' : η[Q'.A.X] ≫ eI = η[Q.A.X] := by
    rw [← hη, Category.assoc]
    have : eH ≫ eI = 𝟙 _ := by
      apply Over.OverMorphism.ext
      exact e.hom_inv_id
    rw [this, Category.comp_id]
  have : IsMonHom eH := G0FibreSimple.rigidityHom Qbar Q.A Q'.A eH hη
  have : IsMonHom eI := G0FibreSimple.rigidityHom Qbar Q'.A Q.A eI hη'
  refine ⟨⟨AbVar.Hom.mk' eH, AbVar.Hom.mk' eI, ?_, ?_, ?_⟩⟩
  · apply Over.OverMorphism.ext
    exact e.hom_inv_id
  · apply Over.OverMorphism.ext
    exact e.inv_hom_id
  · intro a
    simp only [AbVar.Hom.hom_mk']
    apply Over.OverMorphism.ext
    rw [Over.comp_left, Over.comp_left]
    apply hpb'.hom_ext
    · change ((Q.q.iota a).hom.left ≫ e.hom) ≫ g' = (e.hom ≫ (Q'.q.iota a).hom.left) ≫ g'
      rw [Category.assoc, ehf, hι a, Category.assoc, hι' a, ← Category.assoc, ehf]
    · change ((Q.q.iota a).hom.left ≫ e.hom) ≫ Q'.A.X.hom =
        (e.hom ≫ (Q'.q.iota a).hom.left) ≫ Q'.A.X.hom
      rw [Category.assoc, ehs, Category.assoc, Over.w, Over.w, ehs]

/-- **N2 `X6KummerFibre` from the leaf N2-L `X6KummerModel` and the curve glue `MobiusGlue`
(compiled; `PairBaseChangeUnique` is now a theorem).** -/
theorem x6KummerFibre_of_model' (hM : MobiusGlue) (hL : X6KummerModel) : X6KummerFibre :=
  x6KummerFibre_of_model hM pairBaseChangeUnique hL

end X6Kummer

#print axioms X6Kummer.pairBaseChangeUnique
#print axioms X6Kummer.x6KummerFibre_of_model'

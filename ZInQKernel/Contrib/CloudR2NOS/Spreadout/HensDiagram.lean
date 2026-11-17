/-
# H5 / NOS round 2, lane 3 (`Spreadout/`): an ind-étale ring as a cofiltered limit of affine stages

New glue (no vendored source in this file).

For a filtered colimit presentation `pres : ColimitPresentation J S` of a commutative `R`-algebra
`S` (for example H4's `(CommAlgCat.etale R).ind (CommAlgCat.of R Rh)` presentation of the ordinary
henselization `Rh` constructed in
`ZInQKernel.Contrib.CloudR2Raynaud.StrictHenselization.Port.StrictColimit.exists_concrete_henselization`),
`Spec` turns it into a cofiltered diagram of affine schemes with affine transition maps whose limit
is `Spec S` (`isLimit_specCone`).  `exists_grpObj_stage_of_presentation` then spreads a smooth
(and, with the explicit properness input, proper) group object over `Spec S` to some stage
`Spec (pres.diag.obj j)`, by an isomorphism of group objects, and `stagePoint` is the rational
point of a stage given by an `R`-algebra augmentation of `S`.
-/
import ZInQKernel.Contrib.CloudR2NOS.Spreadout.GroupStage

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace ZInQ.Contrib.CloudR2NOS.Spreadout

universe u

section Forget

variable (R : Type u) [CommRing R]

/-- `forget₂ (CommAlgCat R) CommRingCat` is `Under.forget` after `commAlgCatEquivUnder`. -/
def forget₂IsoUnder : forget₂ (CommAlgCat.{u} R) CommRingCat.{u} ≅
    (commAlgCatEquivUnder (CommRingCat.of R)).functor ⋙ Under.forget (CommRingCat.of R) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

instance preservesFilteredColimits_forget₂ {J : Type u} [SmallCategory J] [IsFiltered J] :
    PreservesColimitsOfShape J (forget₂ (CommAlgCat.{u} R) CommRingCat.{u}) :=
  preservesColimitsOfShape_of_natIso (forget₂IsoUnder R).symm

end Forget

section Diagram

variable {R : Type u} [CommRing R] {S : CommAlgCat.{u} R} {J : Type u} [SmallCategory J]
  (pres : ColimitPresentation J S)

/-- The cofiltered diagram of spectra of the stages of a filtered colimit presentation. -/
def specDiagram : Jᵒᵖ ⥤ Scheme.{u} :=
  (pres.diag ⋙ forget₂ (CommAlgCat.{u} R) CommRingCat.{u}).op ⋙ Scheme.Spec

/-- `Spec S` as a cone over `specDiagram`. -/
def specCone : Cone (specDiagram pres) :=
  Scheme.Spec.mapCone
    ((forget₂ (CommAlgCat.{u} R) CommRingCat.{u}).mapCocone (Cocone.mk _ pres.ι)).op

/-- `Spec S` is the limit of the spectra of the stages. -/
def isLimit_specCone [IsFiltered J] : IsLimit (specCone pres) :=
  isLimitOfPreserves Scheme.Spec
    (IsColimit.op (isColimitOfPreserves (forget₂ (CommAlgCat.{u} R) CommRingCat.{u})
      pres.isColimit))

instance specDiagram_isAffine (j : Jᵒᵖ) : IsAffine ((specDiagram pres).obj j) := by
  dsimp [specDiagram]
  infer_instance

instance specDiagram_isAffineHom {i j : Jᵒᵖ} (f : i ⟶ j) :
    IsAffineHom ((specDiagram pres).map f) :=
  isAffineHom_of_isAffine _

instance specDiagram_compactSpace (j : Jᵒᵖ) : CompactSpace ((specDiagram pres).obj j) :=
  inferInstance

instance specDiagram_quasiSeparatedSpace (j : Jᵒᵖ) :
    QuasiSeparatedSpace ((specDiagram pres).obj j) :=
  inferInstance

@[simp]
theorem specCone_pt : (specCone pres).pt = Spec (CommRingCat.of S) := rfl

@[simp]
theorem specDiagram_obj (j : Jᵒᵖ) :
    (specDiagram pres).obj j = Spec (CommRingCat.of (pres.diag.obj j.unop)) := rfl

theorem specCone_π_app (j : Jᵒᵖ) :
    (specCone pres).π.app j = Spec.map (CommRingCat.ofHom (pres.ι.app j.unop).hom.toRingHom) :=
  rfl

/-- **Stage model of a group object over an ind-presented affine base.**  A smooth, finitely
presented group object over `Spec S` is, up to an isomorphism of group objects, the base change of
a smooth, finitely presented group object over the spectrum of some stage of the presentation. -/
theorem exists_grpObj_stage_of_presentation [IsFiltered J] (N : Over (specCone pres).pt) [GrpObj N]
    [LocallyOfFinitePresentation N.hom] [QuasiCompact N.hom] [QuasiSeparated N.hom]
    [Smooth N.hom] :
    ∃ (t : FPStage (specDiagram pres) (specCone pres) N) (_ : GrpObj t.M), Smooth t.M.hom ∧
      letI : GrpObj ((Over.pullback ((specCone pres).π.app t.k)).obj t.M) := Functor.grpObjObj
      IsMonHom t.e.hom :=
  exists_grpObj_smooth_stage (isLimit_specCone pres) N

/-- **The same, also proper**, given the exact properness input for this system. -/
theorem exists_grpObj_proper_stage_of_presentation [IsFiltered J]
    (hpr : ProperDescendsFor (specDiagram pres) (specCone pres))
    (N : Over (specCone pres).pt) [GrpObj N] [LocallyOfFinitePresentation N.hom]
    [QuasiCompact N.hom] [QuasiSeparated N.hom] [Smooth N.hom] [IsProper N.hom] :
    ∃ (t : FPStage (specDiagram pres) (specCone pres) N) (_ : GrpObj t.M), Smooth t.M.hom ∧
      IsProper t.M.hom ∧
      letI : GrpObj ((Over.pullback ((specCone pres).π.app t.k)).obj t.M) := Functor.grpObjObj
      IsMonHom t.e.hom :=
  exists_grpObj_proper_smooth_stage (isLimit_specCone pres) hpr N

/-- The rational point of a stage given by an `R`-algebra augmentation `ψ : S →ₐ[R] k`. -/
def stagePoint {k : Type u} [CommRing k] [Algebra R k] (ψ : S →ₐ[R] k) (j : J) :
    Spec (CommRingCat.of k) ⟶ (specDiagram pres).obj (op j) :=
  Spec.map (CommRingCat.ofHom (ψ.comp (pres.ι.app j).hom).toRingHom)

/-- The stage point lies over the point `Spec (algebraMap R k)` of `Spec R`. -/
theorem stagePoint_comp {k : Type u} [CommRing k] [Algebra R k] (ψ : S →ₐ[R] k) (j : J) :
    stagePoint pres ψ j ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (pres.diag.obj j))) =
      Spec.map (CommRingCat.ofHom (algebraMap R k)) := by
  have h : (ψ.comp (pres.ι.app j).hom).toRingHom.comp (algebraMap R (pres.diag.obj j)) =
      algebraMap R k := by
    ext r
    simp
  have h' := congrArg (fun g : R →+* k => Spec.map (CommRingCat.ofHom g)) h
  simp only [CommRingCat.ofHom_comp, Spec.map_comp] at h'
  exact h'

/-- The stage point factors through the limit point `Spec S`. -/
theorem stagePoint_eq {k : Type u} [CommRing k] [Algebra R k] (ψ : S →ₐ[R] k) (j : J) :
    stagePoint pres ψ j = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ (specCone pres).π.app (op j) := by
  have h' : Spec.map (CommRingCat.ofHom (ψ.toRingHom.comp (pres.ι.app j).hom.toRingHom)) =
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (pres.ι.app j).hom.toRingHom) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  exact h'

end Diagram

end ZInQ.Contrib.CloudR2NOS.Spreadout

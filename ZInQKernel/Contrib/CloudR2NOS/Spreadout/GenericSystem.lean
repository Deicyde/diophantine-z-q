/-
# H5 / NOS round 2, lane 3 (`Spreadout/`): the generic system of an ind-presented base

New glue (no vendored source in this file).

For a filtered colimit presentation `pres` of an `R`-algebra `S` and an `R`-algebra `K` (the
fraction field of `R` in the application), the stages `Spec Bⱼ` and `Spec S` lie over `Spec R`
(`specDiagramOver`, `specConeOver`); base changing along `Spec K ⟶ Spec R` gives the *generic
system* `j ↦ Spec Bⱼ ×_{Spec R} Spec K`, whose limit is `Spec S ×_{Spec R} Spec K`
(`isLimit_genCone`: `Over.forget` reflects and preserves the connected limit, and `Over.pullback`
is a right adjoint).  It is again a cofiltered system of affine schemes with affine transition
maps, so the stage-spreading results of `GroupStage`/`IsoStage` apply to it.
-/
import ZInQKernel.Contrib.CloudR2NOS.Spreadout.HensDiagram
import ZInQKernel.Contrib.CloudR2NOS.Spreadout.IsoStage

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace ZInQ.Contrib.CloudR2NOS.Spreadout

universe u

section Over

variable {R : Type u} [CommRing R]

/-- The spectrum of an `R`-algebra, as an object over `Spec R`. -/
@[simps]
def specOverFunctor : (CommAlgCat.{u} R)ᵒᵖ ⥤ Over (Spec (CommRingCat.of R)) where
  obj A := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A.unop)))
  map {A B} f := Over.homMk (Spec.map (CommRingCat.ofHom f.unop.hom.toRingHom)) (by
    dsimp
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    simp)
  map_id A := by
    ext1
    change Spec.map (CommRingCat.ofHom (RingHom.id _)) = 𝟙 _
    rw [CommRingCat.ofHom_id, Spec.map_id]
  map_comp f g := by
    ext1
    simp only [Over.homMk_left, Over.comp_left]
    rw [← Spec.map_comp]
    rfl

variable {S : CommAlgCat.{u} R} {J : Type u} [SmallCategory J]
  (pres : ColimitPresentation J S)

/-- The stages `Spec Bⱼ` as objects over `Spec R`. -/
def specDiagramOver : Jᵒᵖ ⥤ Over (Spec (CommRingCat.of R)) :=
  pres.diag.op ⋙ specOverFunctor

/-- `Spec S` over `Spec R`, as a cone over `specDiagramOver`. -/
def specConeOver : Cone (specDiagramOver pres) :=
  specOverFunctor.mapCone (Cocone.mk _ pres.ι).op

/-- Forgetting the base, `specConeOver` is `specCone`. -/
def specConeOverForgetIso : (Over.forget _).mapCone (specConeOver pres) ≅ specCone pres :=
  Cone.ext (Iso.refl _) (fun _ => by
    simp only [Iso.refl_hom]
    rfl)

/-- `Spec S` is the limit of the stages over `Spec R`. -/
def isLimit_specConeOver [IsFiltered J] : IsLimit (specConeOver pres) :=
  haveI : IsConnected Jᵒᵖ := IsCofiltered.isConnected (C := Jᵒᵖ)
  haveI : ReflectsLimitsOfShape Jᵒᵖ
      (CostructuredArrow.proj (𝟭 Scheme.{u}) (Spec (CommRingCat.of R))) := inferInstance
  isLimitOfReflects (CostructuredArrow.proj (𝟭 Scheme.{u}) (Spec (CommRingCat.of R)))
    ((isLimit_specCone pres).ofIsoLimit (specConeOverForgetIso pres).symm)

end Over

section Generic

variable {R : Type u} [CommRing R] {S : CommAlgCat.{u} R} {J : Type u} [SmallCategory J]
  (pres : ColimitPresentation J S) (K : Type u) [CommRing K] [Algebra R K]

/-- The generic map `Spec K ⟶ Spec R`. -/
abbrev genMap : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R K))

/-- The generic system `j ↦ Spec Bⱼ ×_{Spec R} Spec K`. -/
def genDiagram : Jᵒᵖ ⥤ Scheme.{u} :=
  specDiagramOver pres ⋙ Over.pullback (genMap K) ⋙ Over.forget _

/-- `Spec S ×_{Spec R} Spec K` as a cone over the generic system. -/
def genCone : Cone (genDiagram pres K) :=
  (Over.forget _).mapCone ((Over.pullback (genMap K)).mapCone (specConeOver pres))

/-- The generic system has limit `Spec S ×_{Spec R} Spec K`. -/
def isLimit_genCone [IsFiltered J] : IsLimit (genCone pres K) :=
  isLimitOfPreserves (Over.forget _)
    (isLimitOfPreserves (Over.pullback (genMap K)) (isLimit_specConeOver pres))

@[simp]
theorem genDiagram_obj (j : Jᵒᵖ) :
    (genDiagram pres K).obj j =
      pullback (Spec.map (CommRingCat.ofHom (algebraMap R (pres.diag.obj j.unop)))) (genMap K) :=
  rfl

@[simp]
theorem genCone_pt :
    (genCone pres K).pt = pullback (Spec.map (CommRingCat.ofHom (algebraMap R S))) (genMap K) :=
  rfl

instance genDiagram_isAffine (j : Jᵒᵖ) : IsAffine ((genDiagram pres K).obj j) := by
  rw [genDiagram_obj]
  exact isAffine_of_isAffineHom (pullback.snd _ (genMap K))

instance genDiagram_isAffineHom {i j : Jᵒᵖ} (f : i ⟶ j) :
    IsAffineHom ((genDiagram pres K).map f) :=
  isAffineHom_of_isAffine _

instance genDiagram_compactSpace (j : Jᵒᵖ) : CompactSpace ((genDiagram pres K).obj j) :=
  inferInstance

instance genDiagram_quasiSeparatedSpace (j : Jᵒᵖ) :
    QuasiSeparatedSpace ((genDiagram pres K).obj j) :=
  inferInstance

/-- The projection of a generic stage to the stage. -/
abbrev genFst (j : Jᵒᵖ) : (genDiagram pres K).obj j ⟶ (specDiagram pres).obj j :=
  pullback.fst _ _

/-- The projection of a generic stage to `Spec K`. -/
abbrev genSnd (j : Jᵒᵖ) : (genDiagram pres K).obj j ⟶ Spec (CommRingCat.of K) :=
  pullback.snd _ _

/-- The projection of the generic limit to the limit. -/
abbrev genFstLim : (genCone pres K).pt ⟶ (specCone pres).pt := pullback.fst _ _

/-- The projection of the generic limit to `Spec K`. -/
abbrev genSndLim : (genCone pres K).pt ⟶ Spec (CommRingCat.of K) := pullback.snd _ _

theorem genCone_π_fst (j : Jᵒᵖ) :
    (genCone pres K).π.app j ≫ genFst pres K j =
      genFstLim pres K ≫ (specCone pres).π.app j := by
  change ((Over.pullback (genMap K)).map ((specConeOver pres).π.app j)).left ≫ pullback.fst _ _ =
    pullback.fst _ _ ≫ ((specConeOver pres).π.app j).left
  simp [Over.pullback_map_left]

theorem genCone_π_snd (j : Jᵒᵖ) :
    (genCone pres K).π.app j ≫ genSnd pres K j = genSndLim pres K := by
  change ((Over.pullback (genMap K)).map ((specConeOver pres).π.app j)).left ≫ pullback.snd _ _ =
    pullback.snd _ _
  simp [Over.pullback_map_left]

theorem genDiagram_map_fst {i j : Jᵒᵖ} (f : i ⟶ j) :
    (genDiagram pres K).map f ≫ genFst pres K j = genFst pres K i ≫ (specDiagram pres).map f := by
  change ((Over.pullback (genMap K)).map ((specDiagramOver pres).map f)).left ≫
      pullback.fst _ _ = pullback.fst _ _ ≫ ((specDiagramOver pres).map f).left
  simp [Over.pullback_map_left]

theorem genDiagram_map_snd {i j : Jᵒᵖ} (f : i ⟶ j) :
    (genDiagram pres K).map f ≫ genSnd pres K j = genSnd pres K i := by
  change ((Over.pullback (genMap K)).map ((specDiagramOver pres).map f)).left ≫
      pullback.snd _ _ = pullback.snd _ _
  simp [Over.pullback_map_left]

end Generic

end ZInQ.Contrib.CloudR2NOS.Spreadout

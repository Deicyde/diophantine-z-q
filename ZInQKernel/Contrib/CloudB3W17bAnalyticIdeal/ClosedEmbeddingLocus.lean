import ZInQKernel.Contrib.CloudB3W17bAnalyticIdeal.InverseImageLocus
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.Geometry.RingedSpace.LocallyRingedSpace.ModulesClosedEmbedding
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-!
# The ideal of a closed embedding of locally ringed spaces and its vanishing locus

For `f : Z ⟶ Y`, the ideal of `f` is the kernel of `𝒪_Y ⟶ f_* 𝒪_Z`. For a closed embedding, its
vanishing locus (where the stalk of the ideal inclusion is not surjective) is exactly the image of
`f`.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite Topology

universe u

namespace ZInQ.Contrib.CloudB3W17bAnalyticIdeal

section ClosedEmbedding

variable {Z Y : LocallyRingedSpace.{u}} (f : Z ⟶ Y)

/-- `𝒪_Y ⟶ f_* 𝒪_Z`. -/
noncomputable abbrev unitToPush : SheafOfModules.unit Y.ringSheaf ⟶
    (SheafOfModules.pushforward.{u} f.toRingSheafHom).obj (SheafOfModules.unit Z.ringSheaf) :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingSheafHom

/-- The ideal of `f`: the kernel of `𝒪_Y ⟶ f_* 𝒪_Z`. -/
noncomputable abbrev closedIdeal : SheafOfModules.{u} Y.ringSheaf := Limits.kernel (unitToPush f)

/-- Its inclusion into `𝒪_Y`. -/
noncomputable abbrev closedIdealι : closedIdeal f ⟶ SheafOfModules.unit Y.ringSheaf :=
  Limits.kernel.ι (unitToPush f)

/-- Off the closed image of `f`, the stalk of the ideal inclusion is surjective. -/
theorem surjective_stalk_closedIdealι_of_not_mem (hcl : IsClosed (Set.range f.base)) (y : Y)
    (hy : y ∉ Set.range f.base) :
    Function.Surjective ((Y.stalkFunctor y).map (closedIdealι f)) := by
  have hS : (ShortComplex.mk (closedIdealι f) (unitToPush f) (kernel.condition _)).Exact :=
    ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)
  have hst := SheafOfModules.stalk_exact_of_exact _ hS y
  rw [ShortComplex.ab_exact_iff] at hst
  have hsub := f.subsingleton_stalk_pushforward hcl y hy (SheafOfModules.unit Z.ringSheaf)
  intro t
  obtain ⟨t₁, ht₁⟩ := hst t (by exact @Subsingleton.elim _ hsub _ _)
  exact ⟨t₁, ht₁⟩

/-- On the image of `f`, the stalk of the ideal inclusion is not surjective. -/
theorem not_surjective_stalk_closedIdealι_of_mem (z : Z) :
    ¬ Function.Surjective ((Y.stalkFunctor (f.base z)).map (closedIdealι f)) := by
  intro hsurj
  obtain ⟨t₁, ht₁⟩ := hsurj (PM.unitStalkGen Y.presheaf (f.base z))
  have hz := ((ShortComplex.mk (closedIdealι f) (unitToPush f) (kernel.condition _)).map
      (SheafOfModules.stalkFunctorAddCommGrp (f.base z))).zero
  have hS0 := congrArg (fun φ => (ConcreteCategory.hom φ) t₁) hz
  simp only [AddCommGrpCat.hom_zero] at hS0
  have hS0' : (Y.stalkFunctor (f.base z)).map (unitToPush f)
      ((Y.stalkFunctor (f.base z)).map (closedIdealι f) t₁) = 0 := by
    exact hS0
  have h0 : (Y.stalkFunctor (f.base z)).map (unitToPush f) (PM.unitStalkGen Y.presheaf (f.base z)) = 0 :=
    (congrArg ((Y.stalkFunctor (f.base z)).map (unitToPush f)) ht₁).symm.trans hS0'
  have h1 := PresheafOfModules.stalkFunctor_map_germ (f.base z)
    (SheafOfModules.unit Y.ringSheaf).val
    ((SheafOfModules.pushforward.{u} f.toRingSheafHom).obj (SheafOfModules.unit Z.ringSheaf)).val
    (unitToPush f).val ⊤ trivial (PM.asUnitSec Y.presheaf (1 : Y.presheaf.obj (op ⊤)))
  have h2 := f.stalkPushforwardModules_germ (SheafOfModules.unit Z.ringSheaf) z ⊤ trivial
    ((unitToPush f).val.app (op ⊤) (PM.asUnitSec Y.presheaf (1 : Y.presheaf.obj (op ⊤))))
  have h3 : ((unitToPush f).val.app (op ⊤) (PM.asUnitSec Y.presheaf (1 : Y.presheaf.obj (op ⊤))) :
      (SheafOfModules.unit Z.ringSheaf).val.obj (op ((Opens.map f.base).obj ⊤))) =
      PM.asUnitSec Z.presheaf (1 : Z.presheaf.obj (op ((Opens.map f.base).obj ⊤))) :=
    (f.toRingSheafHom.hom.app (op ⊤)).hom.map_one
  have e1 : (TopCat.Presheaf.germ ((SheafOfModules.pushforward.{u} f.toRingSheafHom).obj
      (SheafOfModules.unit Z.ringSheaf)).val.presheaf ⊤ (f.base z) trivial
      ((unitToPush f).val.app (op ⊤) (PM.asUnitSec Y.presheaf (1 : Y.presheaf.obj (op ⊤))))) = 0 :=
    h1.symm.trans h0
  have hgen : PM.unitStalkGen Z.presheaf z = 0 :=
    ((PM.unitStalkGen_eq (R := Z.presheaf) (x := z) ((Opens.map f.base).obj ⊤) trivial).trans
      ((congrArg _ h3.symm).trans (h2.symm.trans (congrArg _ e1)))).trans
      ((TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f.base
        (SheafOfModules.unit Z.ringSheaf).val.presheaf z).hom.map_zero)
  have hne : PM.unitStalkMap Z.presheaf z 1 ≠ 0 := by
    intro h
    have := (PM.bijective_unitStalkMap Z.presheaf z).1 (h.trans (map_zero _).symm)
    exact one_ne_zero this
  exact hne ((one_smul _ _).trans hgen)

/-- **The vanishing locus of the ideal of a closed embedding is its image.** -/
theorem vanishingLocus_closedIdeal (hf : IsClosedEmbedding f.base) :
    vanishingLocus (closedIdealι f) = Set.range f.base := by
  ext y
  simp only [vanishingLocus, Set.mem_ofPred_eq]
  constructor
  · intro h
    by_contra hy
    exact h (surjective_stalk_closedIdealι_of_not_mem f hf.isClosed_range y hy)
  · rintro ⟨z, rfl⟩
    exact not_surjective_stalk_closedIdealι_of_mem f z

end ClosedEmbedding

end ZInQ.Contrib.CloudB3W17bAnalyticIdeal

import IntegralResidueActionsSecond
import ActualResidueFrobeniusThird

/-!
# Original-model residue points as actual geometric points of the special fibre

The original integral base map and the actual residue-field base map agree.
Native residue points therefore lift to actual points of the base-change
special fibre. Its Galois covariance is proved from the literal Spec actions
and pullback projections; no point-action model or desired covariance is
supplied as a hypothesis.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Limits

namespace SemistableGeometry.SpecialPointBinding

open SemistableGeometry.IntegralGalois
open SemistableGeometry.IntegralResidueActions
open SemistableGeometry.ActualResidueFrobenius

variable {K : Type} [Field K] [NumberField K]
variable {O : ValuationSubring K} [IsDiscreteValuationRing O]
variable {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
variable {w : ValuationSubring Ω}

/-- The actual integral-closure base map is the original valuation-ring base map. -/
theorem incO_eq_toW (hw : w.comap (algebraMap K Ω) = O) :
    FrobLift.incO hw = PkgI2.toW O w hw := by
  ext a
  exact FrobLift.incO_coe hw a

/-- Compatibility is with the literal original integral model base map. -/
theorem residueBase_original (hw : w.comap (algebraMap K Ω) = O) (a : O) :
    residueBase hw (IsLocalRing.residue O a) = IsLocalRing.residue w (PkgI2.toW O w hw a) := by
  have h := congrArg (fun f : O →+* IsLocalRing.ResidueField w ↦ f a)
    (residueBase_comp_residue hw)
  simpa only [RingHom.comp_apply, incO_eq_toW hw] using h

abbrev specialBase : Spec (CommRingCat.of (IsLocalRing.ResidueField O)) ⟶ Spec (CommRingCat.of O) :=
  Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))

abbrev specialDomain (hw : w.comap (algebraMap K Ω) = O) :
    Over (Spec (CommRingCat.of (IsLocalRing.ResidueField O))) :=
  Over.mk (Spec.map (CommRingCat.ofHom (residueBase hw)))

abbrev specialFibre (N : Over (Spec (CommRingCat.of O))) :
    Over (Spec (CommRingCat.of (IsLocalRing.ResidueField O))) :=
  (Over.pullback (specialBase (O := O))).obj N

/-- The actual geometric residue domain lies over the actual original residue domain. -/
theorem specialDomain_base (hw : w.comap (algebraMap K Ω) = O) :
    (specialDomain hw).hom ≫ specialBase = (residueDomain w hw).hom := by
  change Spec.map (CommRingCat.ofHom (residueBase hw)) ≫
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)) =
    Spec.map (CommRingCat.ofHom ((IsLocalRing.residue w).comp (PkgI2.toW O w hw)))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, residueBase_comp_residue, incO_eq_toW hw]

/-- The actual residue model point is an actual point of the base-change special fibre. -/
def specialPoint (hw : w.comap (algebraMap K Ω) = O)
    (N : Over (Spec (CommRingCat.of O))) (a : residueDomain w hw ⟶ N) :
    specialDomain hw ⟶ specialFibre N :=
  Over.homMk (pullback.lift a.left (specialDomain hw).hom (by
    rw [Over.w a, specialDomain_base])) (pullback.lift_snd _ _ _)

/-- Its first projection is the original residue model point. -/
theorem specialPoint_fst (hw : w.comap (algebraMap K Ω) = O)
    (N : Over (Spec (CommRingCat.of O))) (a : residueDomain w hw ⟶ N) :
    (specialPoint hw N a).left ≫ pullback.fst N.hom (specialBase (O := O)) = a.left :=
  pullback.lift_fst _ _ _

/-- Its second projection is the actual geometric residue base map. -/
theorem specialPoint_snd (hw : w.comap (algebraMap K Ω) = O)
    (N : Over (Spec (CommRingCat.of O))) (a : residueDomain w hw ⟶ N) :
    (specialPoint hw N a).left ≫ pullback.snd N.hom (specialBase (O := O)) =
      (specialDomain hw).hom := pullback.lift_snd _ _ _

/-- The actual special-point lift is injective, by its actual first projection. -/
theorem specialPoint_injective (hw : w.comap (algebraMap K Ω) = O)
    (N : Over (Spec (CommRingCat.of O))) : Function.Injective (specialPoint hw N) := by
  intro a b h
  apply Over.OverMorphism.ext
  have he := congrArg (fun x : specialDomain hw ⟶ specialFibre N ↦
    x.left ≫ pullback.fst N.hom (specialBase (O := O))) h
  simpa only [specialPoint_fst] using he

/-- The native decomposition action fixes the actual finite residue base. -/
theorem residueRingAction_residueBase (hw : w.comap (algebraMap K Ω) = O)
    (σ : Ω ≃ₐ[K] Ω) (hD : σ ∈ w.decompositionSubgroup K) :
    (residueRingAction w σ hD).comp (residueBase hw) = residueBase hw := by
  ext a
  obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective a
  rw [RingHom.comp_apply, residueBase_original]
  have h := congrArg (fun f : O →+* IsLocalRing.ResidueField w ↦ f b)
    (residueRingAction_base w hw σ hD)
  exact h

/-- The literal native residue Spec action over the actual residue base. -/
def specialActionArrow (hw : w.comap (algebraMap K Ω) = O)
    (σ : Ω ≃ₐ[K] Ω) (hD : σ ∈ w.decompositionSubgroup K) :
    specialDomain hw ⟶ specialDomain hw :=
  Over.homMk (Spec.map (CommRingCat.ofHom (residueRingAction w σ hD))) (by
    change Spec.map (CommRingCat.ofHom (residueRingAction w σ hD)) ≫
      Spec.map (CommRingCat.ofHom (residueBase hw)) = Spec.map (CommRingCat.ofHom (residueBase hw))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, residueRingAction_residueBase])

/-- Actual covariance into the actual original model's special fibre. -/
theorem specialPoint_covariance (hw : w.comap (algebraMap K Ω) = O)
    (N : Over (Spec (CommRingCat.of O))) (σ : Ω ≃ₐ[K] Ω)
    (hD : σ ∈ w.decompositionSubgroup K) (a : residueDomain w hw ⟶ N) :
    specialActionArrow hw σ hD ≫ specialPoint hw N a =
      specialPoint hw N (residueActionArrow w hw σ hD ≫ a) := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.comp_left, Category.assoc, specialPoint_fst]
    rfl
  · simp only [Over.comp_left, Category.assoc, specialPoint_snd]
    exact Over.w (specialActionArrow hw σ hD)

end SemistableGeometry.SpecialPointBinding

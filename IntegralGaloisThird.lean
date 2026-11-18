import ZInQKernel.HDecomp.Objects

/-!
# Original geometric points and valuation-ring Galois covariance

The valuation-ring action of a decomposition element and its actual Spec
map give the native integral-section action. A pullback calculation proves
covariance of the actual generic-fibre map with the original abelian point
action. Inertia is then shown to preserve the actual reduction morphism.
No invariant-point field of definition or monodromy statement is assumed.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace SemistableGeometry.IntegralGalois

variable {K : Type} [Field K] {O : ValuationSubring K}
variable {Ω : Type} [Field Ω] [Algebra K Ω]

abbrev base : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of O) :=
  Spec.map (CommRingCat.ofHom (algebraMap O K))

abbrev valuationDomain (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O) :
    Over (Spec (CommRingCat.of O)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW O w hw)))

abbrev residueDomain (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O) :
    Over (Spec (CommRingCat.of O)) :=
  Over.mk (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue w).comp (PkgI2.toW O w hw))))

def reductionArrow (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O) :
    residueDomain w hw ⟶ valuationDomain w hw :=
  Over.homMk (Spec.map (CommRingCat.ofHom (IsLocalRing.residue w))) (by
    change Spec.map (CommRingCat.ofHom (IsLocalRing.residue w)) ≫
      Spec.map (CommRingCat.ofHom (PkgI2.toW O w hw)) =
      Spec.map (CommRingCat.ofHom ((IsLocalRing.residue w).comp (PkgI2.toW O w hw)))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp])

def valuationAction (w : ValuationSubring Ω) (σ : Ω ≃ₐ[K] Ω)
    (hd : σ ∈ w.decompositionSubgroup K) : w →+* w :=
  MulSemiringAction.toRingHom (w.decompositionSubgroup K) w ⟨σ, hd⟩

/-- The actual valuation action fixes the given base ring pointwise. -/
theorem valuationAction_base (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O)
    (σ : Ω ≃ₐ[K] Ω) (hd : σ ∈ w.decompositionSubgroup K) :
    (valuationAction w σ hd).comp (PkgI2.toW O w hw) = PkgI2.toW O w hw := by
  ext a
  change σ (algebraMap K Ω (a : K)) = algebraMap K Ω (a : K)
  exact σ.commutes _

def valuationActionArrow (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O)
    (σ : Ω ≃ₐ[K] Ω) (hd : σ ∈ w.decompositionSubgroup K) :
    valuationDomain w hw ⟶ valuationDomain w hw :=
  Over.homMk (Spec.map (CommRingCat.ofHom (valuationAction w σ hd))) (by
    change Spec.map (CommRingCat.ofHom (valuationAction w σ hd)) ≫
      Spec.map (CommRingCat.ofHom (PkgI2.toW O w hw)) =
      Spec.map (CommRingCat.ofHom (PkgI2.toW O w hw))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, valuationAction_base])

def genericDomainLift (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O) :
    PkgI3.AbVar.ptObj (K := K) Ω ⟶ (Over.pullback (base (O := O))).obj (valuationDomain w hw) := by
  let a := Spec.map (CommRingCat.ofHom w.subtype)
  let b := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  have h : a ≫ (valuationDomain w hw).hom = b ≫ base := by
    change Spec.map (CommRingCat.ofHom w.subtype) ≫ Spec.map (CommRingCat.ofHom (PkgI2.toW O w hw)) =
      Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ Spec.map (CommRingCat.ofHom (algebraMap O K))
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  exact Over.homMk (pullback.lift a b h) (pullback.lift_snd _ _ _)

lemma genericDomainLift_fst (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O) :
    (genericDomainLift w hw).left ≫ pullback.fst (valuationDomain w hw).hom (base (O := O)) =
      Spec.map (CommRingCat.ofHom w.subtype) := pullback.lift_fst _ _ _

lemma genericDomainLift_snd (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O) :
    (genericDomainLift w hw).left ≫ pullback.snd (valuationDomain w hw).hom (base (O := O)) =
      (PkgI3.AbVar.ptObj (K := K) Ω).hom := pullback.lift_snd _ _ _

/-- The actual two Spec actions commute with the canonical valuation/generic pullback lift. -/
theorem genericDomainLift_covariance (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) (σ : Ω ≃ₐ[K] Ω)
    (hd : σ ∈ w.decompositionSubgroup K) :
    PkgI3.AbVar.galHom σ ≫ genericDomainLift w hw =
      genericDomainLift w hw ≫ (Over.pullback (base (O := O))).map (valuationActionArrow w hw σ hd) := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · have hfst : ((Over.pullback (base (O := O))).map (valuationActionArrow w hw σ hd)).left ≫
        pullback.fst (valuationDomain w hw).hom (base (O := O)) =
        pullback.fst (valuationDomain w hw).hom (base (O := O)) ≫
          (valuationActionArrow w hw σ hd).left := pullback.lift_fst _ _ _
    simp only [Over.comp_left, Category.assoc, hfst]
    rw [← Category.assoc (genericDomainLift w hw).left
      (pullback.fst (valuationDomain w hw).hom (base (O := O)))
      (valuationActionArrow w hw σ hd).left, genericDomainLift_fst]
    change Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ Spec.map (CommRingCat.ofHom w.subtype) =
      Spec.map (CommRingCat.ofHom w.subtype) ≫ Spec.map (CommRingCat.ofHom (valuationAction w σ hd))
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  · have hsnd : ((Over.pullback (base (O := O))).map (valuationActionArrow w hw σ hd)).left ≫
        pullback.snd (valuationDomain w hw).hom (base (O := O)) =
        pullback.snd (valuationDomain w hw).hom (base (O := O)) :=
      Over.w ((Over.pullback (base (O := O))).map (valuationActionArrow w hw σ hd))
    simp only [Over.comp_left, Category.assoc, hsnd, genericDomainLift_snd]
    exact Over.w (PkgI3.AbVar.galHom σ)

/-- The actual generic-fibre formula for the original abelian point. -/
def originalPoint {A : PkgI3.AbVar K} (N : Over (Spec (CommRingCat.of O)))
    (gen : (Over.pullback (base (O := O))).obj N ≅ A.X)
    (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O)
    (a : valuationDomain w hw ⟶ N) : A.Pt Ω :=
  genericDomainLift w hw ≫ (Over.pullback (base (O := O))).map a ≫ gen.hom

/-- Covariance lands in the original A.Pt/galAct, not a substituted representation. -/
theorem originalPoint_covariance {A : PkgI3.AbVar K}
    (N : Over (Spec (CommRingCat.of O))) (gen : (Over.pullback (base (O := O))).obj N ≅ A.X)
    (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O)
    (σ : Ω ≃ₐ[K] Ω) (hd : σ ∈ w.decompositionSubgroup K) (a : valuationDomain w hw ⟶ N) :
    originalPoint N gen w hw (valuationActionArrow w hw σ hd ≫ a) =
      A.galAct σ (originalPoint N gen w hw a) := by
  change genericDomainLift w hw ≫ (Over.pullback (base (O := O))).map
      (valuationActionArrow w hw σ hd ≫ a) ≫ gen.hom =
    PkgI3.AbVar.galHom σ ≫ (genericDomainLift w hw ≫ (Over.pullback (base (O := O))).map a ≫ gen.hom)
  rw [Functor.map_comp]
  simpa only [Category.assoc] using congrArg
    (fun f ↦ f ≫ (Over.pullback (base (O := O))).map a ≫ gen.hom)
    (genericDomainLift_covariance w hw σ hd).symm

/-- Literal inertia fixes the actual valuation-ring residue map. -/
theorem inertia_residue_map (w : ValuationSubring Ω) (σ : Ω ≃ₐ[K] Ω)
    (hσ : PkgI2.IsInertia w σ) :
    (IsLocalRing.residue w).comp (valuationAction w σ hσ.1) = IsLocalRing.residue w := by
  ext a
  have hi := hσ.2
  rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker] at hi
  have he := RingEquiv.congr_fun hi (IsLocalRing.residue w a)
  change (⟨σ, hσ.1⟩ : w.decompositionSubgroup K) • IsLocalRing.residue w a =
    IsLocalRing.residue w a at he
  rw [← IsLocalRing.ResidueField.residue_smul] at he
  exact he

/-- Every native section has the same actual reduction after an inertia action. -/
theorem inertia_section_reduction (N : Over (Spec (CommRingCat.of O)))
    (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O)
    (σ : Ω ≃ₐ[K] Ω) (hσ : PkgI2.IsInertia w σ) (a : valuationDomain w hw ⟶ N) :
    reductionArrow w hw ≫ (valuationActionArrow w hw σ hσ.1 ≫ a) = reductionArrow w hw ≫ a := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (IsLocalRing.residue w)) ≫
    (Spec.map (CommRingCat.ofHom (valuationAction w σ hσ.1)) ≫ a.left) =
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue w)) ≫ a.left
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, inertia_residue_map w σ hσ]

end SemistableGeometry.IntegralGalois

import ZInQKernel.Contrib.OneProof.RC.ModelTarget.DetectorModel
import ZInQKernel.Contrib.OneProof.RC.ModelTarget.PullbackMul
import ZInQKernel.Contrib.OneProof.RC.ModelNeron.Source
import ZInQKernel.Contrib.OneProof.RC.PMQuotient.Model
import ZInQKernel.Contrib.OneProof.RC.Stages.ReducedCurve
import ZInQKernel.Contrib.OneProof.RC.PMGeometry.Evaluation

/-! The residue reading of the good cubic, tex 8477–8479: points of the special fibre with
values in the detector's residue field `K`, with the group law induced from the cubic,
are the affine points of the reduction of the good equation over `K`. The reading is the
actual reduction of the points of `W`: a residue point of the special fibre is a point of
the cubic over `R → 𝔽_ℓ → K`, and its value is its solution vector read on the reduced
equation. It commutes with the arithmetic Frobenius. On the spot (c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open WeierstrassCurve WeierstrassCurve.ModelTorsion
open scoped WeierstrassCurve CategoryTheory.Obj WeierstrassCurve.Projective

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ZInQ.Manuscript.RC.ModelTarget

open PMQuotient (residueSource residueFrob)
open PMGeometry (ReducedEquation)

/-- Points of equal curves. -/
def pointCongr {K : Type} [Field K] [DecidableEq K] {W₁ W₂ : WeierstrassCurve K} (h : W₁ = W₂) :
    W₁.toAffine.Point ≃+ W₂.toAffine.Point := by
  subst h
  exact AddEquiv.refl _

theorem pointCongr_toAffine {K : Type} [Field K] [DecidableEq K] {W₁ W₂ : WeierstrassCurve K}
    (h : W₁ = W₂) (v : Fin 3 → K) :
    pointCongr h (Projective.Point.toAffine W₁.toProjective v) =
      Projective.Point.toAffine W₂.toProjective v := by
  subst h
  rfl

/-- An algebra map of fields moves the affine point of a vector to that of its image. -/
theorem map_toAffine {S K : Type} [CommRing S] [Field K] [Algebra S K] [DecidableEq K]
    (E : WeierstrassCurve S) (σ : K →ₐ[S] K) (v : Fin 3 → K) :
    Affine.Point.map (W' := E) σ (Projective.Point.toAffine (E⁄K).toProjective v) =
      Projective.Point.toAffine (E⁄K).toProjective (σ ∘ v) := by
  by_cases hns : (E⁄K).toProjective.Nonsingular v
  · have hns' : (E⁄K).toProjective.Nonsingular (σ ∘ v) :=
      (Projective.baseChange_nonsingular (W' := E.toProjective) σ.injective v).mpr hns
    by_cases hz : v 2 = 0
    · rw [Projective.Point.toAffine_of_Z_eq_zero hz,
        Projective.Point.toAffine_of_Z_eq_zero (show (σ ∘ v) 2 = 0 by simp [hz])]
      rfl
    · have hz' : (σ ∘ v) 2 ≠ 0 := by simpa using hz
      rw [Projective.Point.toAffine_of_Z_ne_zero hns hz, Projective.Point.toAffine_of_Z_ne_zero hns' hz',
        Affine.Point.map_some]
      simp [map_div₀]
  · have hns' : ¬ (E⁄K).toProjective.Nonsingular (σ ∘ v) := fun h =>
      hns ((Projective.baseChange_nonsingular (W' := E.toProjective) σ.injective v).mp h)
    rw [Projective.Point.toAffine_of_singular hns, Projective.Point.toAffine_of_singular hns']
    rfl

variable (ell : ℕ) [Fact ell.Prime] (W₀ : WeierstrassCurve ℤ)
  (K : Type) [Field K] [Algebra (ZMod ell) K] [DecidableEq K]

/-- The good cubic at the detector, as the object used by `PMWire.GoodRow`. -/
abbrev detE : Over (Spec (.of (LocalIntegers ell))) := ModelNeron.weierstrassModel ell (detW ell W₀)

/-- The ring map from the detector ring to the residue field `K`. -/
abbrev resRing : LocalIntegers ell →+* K := (algebraMap (ZMod ell) K).comp (ModelNeron.closed ell)

/-- The special fibre functor at the detector. -/
abbrev special : Over (Spec (.of (LocalIntegers ell))) ⥤ Over (Spec (.of (ZMod ell))) :=
  Over.pullback (Spec.map (CommRingCat.ofHom (ModelNeron.closed ell)))

theorem resRing_curve : (detW ell W₀).map (resRing ell K) = (ReducedEquation W₀ ell)⁄K := by
  rw [detW_map_eq (resRing ell K) ((algebraMap (ZMod ell) K).comp (Int.castRingHom (ZMod ell)))]
  exact (WeierstrassCurve.map_map W₀ _ _).symm

omit [DecidableEq K] in
theorem residue_structure :
    (residueSource ell K).hom ≫ Spec.map (CommRingCat.ofHom (ModelNeron.closed ell)) =
      Spec.map (CommRingCat.ofHom (resRing ell K)) := by
  change Spec.map _ ≫ _ = _
  rw [← Spec.map_comp, CommRingCat.ofHom_comp]

/-- The comparison of the residue point object with the field point over the detector ring. -/
def residueIso : fieldPt (resRing ell K) ≅ Over.mk ((residueSource ell K).hom ≫
    Spec.map (CommRingCat.ofHom (ModelNeron.closed ell))) :=
  Over.isoMk (Iso.refl _) (by simp [residue_structure])

variable {ell W₀ K}

/-- A residue point of the special fibre, read as a point of the cubic over `R → K`. -/
def resUp (y : residueSource ell K ⟶ (special ell).obj (detE ell W₀)) :
    fieldPt (resRing ell K) ⟶ cubic (detW ell W₀) :=
  (residueIso ell K).hom ≫ (upHom _ (detE ell W₀) y : _ ⟶ cubic (detW ell W₀))

theorem resUp_left (y : residueSource ell K ⟶ (special ell).obj (detE ell W₀)) :
    (resUp y).left = y.left ≫ pullback.fst _ _ := by
  change 𝟙 _ ≫ (y.left ≫ pullback.fst _ _) = _
  rw [Category.id_comp]

/-- The value of a residue point on the reduced equation. -/
def readFun (y : residueSource ell K ⟶ (special ell).obj (detE ell W₀)) :
    ((ReducedEquation W₀ ell)⁄K).toAffine.Point :=
  pointCongr (resRing_curve ell W₀ K) (val (detW ell W₀) (resUp y))

theorem readFun_mul (h₅ : 5 ≤ ell) (hΔ : ¬ (ell : ℤ) ∣ W₀.Δ)
    (y z : residueSource ell K ⟶ (special ell).obj (detE ell W₀)) :
    letI := weierstrassModelGrp ell h₅ W₀ hΔ
    readFun (y * z) = readFun y + readFun z := by
  letI := weierstrassModelGrp ell h₅ W₀ hΔ
  haveI := ModelNeron.isElliptic_at_detector ell W₀ hΔ
  haveI : IsReduced (cubic (detW ell W₀) ⊗ cubic (detW ell W₀)).left :=
    isReduced_of_smooth_hom (ZInQ.Contrib.NeronC.smooth_tensor _ _
      (weierstrassModel_smooth ell h₅ W₀ hΔ) (weierstrassModel_smooth ell h₅ W₀ hΔ))
  simp only [readFun, ← map_add]
  congr 1
  have e : resUp (y * z) = lift (resUp y) (resUp z) ≫ cubicMul (detW ell W₀) := by
    apply Over.OverMorphism.ext
    rw [resUp_left, mul_left_fst]
    simp only [resUp, Over.comp_left, comp_lift]
    simp [residueIso]
    rfl
  rw [e, val_mul]

#print axioms map_toAffine
#print axioms readFun_mul

end ZInQ.Manuscript.RC.ModelTarget

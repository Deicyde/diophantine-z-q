import ZInQKernel.Contrib.OneProof.SZThm33.ToricKernelPairs
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! The torus-kernel comparison over arbitrary rings applies to every
test scheme by taking affine fpqc refinements of the two base points. -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ.HeightSplit ZInQ.ChevFree DictModels.RaynaudOr SmoothGroup

set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 180000
set_option backward.isDefEq.respectTransparency false

namespace SZRaynaud

/-- Two field-valued base structures on an affine scheme both lift to the
extension field after one affine fpqc refinement. -/
theorem exists_affine_fpqc_refinement_of_two_maps
    {F L : Type} [Field F] [Field L] [Algebra F L]
    {X : Scheme} [IsAffine X] (a b : X ⟶ Spec (.of F)) :
    ∃ (R : Type) (_ : CommRing R) (p : Spec (.of R) ⟶ X) (_ : Epi p)
      (ra rb : L →+* R),
      Spec.map (CommRingCat.ofHom ra) ≫ Spec.map (CommRingCat.ofHom (algebraMap F L)) = p ≫ a ∧
      Spec.map (CommRingCat.ofHom rb) ≫ Spec.map (CommRingCat.ofHom (algebraMap F L)) = p ≫ b := by
  let c := Spec.map (CommRingCat.ofHom (algebraMap F L))
  haveI : Flat c := (fpqc_specField F L).1
  haveI : Surjective c := (fpqc_specField F L).2
  haveI : IsAffineHom c := isAffineHom_of_isAffine c
  let X₁ := pullback a c
  let p₁ : X₁ ⟶ X := pullback.fst a c
  haveI : IsAffine X₁ := isAffine_of_isAffineHom p₁
  let X₂ := pullback (p₁ ≫ b) c
  let p₂ : X₂ ⟶ X₁ := pullback.fst (p₁ ≫ b) c
  haveI : IsAffine X₂ := isAffine_of_isAffineHom p₂
  haveI : Epi p₁ := inferInstanceAs (Epi (pullback.fst a c))
  haveI : Epi p₂ := inferInstanceAs (Epi (pullback.fst (p₁ ≫ b) c))
  let R := Γ(X₂, ⊤)
  let t : Spec (.of R) ⟶ X₂ := X₂.isoSpec.inv
  let p : Spec (.of R) ⟶ X := t ≫ p₂ ≫ p₁
  haveI : IsIso t := inferInstanceAs (IsIso X₂.isoSpec.inv)
  haveI : Epi p := inferInstanceAs (Epi (t ≫ p₂ ≫ p₁))
  let A := t ≫ p₂ ≫ pullback.snd a c
  let B := t ≫ pullback.snd (p₁ ≫ b) c
  obtain ⟨ra, hra⟩ := Spec.map_surjective A
  obtain ⟨rb, hrb⟩ := Spec.map_surjective B
  refine ⟨R, inferInstance, p, inferInstance, ra.hom, rb.hom, ?_, ?_⟩
  · change Spec.map ra ≫ c = p ≫ a
    rw [hra]
    simp only [A, p, p₁, Category.assoc, ← pullback.condition]
  · change Spec.map rb ≫ c = p ≫ b
    rw [hrb]
    simp only [B, p, p₂, Category.assoc, ← pullback.condition]

section FiniteStage

variable {k : Type} [Field k] {U : Over (Spec (CommRingCat.of k))} [GrpObj U]
  {B' : PkgI3.AbVar (AlgebraicClosure k)}
  {k₁ : Type} [Field k₁] [Algebra k k₁] [Algebra k₁ (AlgebraicClosure k)]
  [IsScalarTower k k₁ (AlgebraicClosure k)]

set_option backward.isDefEq.respectTransparency.types false in
/-- The quotient kernel transports across every base point of the finite
stage, even when the stage is inseparable. -/
theorem KI_of_toric_kernel
    (π' : (Over.pullback (sφ (φbar k))).obj U ⟶ B'.X)
    (hπ : letI := B'.grp; letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
      IsMonHom π') (r : ℕ)
    (e : letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
      ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R],
      (Fin r → Rˣ) →* (algPt (AlgebraicClosure k) R ⟶ (Over.pullback (sφ (φbar k))).obj U))
    (he_ker : letI := B'.grp; letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
      ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R]
      (u : algPt (AlgebraicClosure k) R ⟶ (Over.pullback (sφ (φbar k))).obj U),
      u ≫ π' = 1 ↔ u ∈ (e R).range)
    (he_nat : ∀ (R S : Type) [CommRing R] [Algebra (AlgebraicClosure k) R] [CommRing S]
      [Algebra (AlgebraicClosure k) S] (f : R →ₐ[AlgebraicClosure k] S) (t : Fin r → Rˣ),
      e S (fun i => Units.map (f : R →* S) (t i)) = algPtMap f ≫ e R t)
    (X₁ : Over (Spec (CommRingCat.of k₁))) (π₁ : (Over.pullback (qq k k₁)).obj U ⟶ X₁)
    (c : B'.X.left ⟶ X₁.left) (hc : IsPullback c B'.X.hom X₁.hom (q₂ k k₁))
    (hcompat : π'.left ≫ c = rr U k₁ ≫ π₁.left) :
    KI (qq k k₁) π₁ := by
  intro Z u v a b hu hv hb h
  apply Z.affineCover.hom_ext
  intro i
  let d := Z.affineCover.f i
  obtain ⟨R, hR, p, hp, ra, rb, hra, hrb⟩ :=
    exists_affine_fpqc_refinement_of_two_maps (L := AlgebraicClosure k) (d ≫ a) (d ≫ b)
  letI : CommRing R := hR
  haveI : Epi p := hp
  let ρ := p ≫ d
  apply (cancel_epi p).mp
  simp only [← Category.assoc]
  change (ρ ≫ pullback.lift u b (hu.trans hb)) ≫ π₁.left =
      (ρ ≫ pullback.lift v b (hv.trans hb)) ≫ π₁.left
  rw [← lift_comp_left U.hom (qq k k₁) ρ u b (hu.trans hb),
    ← lift_comp_left U.hom (qq k k₁) ρ v b (hv.trans hb)]
  refine algebra_KI_of_ext_structure π' hπ r e he_ker he_nat X₁ π₁ c hc hcompat R (ρ ≫ u) (ρ ≫ v)
    (ρ ≫ a) (ρ ≫ b) ra rb (by simpa [ρ, Category.assoc] using hra)
    (by simpa [ρ, Category.assoc] using hrb) (by simp [Category.assoc, hu])
    (by simp [Category.assoc, hv]) (by simp [Category.assoc, hb]) ?_
  rw [lift_comp_left U.hom (qq k k₁) ρ u a hu, lift_comp_left U.hom (qq k k₁) ρ v a hv]
  simpa only [ρ, Category.assoc] using congrArg (ρ ≫ ·) h

end FiniteStage

#print axioms exists_affine_fpqc_refinement_of_two_maps
#print axioms KI_of_toric_kernel

end SZRaynaud

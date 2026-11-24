import ZInQKernel.Contrib.CloudR2Poincare.L2.GlobalFibreTriviality
import ZInQKernel.Contrib.CloudR2Poincare.L1.Normalization

/-!
# Relative-family residue fibres and arbitrary parameter pullback

These are actual pullback-square identities for Picard classes. They compare
the native scheme-theoretic residue fibre with the relative Picard presheaf's
parameter restriction, and preserve fibre triviality under ANY base change.
No global normalized seesaw is assumed or proved in this module.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Limits

namespace ZInQ.Contrib.CloudR2Poincare.L2

universe u

/-- The actual residue-field scheme as a parameter over the original base. -/
def residueParameter {S : Scheme.{u}} (T : Over S) (t : T.left) : Over S :=
  Over.mk (T.left.fromSpecResidueField t ≫ T.hom)

/-- The canonical residue-field parameter map, with its actual structural equation. -/
def residueParameterMap {S : Scheme.{u}} (T : Over S) (t : T.left) : residueParameter T t ⟶ T :=
  Over.homMk (T.left.fromSpecResidueField t)

/-- Arbitrary parameter change preserves triviality of the corresponding
original residue fibre, with no residue-field-isomorphism assumption. -/
theorem fibrePicardClass_baseChange_of_eq_one {P X U Y : Scheme.{u}}
    {fst : P ⟶ X} {snd : P ⟶ U} {f : X ⟶ Y} {g : U ⟶ Y}
    (h : IsPullback fst snd f g) (L : X.Pic) (u : U)
    (hL : Scheme.Pic.map (f.fiberι (g u)) L = 1) :
    Scheme.Pic.map (snd.fiberι u) (Scheme.Pic.map fst L) = 1 := by
  rw [← Scheme.Pic.map_comp, ← fibreComparison_fiberι h u,
    Scheme.Pic.map_comp, hL, Scheme.Pic.map_one]

/-- The relative Picard parameter pullback at t agrees, up to a genuine
isomorphism, with the actual scheme-theoretic fibre of the parameter projection. -/
theorem relativeFibrePicardClass_eq_one_iff {X S : Scheme.{u}}
    (π : X ⟶ S) (T : Over S) (L : (pullback π T.hom).Pic) (t : T.left) :
    Scheme.Pic.map ((pullback.snd π T.hom).fiberι t) L = 1 ↔
      Scheme.Pic.map (JacobianChallenge.baseChangeMap π (residueParameterMap T t)) L = 1 := by
  let q := T.left.fromSpecResidueField t
  let h := (IsPullback.of_hasPullback (pullback.snd π T.hom) q).paste_horiz
    (IsPullback.of_hasPullback π T.hom)
  let e := h.isoPullback
  have he : e.hom ≫ JacobianChallenge.baseChangeMap π (residueParameterMap T t) =
      (pullback.snd π T.hom).fiberι t := by
    apply pullback.hom_ext
    · simp [e, residueParameterMap, residueParameter, JacobianChallenge.baseChangeMap,
        Scheme.Hom.fiberι, Scheme.Hom.fiber, Category.assoc]
      simpa only [q] using h.isoPullback_hom_fst
    · simp [e, residueParameterMap, residueParameter, JacobianChallenge.baseChangeMap,
        Scheme.Hom.fiberι, Scheme.Hom.fiber, Category.assoc, pullback.condition]
      simpa only [q, Category.assoc] using
        congrArg (fun m => m ≫ q) h.isoPullback_hom_snd
  have heq : Scheme.Pic.map e.hom
      (Scheme.Pic.map (JacobianChallenge.baseChangeMap π (residueParameterMap T t)) L) =
      Scheme.Pic.map ((pullback.snd π T.hom).fiberι t) L := by
    rw [← Scheme.Pic.map_comp, he]
  rw [← heq]
  constructor
  · intro ht
    apply L1.pic_map_injective_of_isIso e.hom
    simpa only [Scheme.Pic.map_one] using ht
  · intro ht
    rw [ht, Scheme.Pic.map_one]

/-- Specialization of the normalized polarization self-family at a residue
point is its actual normalized family on that residue-field test scheme. -/
theorem normalizedSelfFamily_residueFibre_eq_one_iff
    {S : Scheme.{u}} (A : Over S) [MonObj A] (L : A.left.Pic) (t : A.left) :
    Scheme.Pic.map ((pullback.snd A.hom A.hom).fiberι t)
      (L1.normalizedPolarizationFamily A L (𝟙 A)) = 1 ↔
    L1.normalizedPolarizationFamily A L (residueParameterMap A t) = 1 := by
  rw [relativeFibrePicardClass_eq_one_iff, L1.normalizedPolarizationFamily_parameter,
    Category.comp_id]

end ZInQ.Contrib.CloudR2Poincare.L2

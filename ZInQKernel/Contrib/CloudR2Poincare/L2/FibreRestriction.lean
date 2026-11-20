import Mathlib.AlgebraicGeometry.Fiber
import ZInQKernel.Contrib.CloudR2Poincare.L1.PicardKernel

/-!
# Native residue-fibre Picard classes under open base change

The actual scheme-theoretic fibre comparison in Mathlib is a pullback of the
residue-field map. An open immersion makes that map an isomorphism, so the
comparison is an isomorphism and detects triviality of actual Picard classes.
This is the compatibility needed to glue the affine fibre-triviality loci.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Limits

namespace ZInQ.Contrib.CloudR2Poincare.L2

universe u

/-- The actual comparison from a base-changed residue fibre to the original
residue fibre, with the canonical change of residue field. -/
def fibreComparison {P X U Y : Scheme.{u}}
    {fst : P ⟶ X} {snd : P ⟶ U} {f : X ⟶ Y} {g : U ⟶ Y}
    (h : IsPullback fst snd f g) (u : U) : snd.fiber u ⟶ f.fiber (g u) :=
  pullback.map _ _ _ _ fst (Spec.map (g.residueFieldMap u)) g h.w.symm (by simp)

/-- Open base change does not change the actual fibre up to isomorphism. -/
instance fibreComparison_isIso {P X U Y : Scheme.{u}}
    {fst : P ⟶ X} {snd : P ⟶ U} {f : X ⟶ Y} {g : U ⟶ Y}
    (h : IsPullback fst snd f g) [IsOpenImmersion g] (u : U) :
    IsIso (fibreComparison h u) := by
  have h' := isPullback_fiberToSpecResidueField_of_isPullback h u
  exact h'.isIso_fst_of_isIso

/-- The fibre comparison commutes with the actual source projections. -/
@[reassoc]
theorem fibreComparison_fiberι {P X U Y : Scheme.{u}}
    {fst : P ⟶ X} {snd : P ⟶ U} {f : X ⟶ Y} {g : U ⟶ Y}
    (h : IsPullback fst snd f g) (u : U) :
    fibreComparison h u ≫ f.fiberι (g u) = snd.fiberι u ≫ fst := by
  simp [fibreComparison, Scheme.Hom.fiber, Scheme.Hom.fiberι]

/-- Triviality of a residue-fibre Picard class is Zariski-local on the
parameter scheme, via an actual isomorphism of the residue fibres. -/
theorem fibrePicardClass_open_baseChange_iff {P X U Y : Scheme.{u}}
    {fst : P ⟶ X} {snd : P ⟶ U} {f : X ⟶ Y} {g : U ⟶ Y}
    (h : IsPullback fst snd f g) [IsOpenImmersion g] (L : X.Pic) (u : U) :
    Scheme.Pic.map (snd.fiberι u) (Scheme.Pic.map fst L) = 1 ↔
      Scheme.Pic.map (f.fiberι (g u)) L = 1 := by
  have heq : Scheme.Pic.map (fibreComparison h u)
      (Scheme.Pic.map (f.fiberι (g u)) L) =
      Scheme.Pic.map (snd.fiberι u) (Scheme.Pic.map fst L) := by
    rw [← Scheme.Pic.map_comp, fibreComparison_fiberι, Scheme.Pic.map_comp]
  rw [← heq]
  constructor
  · intro hz
    apply L1.pic_map_injective_of_isIso (fibreComparison h u)
    simpa only [Scheme.Pic.map_one] using hz
  · intro hz
    rw [hz, Scheme.Pic.map_one]

end ZInQ.Contrib.CloudR2Poincare.L2

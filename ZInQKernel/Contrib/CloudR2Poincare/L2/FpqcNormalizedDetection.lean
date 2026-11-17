import ZInQKernel.Contrib.CloudR2Poincare.L1.Normalization
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Sites.Fpqc

/-!
# Actual fpqc detection of normalized Picard-class equality

A pointed proper geometrically integral scheme's normalized Picard presheaf
is a genuine fpqc sheaf. Equality is therefore detected on an actual fpqc
cover, including arbitrary field extensions. This is NOT an inference from
all residue-field points covering a reduced parameter scheme, and does not
assume global seesaw or canonical H0 base-change.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Limits Opposite

namespace ZInQ.Contrib.CloudR2Poincare.L2

universe u

/-- Genuine fpqc equality detection for normalized families, using the actual
native normalized-Picard/fpqc isomorphism and a SINGLE covering morphism. -/
theorem normalizedPicard_eq_of_fpqc_pullback
    {k : Type u} [Field k] {X : Scheme.{u}} (π : X ⟶ Spec (.of k))
    [IsProper π] [GeometricallyIntegral π]
    (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ π = 𝟙 _)
    {T U : Over (Spec (.of k))} (g : U ⟶ T)
    [Flat g.left] [Surjective g.left] [QuasiCompact g.left]
    (L N : (pullback π T.hom).Pic)
    (hL : Scheme.Pic.map (sectionBaseChange π σ hσ T) L = 1)
    (hN : Scheme.Pic.map (sectionBaseChange π σ hσ T) N = 1)
    (h : Scheme.Pic.map (JacobianChallenge.baseChangeMap π g) L =
      Scheme.Pic.map (JacobianChallenge.baseChangeMap π g) N) : L = N := by
  letI : X.Over (Spec (.of k)) := ⟨π⟩
  letI : IsProper (X ↘ Spec (.of k)) := by change IsProper π; infer_instance
  letI : GeometricallyIntegral (X ↘ Spec (.of k)) := by change GeometricallyIntegral π; infer_instance
  let F := picardFunctorNormalized π σ hσ
  let e : F.toFunctor ≅ (picardFunctor π).obj := normalizedPicardIso σ hσ
  have hF : Presheaf.IsSheaf (Scheme.fpqcTopology.over (Spec (.of k))) F.toFunctor :=
    (Presheaf.isSheaf_of_iso_iff e).mpr (isSheaf_fpqc_picardFunctor σ hσ)
  have hF' := (isSheaf_iff_isSheaf_of_type _ F.toFunctor).mp hF
  have hs : Presieve.IsSheafFor F.toFunctor (Presieve.singleton g) := by
    rw [Presieve.isSheafFor_iff_generate]
    exact hF' _ (Scheme.singleton_mem_over_fpqcTopology g)
  let L' : F.toFunctor.obj (.op T) := ⟨L, hL⟩
  let N' : F.toFunctor.obj (.op T) := ⟨N, hN⟩
  have heq : L' = N' := by
    apply hs.isSeparatedFor.ext
    intro V v hv
    cases hv
    apply Subtype.ext
    exact h
  exact congrArg Subtype.val heq

/-- Triviality is detected on a genuine fpqc cover when the family is
normalized. This does not install any global-seesaw or residue-point Fact. -/
theorem normalizedPicard_eq_one_iff_fpqc_pullback
    {k : Type u} [Field k] {X : Scheme.{u}} (π : X ⟶ Spec (.of k))
    [IsProper π] [GeometricallyIntegral π]
    (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ π = 𝟙 _)
    {T U : Over (Spec (.of k))} (g : U ⟶ T)
    [Flat g.left] [Surjective g.left] [QuasiCompact g.left]
    (L : (pullback π T.hom).Pic)
    (hL : Scheme.Pic.map (sectionBaseChange π σ hσ T) L = 1) :
    Scheme.Pic.map (JacobianChallenge.baseChangeMap π g) L = 1 ↔ L = 1 := by
  constructor
  · intro h
    apply normalizedPicard_eq_of_fpqc_pullback π σ hσ g L 1 hL (Scheme.Pic.map_one _)
    simpa only [Scheme.Pic.map_one] using h
  · intro h
    rw [h, Scheme.Pic.map_one]

end ZInQ.Contrib.CloudR2Poincare.L2

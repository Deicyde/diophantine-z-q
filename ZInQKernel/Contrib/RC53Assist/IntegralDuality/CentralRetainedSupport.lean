import ZInQKernel.Contrib.RC53Assist.IntegralDuality.ActualGlobalDuality

/-!
# Bounded retained central models from weak arithmetic support

Global and local dimension two give support zero through three for the
compact central complex. This weaker support is already enough to bound
its retained Smith resolution in degrees minus one through three, and its
shift-three dual in degrees zero through four. No vanishing of zeroth
cohomology or rational-point torsion finiteness is needed for these bounds.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace ZInQ.Contrib.RC53Assist.IntegralDuality

open CategoryTheory NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.RC53Assist.Calibration
open ZInQ.Contrib.RC53Assist.CalibrationIntegral
open ZInQ.Contrib.RC53Assist.CalibrationModel
open ZInQ.Contrib.RC53Assist.CalibrationShape
open ZInQ.Contrib.RC53Assist.InnerLimitArith

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}

/-- Weak arithmetic support keeps degree zero instead of requiring a point-finiteness argument. -/
theorem compactCentral_support_zero_three (D : GenuineKummerData K E₀ hZ)
    (hloc : MilneLocalFiniteness) (hglob : MilneGlobalFiniteness)
    (hlocal : MilneLocalDimensionTwo) (hglobal : MilneGlobalDimensionTwo)
    (hK : IsTotallyComplex K)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ D.S)
    (n : ℤ) (hn : n < 0 ∨ 3 < n) :
    Subsingleton ((compactCentralComplex D).homology n) := by
  rw [compactCentralComplex_eq]
  rcases hn with hn | hn
  · exact compactKummer_homology_negative (centralCurve D) (centralFullTorsion D) n hn
  · exact compactKummer_homology_high (centralCurve D) (centralFullTorsion D)
      hloc hglob hlocal hglobal hK D.hSfin h2 n hn

variable (D : GenuineKummerData K E₀ hZ)
  (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex D).homology n))
  (hout : ∀ n : ℤ, n < 0 ∨ 3 < n → Subsingleton ((compactCentralComplex D).homology n))

include hout

/-- The actual retained resolution is bounded in minus one through three from weak support. -/
theorem centralRetainedGCx_bounded_weak (n : ℤ) (hn : n < -1 ∨ 3 < n) :
    Subsingleton ((centralRetainedGCx D hfinite).X n) := by
  have h₁ := (chosenDiagonalResolution_zero (hfinite n) (hout n (by omega))).1
  have h₂ := (chosenDiagonalResolution_zero (hfinite (n + 1)) (hout (n + 1) (by omega))).2
  change Subsingleton
    ((Fin (chosenPresentations (compactCentralComplex D) hfinite n).generators → ℤ_[2]) ×
      (Fin (chosenPresentations (compactCentralComplex D) hfinite (n + 1)).relations → ℤ_[2]))
  dsimp only [chosenPresentations]
  rw [h₁, h₂]
  infer_instance

/-- The exact shifted dual is bounded in zero through four, with the existing signs unchanged. -/
theorem centralRetainedDual_bounded_weak (n : ℤ) (hn : n < 0 ∨ 4 < n) :
    Subsingleton ((dualCx (centralRetainedGCx D hfinite) 3).X n) := by
  let : Subsingleton ((centralRetainedGCx D hfinite).X (3 - n)) :=
    centralRetainedGCx_bounded_weak D hfinite hout (3 - n) (by omega)
  change Subsingleton (Module.Dual ℤ_[2] ((centralRetainedGCx D hfinite).X (3 - n)))
  infer_instance

/-- The retained complex satisfies the same genuine bounded-finite-free predicate as the global models. -/
theorem centralRetained_boundedFiniteFree_weak : IsBoundedFiniteFree (centralRetainedGCx D hfinite) :=
  ⟨⟨-1, 3, centralRetainedGCx_bounded_weak D hfinite hout⟩,
    centralRetainedGCx_terms D hfinite⟩

/-- The reflected retained dual is likewise a bounded finite free model. -/
theorem centralRetainedDual_boundedFiniteFree_weak :
    IsBoundedFiniteFree (dualCx (centralRetainedGCx D hfinite) 3) := by
  refine ⟨⟨0, 4, centralRetainedDual_bounded_weak D hfinite hout⟩, fun n => ?_⟩
  let : Module.Free ℤ_[2] ((centralRetainedGCx D hfinite).X (3 - n)) :=
    (centralRetainedGCx_terms D hfinite (3 - n)).1
  let : Module.Finite ℤ_[2] ((centralRetainedGCx D hfinite).X (3 - n)) :=
    (centralRetainedGCx_terms D hfinite (3 - n)).2
  change Module.Free ℤ_[2] (Module.Dual ℤ_[2] ((centralRetainedGCx D hfinite).X (3 - n))) ∧
    Module.Finite ℤ_[2] (Module.Dual ℤ_[2] ((centralRetainedGCx D hfinite).X (3 - n)))
  exact ⟨inferInstance, inferInstance⟩

/-- The bounded projective realization of the retained model needs only this weaker support. -/
theorem centralRetainedGCx_computesRHom_weak :
    TermwiseDualComputesRHom ℤ_[2] (centralRetainedGCx D hfinite) := by
  refine Or.inr ⟨-1, 3, centralRetainedGCx_bounded_weak D hfinite hout, fun n => ?_⟩
  let : Module.Free ℤ_[2] ((centralRetainedGCx D hfinite).X n) :=
    (centralRetainedGCx_terms D hfinite n).1
  exact ⟨inferInstance, (centralRetainedGCx_terms D hfinite n).2⟩

end ZInQ.Contrib.RC53Assist.IntegralDuality

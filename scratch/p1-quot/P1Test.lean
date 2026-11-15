import ZInQKernel.HDecomp.QM.Pairs
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveLine.RelativeCoordinates
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveSpace.Invertible
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveSpace.CoordinateCover

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite
open LeafQM.AV
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.ProjectiveLine

namespace P1Quot

abbrev I : Type := ULift.{0} (Fin 2)
abbrev i0 : I := ⟨0⟩
abbrev i1 : I := ⟨1⟩
abbrev SQ : Scheme.{0} := Spec (CommRingCat.of ℚ)
abbrev L : Scheme.{0} := ProjectiveSpace I SQ
abbrev std (i : I) : L.Opens := standardOpen I SQ i

theorem i0_ne_i1 : i0 ≠ i1 := by decide
theorem i1_ne_i0 : i1 ≠ i0 := by decide

theorem appLE_eq_of_eq' {X Y : Scheme.{0}} {f g : X ⟶ Y} (e : f = g) (V : Y.Opens) (U : X.Opens)
    (h : U ≤ f ⁻¹ᵁ V) : f.appLE V U h = g.appLE V U (e ▸ h) := by
  subst e; rfl

/-- Preimages of the standard opens under a normalized point. -/
theorem normalized_preimage_other {W : Scheme.{0}} (s : W ⟶ SQ) {i j : I} (hij : i ≠ j)
    (a : Γ(W, ⊤)) : normalized s i a ⁻¹ᵁ std j = W.basicOpen a := by
  rw [normalized, homOfSections_preimage_standardOpen]
  simp [normalizedSections, hij.symm]

theorem normalized_preimage_self {W : Scheme.{0}} (s : W ⟶ SQ) (i : I) (a : Γ(W, ⊤)) :
    normalized s i a ⁻¹ᵁ std i = ⊤ := by
  rw [normalized, homOfSections_preimage_standardOpen]
  simp [normalizedSections, Scheme.basicOpen_of_isUnit _ isUnit_one]

/-- Pulling back the chart coordinate along a normalized point. -/
theorem normalized_appLE {W : Scheme.{0}} (s : W ⟶ SQ) {i j : I} (hij : i ≠ j) (a : Γ(W, ⊤))
    (h : ⊤ ≤ normalized s i a ⁻¹ᵁ std i) :
    (normalized s i a).appLE (std i) ⊤ h (coordRatio I SQ i j) = a := by
  have := homOfSections_appLE_coordRatio s (normalizedSections i a) (normalizedSections_span i a)
    (coordinate := i) (by simp [normalizedSections]) j h
  refine this.trans ?_
  simp [normalizedSections, hij.symm]

theorem topIso_inv_coordRatio {i j : I} (hij : i ≠ j) :
    (std i).topIso.inv (coordRatio I SQ i j) = relativeChartCoordinate SQ i := by
  have e := relativeChart_ι_eq_normalized SQ i
  have h : ⊤ ≤ (std i).ι ⁻¹ᵁ std i := by
    intro x _; exact x.2
  have h2 := congrArg (fun φ => φ (coordRatio I SQ i j)) (appLE_eq_of_eq' e (std i) ⊤ h)
  have h3 := h2.trans (normalized_appLE _ hij _ _)
  refine Eq.trans ?_ h3
  simp only [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
  rfl

end P1Quot

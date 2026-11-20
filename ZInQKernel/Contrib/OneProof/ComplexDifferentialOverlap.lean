import ZInQKernel.Contrib.OneProof.ComplexPointDerivation

/-! The analytic expressions given by two affine representations of the
same regular differential agree on their overlap. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Filter
open scoped Manifold Topology

namespace AlgebraicGeometry.ComplexPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : Over (Spec (CommRingCat.of ℂ))}
  [SmoothOfRelativeDimension 1 X.hom]

private theorem mfderiv_evaluate_res {U W : X.left.Opens} (h : W ≤ U)
    (a : Γ(X.left, U)) (p : ComplexPoint X) (hp : p.underlying ∈ W) :
    mfderiv 𝓘(ℂ, Fin 1 → ℂ) 𝓘(ℂ, ℂ)
      (Point.evaluate W (X.left.presheaf.map (homOfLE h).op a)) p =
    mfderiv 𝓘(ℂ, Fin 1 → ℂ) 𝓘(ℂ, ℂ) (Point.evaluate U a) p := by
  have hEq : Point.evaluate W (X.left.presheaf.map (homOfLE h).op a) =ᶠ[𝓝 p]
      Point.evaluate U a := by
    filter_upwards [(Point.isOpen_overOpen (X := X) W).mem_nhds hp] with q hq
    exact (Point.evaluate_res h a q hq).symm
  exact ((mdifferentiableAt_evaluate U p (h hp) a).hasMFDerivAt.congr_of_eventuallyEq hEq).mfderiv

omit [SmoothOfRelativeDimension 1 X.hom] in
/-- Restriction preserves the expression of a global differential as a
regular function times an exact differential. -/
theorem restrict_differential_expression (ω : Γ(X.hom.relativeDifferentials, ⊤))
    {U W : X.left.Opens} (h : W ≤ U) (s t : Γ(X.left, U))
    (he : s • X.hom.sectionsD U t =
      X.hom.relativeDifferentials.presheaf.map (homOfLE le_top).op ω) :
    X.left.presheaf.map (homOfLE h).op s •
        X.hom.sectionsD W (X.left.presheaf.map (homOfLE h).op t) =
      X.hom.relativeDifferentials.presheaf.map (homOfLE le_top).op ω := by
  rw [X.hom.sectionsD_map h, ← Scheme.Modules.map_smul, he,
      ← CategoryTheory.comp_apply, ← Functor.map_comp]
  rfl

/-- Two expressions for the same section in algebraic affine charts
determine the same complex cotangent functional at a point of both charts. -/
theorem evaluate_differential_expressions_eq
    (ω : Γ(X.hom.relativeDifferentials, ⊤)) {U V : X.left.Opens}
    (a b : Γ(X.left, U)) (c d : Γ(X.left, V))
    (hU : a • X.hom.sectionsD U b =
      X.hom.relativeDifferentials.presheaf.map (homOfLE le_top).op ω)
    (hV : c • X.hom.sectionsD V d =
      X.hom.relativeDifferentials.presheaf.map (homOfLE le_top).op ω)
    (p : ComplexPoint X) (hpU : p.underlying ∈ U) (hpV : p.underlying ∈ V) :
    Point.evaluate U a p • mfderiv 𝓘(ℂ, Fin 1 → ℂ) 𝓘(ℂ, ℂ) (Point.evaluate U b) p =
      Point.evaluate V c p • mfderiv 𝓘(ℂ, Fin 1 → ℂ) 𝓘(ℂ, ℂ) (Point.evaluate V d) p := by
  obtain ⟨W, hW, hpW, hWV⟩ := exists_isAffineOpen_mem_and_subset
    (U := U ⊓ V) (x := p.underlying) ⟨hpU, hpV⟩
  have hWU := hWV.trans (inf_le_left : U ⊓ V ≤ U)
  have hWV' := hWV.trans (inf_le_right : U ⊓ V ≤ V)
  have h₁ := restrict_differential_expression ω hWU a b hU
  have h₂ := restrict_differential_expression ω hWV' c d hV
  ext v
  have hpair := congrArg (differentialSectionPairing W hW p hpW v) (h₁.trans h₂.symm)
  rw [differentialSectionPairing_smul_sectionsD, differentialSectionPairing_smul_sectionsD,
    ← Point.evaluate_res hWU a p hpW, ← Point.evaluate_res hWV' c p hpW,
    mfderiv_evaluate_res hWU b p hpW, mfderiv_evaluate_res hWV' d p hpW] at hpair
  exact hpair

end AlgebraicGeometry.ComplexPoint

#print axioms AlgebraicGeometry.ComplexPoint.evaluate_differential_expressions_eq

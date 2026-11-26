import ZInQKernel.Contrib.OneProof.RC.ModelInvariants.Compatibility
import ZInQKernel.Contrib.OneProof.RC.ModelInvariants.FinitePoints
import ZInQKernel.Contrib.OneProof.RC.ModelInvariants.GradedPoints

/-! # Geometric lifts through the two commuting quotients -/

namespace RC.ModelInvariants

section Points

variable {R S G k : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Group G] [Fintype G] [MulSemiringAction G S] [SMulCommClass G R S]
  [Field k] [Algebra R k] [IsAlgClosed k]
  (grading : ℤ → Submodule R S) [GradedAlgebra grading] [PreservesGrading (G := G) grading]

/-- The inclusion of the degree-zero invariants into the graded algebra. -/
noncomputable def degreeZeroInvariantsInclusion : degreeZero (fixedGrading grading G) →ₐ[R] S :=
  (FixedPoints.subalgebra R S G).val.comp (degreeZero (fixedGrading grading G)).val

private theorem degreeZeroInvariantsInclusion_factor :
    degreeZeroInvariantsInclusion (G := G) grading =
      ((degreeZero grading).val.comp (FixedPoints.subalgebra R (degreeZero grading) G).val).comp
        (fixedDegreeZeroEquiv (G := G) grading).toAlgHom := rfl

/-- A point of the combined quotient lifts to the graded ring if it has a
homogeneous unit of nonzero degree. -/
theorem degreeZeroInvariants_restrict_surjective {d : ℤ} {δ : Sˣ}
    (hd : d ≠ 0) (hδ : (δ : S) ∈ grading d) :
    Function.Surjective (fun f : S →ₐ[R] k =>
      f.comp (degreeZeroInvariantsInclusion (G := G) grading)) := by
  intro f
  let e := fixedDegreeZeroEquiv (G := G) grading
  obtain ⟨g, hg⟩ := fixedPoints_restrict_surjective (G := G) (S := degreeZero grading)
    (f.comp e.symm.toAlgHom)
  obtain ⟨x, hx⟩ := degreeZero_restrict_surjective grading hd hδ g
  refine ⟨x, AlgHom.ext fun a => ?_⟩
  change x (degreeZeroInvariantsInclusion grading a) = f a
  rw [degreeZeroInvariantsInclusion_factor]
  change x ((degreeZero grading).val (e a).val) = f a
  rw [show x ((degreeZero grading).val (e a).val) = g (e a).val from AlgHom.congr_fun hx _]
  exact (AlgHom.congr_fun hg (e a)).trans (congrArg f (e.symm_apply_apply a))

/-- Two lifts have the same restriction precisely when one can be
translated by a group element and then rescaled on homogeneous elements. -/
theorem degreeZeroInvariants_restrict_eq_iff {d : ℤ} {δ : Sˣ} (hd : d ≠ 0)
    (hδ : (δ : S) ∈ grading d) (hG : IsUnit (Fintype.card G : R)) (f g : S →ₐ[R] k) :
    f.comp (degreeZeroInvariantsInclusion (G := G) grading) =
      g.comp (degreeZeroInvariantsInclusion (G := G) grading) ↔
    ∃ a : G, ∃ u : kˣ, ∀ i x, x ∈ grading i → g x = (↑(u ^ i) : k) * (a • f) x := by
  let e := fixedDegreeZeroEquiv (G := G) grading
  have cancel :
      f.comp (degreeZeroInvariantsInclusion (G := G) grading) =
        g.comp (degreeZeroInvariantsInclusion (G := G) grading) ↔
      (f.comp (degreeZero grading).val).comp (FixedPoints.subalgebra R (degreeZero grading) G).val =
        (g.comp (degreeZero grading).val).comp (FixedPoints.subalgebra R (degreeZero grading) G).val := by
    constructor
    · intro h
      exact AlgHom.ext fun x => AlgHom.congr_fun h (e.symm x)
    · intro h
      exact AlgHom.ext fun x => AlgHom.congr_fun h (e x)
  rw [cancel, fixedPoints_restrict_eq_iff hG]
  constructor <;> rintro ⟨a, h⟩ <;> refine ⟨a, ?_⟩
  · exact (degreeZero_restrict_eq_iff grading hd hδ (a • f) g).1 h
  · exact (degreeZero_restrict_eq_iff grading hd hδ (a • f) g).2 h

end Points

#print axioms degreeZeroInvariantsInclusion
#print axioms degreeZeroInvariantsInclusion_factor
#print axioms degreeZeroInvariants_restrict_surjective
#print axioms degreeZeroInvariants_restrict_eq_iff

end RC.ModelInvariants

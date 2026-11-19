import ZInQKernel.Contrib.RC53Assist.HodgeLatticeIdeal.Fractional

/-!
# The lattice ideal of the actual invariant differential

The reviewed evaluation of the transported Weierstrass invariant differential gives a nonzero
vector in the model's Hodge line. For that actual vector, the unchanged determinant lattice
has unique coefficients, those coefficients form a nonzero fractional ideal, and the original
section index is the coefficient index. The original integral cotangent lattice is carried
isomorphically to the coefficient ideal by its natural first wedge.

Locators: `HodgeLineBinding.hodgeEval_invariantDifferential`; `Fractional.lean`.
No minimal model, global integral basis, discriminant, metric, or period is asserted.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.HodgeLatticeIdeal

open NumberField AlgebraicGeometry CategoryTheory
open ZInQ.DefFaltings
open ZInQ.Contrib.RC53Assist.HodgeLineBinding
open ZInQ.Contrib.RC53Assist.S2aNumberField
open ZInQ.Contrib.RC53Assist.AbelianCurve (functionFieldAlgebra abelian_scheme_integral)

variable {K : Type} [Field K] {E : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L]

/-- THEOREM. The exact integral-lattice dictionary for the ACTUAL evaluated invariant
 differential, including reconstruction, nonzero fractional-ideal coefficients, the original
 `omega` isomorphism, and the original section-index orientation and norm formula.
 Locator: `hodgeEval_invariantDifferential`, `detLattice_eq_coefficient_map`,
 `coefficientFractionalIdeal`, `omegaCoefficientEquiv`, `secIndex_detLattice_mul_absNorm`. -/
theorem invariantDifferential_ideal_dictionary (G : GroupModel E L) (hdim : E.dim = 1)
    (E' : WeierstrassCurve L) [E'.IsElliptic]
    (e : letI := abelian_scheme_integral (E.baseChange L).X
      letI := functionFieldAlgebra (E.baseChange L).X.hom
      E'.toAffine.FunctionField ≃ₐ[L] (E.baseChange L).X.left.functionField)
    (i : (E.baseChange L).X.left ≅ Proj E'.toProjective.grading)
    (hfield : letI := abelian_scheme_integral (E.baseChange L).X
      i.hom.functionFieldMap.hom = e.toRingHom.comp (projFunctionFieldEquiv E').toRingHom)
    (hO : i.hom (identityPoint (E.baseChange L).X) = pointO E') :
    letI := abelian_scheme_integral (E.baseChange L).X
    letI := functionFieldAlgebra (E.baseChange L).X.hom
    ∃ hreg : kaehlerTransport e (WeierstrassCurve.Affine.invariantDifferential E'.toAffine) ∈
        regularAtOrigin (E.baseChange L),
      let η := hodgeEval G hdim ⟨_, hreg⟩
      let I := coefficientSubmodule (G.detLattice 1) η
      η = G.wedge ![originParameter G E' i hO] ∧ η ≠ 0 ∧
      G.detLattice 1 = I.map (coordinateMap (L := L) η) ∧
      Function.Injective (coordinateMap (L := L) η) ∧
      (∀ v ∈ G.detLattice 1, ∃! a : L, a ∈ I ∧ a • η = v) ∧
      I ≠ ⊥ ∧ I.FG ∧ Submodule.span L (I : Set L) = ⊤ ∧
      ∃ J : FractionalIdeal (nonZeroDivisors (𝓞 L)) L,
        (J : Submodule (𝓞 L) L) = I ∧ J ≠ 0 ∧
        ∃ c : G.omega ≃ₗ[𝓞 L] I,
          (∀ x : G.omega, (c x : L) • η = oneHodgeMap G x) ∧
          (∀ a : L, secIndex (G.detLattice 1) (a • η) =
            (Submodule.span (𝓞 L) {a}).toAddSubgroup.relIndex I.toAddSubgroup) ∧
          (∀ a : L, a ∈ I → a ≠ 0 →
            (secIndex (G.detLattice 1) (a • η) : ℚ) * FractionalIdeal.absNorm J =
              |Algebra.norm ℚ a| ∧
            (secIndex (G.detLattice 1) (a • η) : ℚ) =
              |Algebra.norm ℚ a| / FractionalIdeal.absNorm J ∧
            secIndex (G.detLattice 1) (a • η) ≠ 0) := by
  haveI := abelian_scheme_integral (E.baseChange L).X
  letI := functionFieldAlgebra (E.baseChange L).X.hom
  obtain ⟨hreg, heval, hwedge⟩ :=
    hodgeEval_invariantDifferential G hdim E' e i hfield hO
  let η := hodgeEval G hdim ⟨_, hreg⟩
  have hη : η ≠ 0 := by
    rw [show η = G.wedge ![originParameter G E' i hO] from heval]
    exact hwedge
  refine ⟨hreg, heval, hη, detLattice_eq_coefficient_map G hdim η hη,
    coordinateMap_injective (L := L) η hη,
    fun v hv => existsUnique_detLattice_coefficient G hdim η hη v hv,
    coefficientSubmodule_detLattice_ne_bot G hdim η hη,
    coefficientSubmodule_detLattice_fg G hdim η hη,
    coefficientSubmodule_detLattice_spans G hdim η hη,
    coefficientFractionalIdeal G hdim η hη, rfl,
    coefficientFractionalIdeal_ne_zero G hdim η hη,
    omegaCoefficientEquiv G hdim η hη, omegaCoefficientEquiv_spec G hdim η hη,
    secIndex_detLattice_relIndex G hdim η hη, ?_⟩
  intro a ha ha0
  exact ⟨secIndex_detLattice_mul_absNorm G hdim η hη ha ha0,
    secIndex_detLattice_eq_norm_div G hdim η hη ha ha0,
    secIndex_detLattice_ne_zero G hdim η hη ha ha0⟩

end ZInQ.Contrib.RC53Assist.HodgeLatticeIdeal

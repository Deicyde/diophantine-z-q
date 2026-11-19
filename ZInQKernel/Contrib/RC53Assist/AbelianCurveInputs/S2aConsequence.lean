import ZInQKernel.Contrib.RC53Assist.AbelianCurveInputs.LocalFacts
import ZInQKernel.Contrib.RC53Assist.AbelianCurve.ObjectBridge

/-!
# Pointed S2a with the regular-differential input discharged

The regular-differential comparison is proved in `LocalFacts.lean`. The existing
pointed projective-model conclusions therefore take only the original invariant
sheaf trivialization input. This file does not prove that remaining input, and
makes no claim of parameter independence for the normalized Kähler–Weil map.

Locators: Milne, *Abelian varieties*, version 2.00, IV, Proposition 6.4(a)–(b),
p. 152; Silverman, *The Arithmetic of Elliptic Curves*, Proposition III.3.1;
`AbelianCurve/ProjectiveComparison.lean` and `AbelianCurve/ObjectBridge.lean`.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.AbelianCurveInputs.S2aConsequence

open AlgebraicGeometry CategoryTheory
open ZInQ.Contrib.RC53Assist.AbelianCurve
open ZInQ.Contrib.RC53Assist.IsogenyScheme

/-- THEOREM. The actual proper smooth geometrically integral group curve has an
elliptic function field using only the original invariant sheaf input.
Locator: `AbelianCurve.abelian_isEllipticFunctionField`;
`LocalFacts.regularDifferentialComparison`. -/
theorem abelian_isEllipticFunctionField_of_trivialization
    (hT : InvariantDifferentialTrivialization)
    (G : Over (Spec (.of ℚ))) [CategoryTheory.GrpObj G] [IsIntegral G.left]
    [Smooth G.hom] [IsProper G.hom] [GeometricallyIntegral G.hom]
    (hdim : topologicalKrullDim G.left = 1) :
    letI := functionFieldAlgebra G.hom
    TauCeti.IsEllipticFunctionField ℚ G.left.functionField :=
  abelian_isEllipticFunctionField hT LocalFacts.regularDifferentialComparison G hdim

/-- THEOREM. The pointed scheme-level S2a conclusion has just one remaining
original input. The map is over the rationals, its function-field pullback is
specified, and it sends the actual identity to infinity.
Locator: `AbelianCurve.abelian_projectiveWeierstrassModel`;
`LocalFacts.regularDifferentialComparison`. -/
theorem abelian_projectiveWeierstrassModel_of_trivialization
    (hT : InvariantDifferentialTrivialization)
    (G : Over (Spec (.of ℚ))) [CategoryTheory.GrpObj G] [IsIntegral G.left]
    [Smooth G.hom] [IsProper G.hom] [GeometricallyIntegral G.hom]
    (hdim : topologicalKrullDim G.left = 1) :
    letI := functionFieldAlgebra G.hom
    ∃ E : WeierstrassCurve ℚ, E.IsElliptic ∧
      ∃ (e : E.toAffine.FunctionField ≃ₐ[ℚ] G.left.functionField)
        (i : G.left ≅ Proj E.toProjective.grading),
        i.hom ≫ projectiveStructure E = G.hom ∧
        i.hom.functionFieldMap.hom =
          e.toRingHom.comp (projFunctionFieldEquiv E).toRingHom ∧
        i.hom (identityPoint G) = pointO E :=
  abelian_projectiveWeierstrassModel hT LocalFacts.regularDifferentialComparison G hdim

/-- THEOREM. The project's `PkgI3.AbVar` has the pointed projective-model
conclusion with only the invariant sheaf trivialization still assumed.
Locator: `AbelianCurve.abVar_projectiveWeierstrassModel`;
`ZInQKernel/HDecomp/Objects.lean`, `PkgI3.AbVar`. -/
theorem abVar_projectiveWeierstrassModel_of_trivialization
    (hT : InvariantDifferentialTrivialization)
    (A : PkgI3.AbVar ℚ) (hdim : A.dim = 1) :
    letI := abelian_scheme_integral A.X
    letI := functionFieldAlgebra A.X.hom
    ∃ E : WeierstrassCurve ℚ, E.IsElliptic ∧
      ∃ (e : E.toAffine.FunctionField ≃ₐ[ℚ] A.X.left.functionField)
        (i : A.X.left ≅ Proj E.toProjective.grading),
        i.hom ≫ projectiveStructure E = A.X.hom ∧
        i.hom.functionFieldMap.hom =
          e.toRingHom.comp (projFunctionFieldEquiv E).toRingHom ∧
        i.hom (identityPoint A.X) = pointO E :=
  abVar_projectiveWeierstrassModel hT LocalFacts.regularDifferentialComparison A hdim

/-- THEOREM. The project's `PkgI2.IsAbelianVariety` presentation has the same
pointed projective-model conclusion with one remaining original input.
Locator: `AbelianCurve.groupAbVar_projectiveWeierstrassModel`;
`ZInQKernel/HDecomp/Objects.lean`, `PkgI2.IsAbelianVariety`. -/
theorem groupAbVar_projectiveWeierstrassModel_of_trivialization
    (hT : InvariantDifferentialTrivialization)
    (A : Grp (Over (Spec (.of ℚ)))) [PkgI2.IsAbelianVariety A]
    (hdim : topologicalKrullDim A.X.left = 1) :
    letI := (inferInstance : PkgI2.IsAbelianVariety A).geomIntegral
    letI := abelian_scheme_integral A.X
    letI := functionFieldAlgebra A.X.hom
    ∃ E : WeierstrassCurve ℚ, E.IsElliptic ∧
      ∃ (e : E.toAffine.FunctionField ≃ₐ[ℚ] A.X.left.functionField)
        (i : A.X.left ≅ Proj E.toProjective.grading),
        i.hom ≫ projectiveStructure E = A.X.hom ∧
        i.hom.functionFieldMap.hom =
          e.toRingHom.comp (projFunctionFieldEquiv E).toRingHom ∧
        i.hom (identityPoint A.X) = pointO E :=
  groupAbVar_projectiveWeierstrassModel hT LocalFacts.regularDifferentialComparison A hdim

end ZInQ.Contrib.RC53Assist.AbelianCurveInputs.S2aConsequence

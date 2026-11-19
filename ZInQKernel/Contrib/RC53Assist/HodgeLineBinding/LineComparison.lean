import ZInQKernel.Contrib.RC53Assist.HodgeLineBinding.HodgeLine

/-!
# The comparison of the regular Kähler line with the Hodge line

Given Weierstrass data `(E', e, i)` for `E_L` of the shape produced by the number-field S2a theorem
(with the function-field equation `hfield` and the point equation `i(o) = O`), the composite

`regular Kähler line of E'  --Kähler transport along e-->  differentials of L(X) regular at o
  --value at o-->  𝔪_o/𝔪_o²  --stalk maps-->  𝒢.cotangent  --1 ⊗ ι-->  hodgeSpace 1`

is an `L`-linear isomorphism (`lineComparisonEquiv`) sending the invariant differential `ω` to the
wedge `𝒢.wedge ![f]` of the local parameter `f` of `-x/y` (`lineComparisonEquiv_invariant`). It
is built only from actual maps (Kähler functoriality, restriction to the local ring at the
origin, evaluation of differentials at the origin, stalk maps); no basis of either line is
chosen.

Locator: Silverman, *The Arithmetic of Elliptic Curves*, second edition, III.1.5 and IV.1.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.HodgeLineBinding

open AlgebraicGeometry CategoryTheory NumberField KaehlerDifferential
open ZInQ.DefFaltings
open ZInQ.Contrib.RC53Assist.S2aNumberField
open ZInQ.Contrib.RC53Assist.AbelianCurve (functionFieldAlgebra abelian_scheme_integral)
open ZInQ.Contrib.RC53Assist.AbelianCurveInputs.ComplexDifferentialLine
  (regularKaehlerSubmodule regularKaehler_eq_span)

variable {K : Type} [Field K] {E : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L]

/-- THEOREM (proved). The Kähler transport along `e` carries the regular Kähler line of `E'` into
the differentials regular at the origin. Locator: `hodgeEval_regularKaehler`. -/
theorem kaehlerTransport_regularKaehler_mem (G : GroupModel E L) (hdim : E.dim = 1)
    (E' : WeierstrassCurve L) [E'.IsElliptic]
    (e : letI := abelian_scheme_integral (E.baseChange L).X
      letI := functionFieldAlgebra (E.baseChange L).X.hom
      E'.toAffine.FunctionField ≃ₐ[L] (E.baseChange L).X.left.functionField)
    (i : (E.baseChange L).X.left ≅ Proj E'.toProjective.grading)
    (hfield : letI := abelian_scheme_integral (E.baseChange L).X
      i.hom.functionFieldMap.hom = e.toRingHom.comp (projFunctionFieldEquiv E').toRingHom)
    (hO : i.hom (identityPoint (E.baseChange L).X) = pointO E')
    (η : Ω[E'.toAffine.FunctionField⁄L]) (hη : η ∈ regularKaehlerSubmodule E'.toAffine) :
    letI := abelian_scheme_integral (E.baseChange L).X
    letI := functionFieldAlgebra (E.baseChange L).X.hom
    kaehlerTransport e η ∈ regularAtOrigin (E.baseChange L) := by
  obtain ⟨c, hreg, -, -⟩ := hodgeEval_regularKaehler G hdim E' e i hfield hO η hη
  exact hreg

/-- DEFINITION. The comparison of the regular Kähler line of `E'` with the Hodge line of `𝒢`:
Kähler transport along `e` followed by the evaluation in the Hodge line. Locator:
`hodgeEvalLinear`, `kaehlerTransport_regularKaehler_mem`. -/
def lineComparison (G : GroupModel E L) (hdim : E.dim = 1)
    (E' : WeierstrassCurve L) [E'.IsElliptic]
    (e : letI := abelian_scheme_integral (E.baseChange L).X
      letI := functionFieldAlgebra (E.baseChange L).X.hom
      E'.toAffine.FunctionField ≃ₐ[L] (E.baseChange L).X.left.functionField)
    (i : (E.baseChange L).X.left ≅ Proj E'.toProjective.grading)
    (hfield : letI := abelian_scheme_integral (E.baseChange L).X
      i.hom.functionFieldMap.hom = e.toRingHom.comp (projFunctionFieldEquiv E').toRingHom)
    (hO : i.hom (identityPoint (E.baseChange L).X) = pointO E') :
    regularKaehlerSubmodule E'.toAffine →ₗ[L] G.hodgeSpace 1 :=
  haveI := abelian_scheme_integral (E.baseChange L).X
  letI := functionFieldAlgebra (E.baseChange L).X.hom
  (hodgeEvalLinear G hdim).comp ((kaehlerTransport e).restrict
    (kaehlerTransport_regularKaehler_mem G hdim E' e i hfield hO))

/-- THEOREM (proved). The invariant differential lies on the regular Kähler line. Locator:
`regularKaehler_eq_span`. -/
theorem invariantDifferential_mem_regularKaehler (E' : WeierstrassCurve L) [E'.IsElliptic] :
    WeierstrassCurve.Affine.invariantDifferential E'.toAffine ∈
      regularKaehlerSubmodule E'.toAffine := by
  rw [regularKaehler_eq_span]
  exact Submodule.mem_span_singleton_self _

/-- THEOREM (proved). The comparison sends `ω` to the wedge of the local parameter `-x/y`.
Locator: `hodgeEval_invariantDifferential`. -/
theorem lineComparison_invariant (G : GroupModel E L) (hdim : E.dim = 1)
    (E' : WeierstrassCurve L) [E'.IsElliptic]
    (e : letI := abelian_scheme_integral (E.baseChange L).X
      letI := functionFieldAlgebra (E.baseChange L).X.hom
      E'.toAffine.FunctionField ≃ₐ[L] (E.baseChange L).X.left.functionField)
    (i : (E.baseChange L).X.left ≅ Proj E'.toProjective.grading)
    (hfield : letI := abelian_scheme_integral (E.baseChange L).X
      i.hom.functionFieldMap.hom = e.toRingHom.comp (projFunctionFieldEquiv E').toRingHom)
    (hO : i.hom (identityPoint (E.baseChange L).X) = pointO E') :
    lineComparison G hdim E' e i hfield hO
        ⟨_, invariantDifferential_mem_regularKaehler E'⟩ =
      G.wedge ![originParameter G E' i hO] := by
  haveI := abelian_scheme_integral (E.baseChange L).X
  letI := functionFieldAlgebra (E.baseChange L).X.hom
  obtain ⟨hreg, heval, -⟩ := hodgeEval_invariantDifferential G hdim E' e i hfield hO
  exact heval

/-- THEOREM (proved). The comparison is bijective. Locator: `eq_zero_of_hodgeEval_eq_zero`,
`hodgeEval_regularKaehler_surjective`. -/
theorem lineComparison_bijective (G : GroupModel E L) (hdim : E.dim = 1)
    (E' : WeierstrassCurve L) [E'.IsElliptic]
    (e : letI := abelian_scheme_integral (E.baseChange L).X
      letI := functionFieldAlgebra (E.baseChange L).X.hom
      E'.toAffine.FunctionField ≃ₐ[L] (E.baseChange L).X.left.functionField)
    (i : (E.baseChange L).X.left ≅ Proj E'.toProjective.grading)
    (hfield : letI := abelian_scheme_integral (E.baseChange L).X
      i.hom.functionFieldMap.hom = e.toRingHom.comp (projFunctionFieldEquiv E').toRingHom)
    (hO : i.hom (identityPoint (E.baseChange L).X) = pointO E') :
    Function.Bijective (lineComparison G hdim E' e i hfield hO) := by
  haveI := abelian_scheme_integral (E.baseChange L).X
  letI := functionFieldAlgebra (E.baseChange L).X.hom
  refine ⟨(injective_iff_map_eq_zero _).mpr fun η h0 => Subtype.ext
    (eq_zero_of_hodgeEval_eq_zero G hdim E' e i hfield hO η.1 η.2
      (kaehlerTransport_regularKaehler_mem G hdim E' e i hfield hO η.1 η.2) h0), fun w => ?_⟩
  obtain ⟨η, hη, hreg, heval⟩ := hodgeEval_regularKaehler_surjective G hdim E' e i hfield hO w
  exact ⟨⟨η, hη⟩, heval⟩

/-- DEFINITION. **The comparison of lines** as an `L`-linear isomorphism
`regular Kähler line of E' ≃ hodgeSpace 1`. Locator: `lineComparison_bijective`. -/
def lineComparisonEquiv (G : GroupModel E L) (hdim : E.dim = 1)
    (E' : WeierstrassCurve L) [E'.IsElliptic]
    (e : letI := abelian_scheme_integral (E.baseChange L).X
      letI := functionFieldAlgebra (E.baseChange L).X.hom
      E'.toAffine.FunctionField ≃ₐ[L] (E.baseChange L).X.left.functionField)
    (i : (E.baseChange L).X.left ≅ Proj E'.toProjective.grading)
    (hfield : letI := abelian_scheme_integral (E.baseChange L).X
      i.hom.functionFieldMap.hom = e.toRingHom.comp (projFunctionFieldEquiv E').toRingHom)
    (hO : i.hom (identityPoint (E.baseChange L).X) = pointO E') :
    regularKaehlerSubmodule E'.toAffine ≃ₗ[L] G.hodgeSpace 1 :=
  LinearEquiv.ofBijective _ (lineComparison_bijective G hdim E' e i hfield hO)

/-- THEOREM (proved). **Explicit formula**: the comparison isomorphism sends `ω` to the nonzero
wedge `𝒢.wedge ![f]` of the local parameter of `-x/y`, and `c • ω` to `c • 𝒢.wedge ![f]`.
Locator: `lineComparison_invariant`, `wedge_originParameter_ne_zero`. -/
theorem lineComparisonEquiv_invariant (G : GroupModel E L) (hdim : E.dim = 1)
    (E' : WeierstrassCurve L) [E'.IsElliptic]
    (e : letI := abelian_scheme_integral (E.baseChange L).X
      letI := functionFieldAlgebra (E.baseChange L).X.hom
      E'.toAffine.FunctionField ≃ₐ[L] (E.baseChange L).X.left.functionField)
    (i : (E.baseChange L).X.left ≅ Proj E'.toProjective.grading)
    (hfield : letI := abelian_scheme_integral (E.baseChange L).X
      i.hom.functionFieldMap.hom = e.toRingHom.comp (projFunctionFieldEquiv E').toRingHom)
    (hO : i.hom (identityPoint (E.baseChange L).X) = pointO E') (c : L) :
    lineComparisonEquiv G hdim E' e i hfield hO
        (c • ⟨_, invariantDifferential_mem_regularKaehler E'⟩) =
      c • G.wedge ![originParameter G E' i hO] ∧
      G.wedge ![originParameter G E' i hO] ≠ 0 := by
  refine ⟨?_, wedge_originParameter_ne_zero G E' i hO⟩
  rw [map_smul]
  exact congrArg (c • ·) (lineComparison_invariant G hdim E' e i hfield hO)

/-- THEOREM (proved). **Every local parameter.** For every local parameter `t` at the identity of
the generic fibre (`t ∈ 𝔪_ξ`, `t ∉ 𝔪_ξ²`), `𝒢.wedge ![t] = c • image(ω)` for a nonzero constant
`c ∈ L`. Locator: `exists_smul_wedge_eq`, `wedge_single_ne_zero`,
`hodgeEval_invariantDifferential`. -/
theorem wedge_eq_smul_hodgeEval (G : GroupModel E L) (hdim : E.dim = 1)
    (E' : WeierstrassCurve L) [E'.IsElliptic]
    (e : letI := abelian_scheme_integral (E.baseChange L).X
      letI := functionFieldAlgebra (E.baseChange L).X.hom
      E'.toAffine.FunctionField ≃ₐ[L] (E.baseChange L).X.left.functionField)
    (i : (E.baseChange L).X.left ≅ Proj E'.toProjective.grading)
    (hfield : letI := abelian_scheme_integral (E.baseChange L).X
      i.hom.functionFieldMap.hom = e.toRingHom.comp (projFunctionFieldEquiv E').toRingHom)
    (hO : i.hom (identityPoint (E.baseChange L).X) = pointO E')
    (t : IsLocalRing.maximalIdeal G.genStalk)
    (ht : (t : G.genStalk) ∉ IsLocalRing.maximalIdeal G.genStalk ^ 2) :
    letI := abelian_scheme_integral (E.baseChange L).X
    letI := functionFieldAlgebra (E.baseChange L).X.hom
    ∃ hreg : kaehlerTransport e (WeierstrassCurve.Affine.invariantDifferential E'.toAffine) ∈
        regularAtOrigin (E.baseChange L),
      ∃ c : L, c ≠ 0 ∧ G.wedge ![t] = c • hodgeEval G hdim ⟨_, hreg⟩ := by
  haveI := abelian_scheme_integral (E.baseChange L).X
  letI := functionFieldAlgebra (E.baseChange L).X.hom
  obtain ⟨hreg, heval, -⟩ := hodgeEval_invariantDifferential G hdim E' e i hfield hO
  obtain ⟨c, hc⟩ := exists_smul_wedge_eq G E' i hO (G.wedge ![t])
  refine ⟨hreg, c, ?_, ?_⟩
  · rintro rfl
    rw [zero_smul] at hc
    exact wedge_single_ne_zero G t ht hc.symm
  · rw [heval, hc]

end ZInQ.Contrib.RC53Assist.HodgeLineBinding

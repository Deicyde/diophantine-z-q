import ZInQKernel.Contrib.RC53Assist.HodgeLineBinding.Linearity

/-!
# The Hodge line is spanned by the wedge of the local parameter

For a one-dimensional `E` the local ring `𝒪_{𝒢,ξ}` is isomorphic, through the actual stalk maps
(`originStalkEquiv` and the stalk map of `i` at the origin), to the local ring of the projective
Weierstrass model at `O`, a discrete valuation ring. Hence the cotangent space `𝔪_ξ/𝔪_ξ²` is one
dimensional over the residue field (`finrank_cotangentSpace_genStalk`), the Hodge space
`hodgeSpace 1 = L ⊗_{𝓞_L} ⋀¹(𝔪_ξ/𝔪_ξ²)` is an `L`-line (`finrank_hodgeSpace_one`, through
`rank_tensor_cotangent` of `HDecomp/Faltings/HodgeLattice.lean`), and the nonzero wedge
`𝒢.wedge ![f]` of the local parameter `f` of `-x/y` spans it (`exists_smul_wedge_eq`).

Together with `hodgeEval_regularKaehler` and `eq_zero_of_hodgeEval_eq_zero`, the evaluation in
the Hodge line maps the regular Kähler line of `E'` bijectively onto `hodgeSpace 1`, with
`c • ω ↦ c • 𝒢.wedge ![f]` (`hodgeEval_regularKaehler_surjective`).

Locator: Mathlib, `IsLocalRing.finrank_CotangentSpace_eq_one`, `finrank_eq_one_iff_of_nonzero'`;
Silverman, *The Arithmetic of Elliptic Curves*, second edition, II.1 and IV.1.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.HodgeLineBinding

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing KaehlerDifferential TensorProduct
open ZInQ.DefFaltings ZInQ.DefFaltings.HodgeLattice
open ZInQ.Contrib.RC53Assist.S2aNumberField
open ZInQ.Contrib.RC53Assist.AbelianCurve (functionFieldAlgebra stalkAlgebra
  abelian_scheme_integral)

variable {K : Type} [Field K] {E : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L]

/-- DEFINITION. The ring isomorphism `𝒪_{𝒢,ξ} ≅ 𝒪_{Proj, O}`: `originStalkEquiv` followed by the
inverse of the stalk map of `i` at the origin. Locator: `originStalkEquiv`, `stalkMapAt`. -/
def modelStalkEquivPointO (G : GroupModel E L) (E' : WeierstrassCurve L)
    (i : (E.baseChange L).X.left ≅ Proj E'.toProjective.grading)
    (hO : i.hom (identityPoint (E.baseChange L).X) = pointO E') :
    G.genStalk ≃+* (Proj E'.toProjective.grading).presheaf.stalk (pointO E') :=
  haveI : IsIso (i.hom.stalkMap (identityPoint (E.baseChange L).X)) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp inferInstance).2 _
  haveI : IsIso (stalkMapAt i.hom hO) := by
    unfold stalkMapAt
    infer_instance
  (originStalkEquiv G).trans (asIso (stalkMapAt i.hom hO)).commRingCatIsoToRingEquiv.symm

/-- THEOREM (proved). The cotangent space of `𝒪_{𝒢,ξ}` has dimension one over its residue field.
Locator: `isDiscreteValuationRing_stalk_pointO`, `IsLocalRing.finrank_CotangentSpace_eq_one`;
Mathlib, `spanFinrank_maximalIdeal_eq_finrank_cotangentSpace`,
`Ideal.spanFinrank_map_eq_of_ringEquiv`. -/
theorem finrank_cotangentSpace_genStalk (G : GroupModel E L) (E' : WeierstrassCurve L)
    (i : (E.baseChange L).X.left ≅ Proj E'.toProjective.grading)
    (hO : i.hom (identityPoint (E.baseChange L).X) = pointO E') :
    Module.finrank (ResidueField G.genStalk) (CotangentSpace G.genStalk) = 1 := by
  haveI : IsLocallyNoetherian G.G.left := LocallyOfFiniteType.isLocallyNoetherian G.G.hom
  haveI := isDiscreteValuationRing_stalk_pointO E'
  have h1 := IsLocalRing.finrank_CotangentSpace_eq_one
    ((Proj E'.toProjective.grading).presheaf.stalk (pointO E'))
  rw [← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace] at h1 ⊢
  rw [← map_ringEquiv_maximalIdeal (modelStalkEquivPointO G E' i hO),
    Ideal.spanFinrank_map_eq_of_ringEquiv] at h1
  exact h1

/-- THEOREM (proved). The Hodge space `hodgeSpace 1` is an `L`-line. Locator:
`rank_tensor_cotangent`, `finrank_cotangentSpace_genStalk`; Mathlib, `LinearEquiv.baseChange`,
`exteriorPower.oneEquiv`. -/
theorem finrank_hodgeSpace_one (G : GroupModel E L) (E' : WeierstrassCurve L)
    (i : (E.baseChange L).X.left ≅ Proj E'.toProjective.grading)
    (hO : i.hom (identityPoint (E.baseChange L).X) = pointO E') :
    Module.finrank L (G.hodgeSpace 1) = 1 := by
  haveI : IsLocallyNoetherian G.G.left := LocallyOfFiniteType.isLocallyNoetherian G.G.hom
  have h1 := finrank_cotangentSpace_genStalk G E' i hO
  have h2 := rank_tensor_cotangent G
  have h3 := ((exteriorPower.oneEquiv (𝓞 L) G.cotangent).baseChange (𝓞 L) L _ _).rank_eq
  apply Module.finrank_eq_of_rank_eq
  rw [h3, h2, ← Module.finrank_eq_rank, h1]

/-- THEOREM (proved). **The wedge of the local parameter spans the Hodge line**: every vector of
`hodgeSpace 1` is `c • 𝒢.wedge ![f]`. Locator: `finrank_hodgeSpace_one`,
`wedge_originParameter_ne_zero`; Mathlib, `finrank_eq_one_iff_of_nonzero'`. -/
theorem exists_smul_wedge_eq (G : GroupModel E L) (E' : WeierstrassCurve L)
    (i : (E.baseChange L).X.left ≅ Proj E'.toProjective.grading)
    (hO : i.hom (identityPoint (E.baseChange L).X) = pointO E') (w : G.hodgeSpace 1) :
    ∃ c : L, c • G.wedge ![originParameter G E' i hO] = w :=
  (finrank_eq_one_iff_of_nonzero' _ (wedge_originParameter_ne_zero G E' i hO)).mp
    (finrank_hodgeSpace_one G E' i hO) w

/-- THEOREM (proved). **The comparison is onto the Hodge line**: every vector of `hodgeSpace 1` is
the evaluation of the transport of a differential `c • ω` of the regular Kähler line. Locator:
`exists_smul_wedge_eq`, `hodgeEval_invariantDifferential`, `hodgeEval_smul`;
`ComplexDifferentialLine.regularKaehler_eq_span`. -/
theorem hodgeEval_regularKaehler_surjective (G : GroupModel E L) (hdim : E.dim = 1)
    (E' : WeierstrassCurve L) [E'.IsElliptic]
    (e : letI := abelian_scheme_integral (E.baseChange L).X
      letI := functionFieldAlgebra (E.baseChange L).X.hom
      E'.toAffine.FunctionField ≃ₐ[L] (E.baseChange L).X.left.functionField)
    (i : (E.baseChange L).X.left ≅ Proj E'.toProjective.grading)
    (hfield : letI := abelian_scheme_integral (E.baseChange L).X
      i.hom.functionFieldMap.hom = e.toRingHom.comp (projFunctionFieldEquiv E').toRingHom)
    (hO : i.hom (identityPoint (E.baseChange L).X) = pointO E') (w : G.hodgeSpace 1) :
    letI := abelian_scheme_integral (E.baseChange L).X
    letI := functionFieldAlgebra (E.baseChange L).X.hom
    ∃ η ∈ AbelianCurveInputs.ComplexDifferentialLine.regularKaehlerSubmodule E'.toAffine,
      ∃ hreg : kaehlerTransport e η ∈ regularAtOrigin (E.baseChange L),
        hodgeEval G hdim ⟨_, hreg⟩ = w := by
  haveI := abelian_scheme_integral (E.baseChange L).X
  letI := functionFieldAlgebra (E.baseChange L).X.hom
  obtain ⟨c, rfl⟩ := exists_smul_wedge_eq G E' i hO w
  obtain ⟨hreg, heval, -⟩ := hodgeEval_invariantDifferential G hdim E' e i hfield hO
  have hmemη : c • WeierstrassCurve.Affine.invariantDifferential E'.toAffine ∈
      AbelianCurveInputs.ComplexDifferentialLine.regularKaehlerSubmodule E'.toAffine := by
    rw [AbelianCurveInputs.ComplexDifferentialLine.regularKaehler_eq_span]
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)
  have hT : kaehlerTransport e (c • WeierstrassCurve.Affine.invariantDifferential E'.toAffine) =
      c • kaehlerTransport e (WeierstrassCurve.Affine.invariantDifferential E'.toAffine) :=
    map_smul _ _ _
  have hmem : kaehlerTransport e (c • WeierstrassCurve.Affine.invariantDifferential E'.toAffine)
      ∈ regularAtOrigin (E.baseChange L) := by
    rw [hT]
    exact Submodule.smul_mem _ c hreg
  refine ⟨_, hmemη, hmem, ?_⟩
  have hsub : (⟨_, hmem⟩ : regularAtOrigin (E.baseChange L)) = c • ⟨_, hreg⟩ := Subtype.ext hT
  rw [hsub, hodgeEval_smul, heval]

/-- THEOREM (proved). For a one-dimensional abelian variety `E`, the Hodge space `hodgeSpace 1` of
every smooth group model over `𝓞_L` is an `L`-line. Locator: `finrank_hodgeSpace_one`,
`abVar_projectiveWeierstrassModel_numberField`. -/
theorem finrank_hodgeSpace_one_of_dim_one (G : GroupModel E L) (hdim : E.dim = 1) :
    Module.finrank L (G.hodgeSpace 1) = 1 := by
  haveI := abelian_scheme_integral (E.baseChange L).X
  letI := functionFieldAlgebra (E.baseChange L).X.hom
  obtain ⟨E', -, -, i, -, -, hO⟩ :=
    abVar_projectiveWeierstrassModel_numberField L (E.baseChange L) (baseChange_dim_eq_one hdim)
  exact finrank_hodgeSpace_one G E' i hO

end ZInQ.Contrib.RC53Assist.HodgeLineBinding

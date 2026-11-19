import ZInQKernel.Contrib.RC53Assist.HodgeLineBinding.WeierstrassParameter
import ZInQKernel.Contrib.RC53Assist.HodgeLineBinding.CurveOrigin
import ZInQKernel.Contrib.RC53Assist.HodgeLineBinding.ModelOrigin
import ZInQKernel.Contrib.RC53Assist.HodgeLineBinding.ProjectiveParameter
import ZInQKernel.Contrib.RC53Assist.S2aNumberField.S2a
import ZInQKernel.Contrib.AbVarBC.Dim

/-!
# The invariant differential evaluated in the Hodge line of a group model

Let `K, L` be fields with `L` a number field and `[Algebra K L]`, `E` a one-dimensional abelian
variety over `K`, `B = E_L`, `X` the scheme of `B` and `o` its identity point, and `𝒢` a smooth
group model of `E` over `𝓞_L`. Let `(E', e, i)` be Weierstrass data for `B` of the shape given
by the number-field S2a theorem: `i : X ≅ Proj` of the Weierstrass coordinate ring of `E'`, with
function-field pull-back `e` composed with the function-field identification of the projective
model (`hfield`) and `i(o) = O` (`hO`).

The evaluation in the Hodge line (`hodgeEval`) of a differential `η` of `L(X)` regular at `o` is

`η ↦ 1 ⊗ (image in 𝒢.cotangent of the value η(o) ∈ 𝔪_o/𝔪_o²)  ∈  hodgeSpace 1`,

built from the evaluation of Kähler differentials at the rational point `o` (given by the unit
section of `B`), its injectivity on the local ring, and the actual stalk maps of the projection of
the generic fibre and of `𝒢.gen` at the identity of the generic fibre.

**Main theorem** (`hodgeEval_invariantDifferential`). The Kähler transport along `e` of the
invariant differential `ω = dx/(2y + a₁x + a₃)` of `E'` is regular at `o`, and

`hodgeEval ω = 𝒢.wedge ![f] ≠ 0`,

where `f ∈ 𝔪_ξ` is the image, under the stalk maps of `i` at `o` and of the generic-fibre
identification, of the germ at `O` of the local parameter `-x/y` (`originParameter`). In the
form `𝒢.wedge ![f] = c • image(ω)` the constant is `c = 1`. The existence form
(`exists_weierstrassModel_hodgeEval`) combines it with the number-field S2a theorem.

Only the point equation `i(o) = O` is used (stalk maps at points); no equation of sections, no
group law of the projective model, and no property of `𝒢.gen` beyond being an isomorphism of group
objects are used. The integral structure (the lattice `𝒢.omega`, minimal discriminants, periods)
is not touched.

Locator: Silverman, *The Arithmetic of Elliptic Curves*, second edition, III.1.5 and IV.1;
Hartshorne, *Algebraic Geometry*, II.8.7.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.HodgeLineBinding

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing KaehlerDifferential TensorProduct
open ZInQ.DefFaltings
open ZInQ.Contrib.RC53Assist.S2aNumberField
open ZInQ.Contrib.RC53Assist.AbelianCurve (functionFieldAlgebra stalkAlgebra
  stalk_functionField_tower abelian_scheme_integral)

variable {K : Type} [Field K] {E : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L]

omit [NumberField L] in
/-- THEOREM (proved). Dimension one is preserved by base change. Locator:
`PkgI3.AbVar.dim_baseChange`. -/
theorem baseChange_dim_eq_one (hdim : E.dim = 1) : (E.baseChange L).dim = 1 :=
  (PkgI3.AbVar.dim_baseChange E L).trans hdim

/-- DEFINITION. The evaluation in the Hodge line of a differential regular at the origin:
`η ↦ 1 ⊗ (toModelCotangent (η(o)))`. Locator: `originValue`, `toModelCotangent`. -/
def hodgeEval (G : GroupModel E L) (hdim : E.dim = 1) (η : regularAtOrigin (E.baseChange L)) :
    G.hodgeSpace 1 :=
  (1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) 1
    ![toModelCotangent G (originValue (E.baseChange L) (baseChange_dim_eq_one hdim) η)]

/-- DEFINITION. The local parameter at the identity of the generic fibre corresponding to `-x/y`:
the image of the germ of `-x/y` at `O` under the stalk map of `i` at `o` and the inverse of
`originStalkEquiv`. Locator: `paramZ`, `stalkMapAt`, `originStalkEquiv`. -/
def originParameter (G : GroupModel E L) (E' : WeierstrassCurve L)
    (i : (E.baseChange L).X.left ≅ Proj E'.toProjective.grading)
    (hO : i.hom (identityPoint (E.baseChange L).X) = pointO E') : maximalIdeal G.genStalk :=
  ⟨(originStalkEquiv G).symm ((stalkMapAt i.hom hO).hom (paramZ E')),
    originStalkEquiv_symm_mem G (stalkMapAt_mem i.hom hO (paramZ_mem E'))⟩

/-- THEOREM (proved). The wedge of the local parameter is nonzero. Locator:
`wedge_single_ne_zero`, `paramZ_not_mem_sq`, `stalkMapAt_not_mem_sq`,
`originStalkEquiv_symm_not_mem_sq`. -/
theorem wedge_originParameter_ne_zero (G : GroupModel E L) (E' : WeierstrassCurve L)
    (i : (E.baseChange L).X.left ≅ Proj E'.toProjective.grading)
    (hO : i.hom (identityPoint (E.baseChange L).X) = pointO E') :
    G.wedge ![originParameter G E' i hO] ≠ 0 :=
  wedge_single_ne_zero G _ (originStalkEquiv_symm_not_mem_sq G
    (stalkMapAt_not_mem_sq i.hom hO (paramZ_not_mem_sq E')))

/-- THEOREM (proved). **The invariant differential evaluated in the Hodge line.** The transport
along `e` of `ω = dx/(2y + a₁x + a₃)` is regular at the origin and its evaluation in the Hodge line
is the wedge of the local parameter `-x/y`, a nonzero vector. Locator: Silverman, IV.1;
`invariant_eq_localUnit_inv_smul`, `pointEval_unit_inv_smul_D`, `wedge_originParameter_ne_zero`. -/
theorem hodgeEval_invariantDifferential (G : GroupModel E L) (hdim : E.dim = 1)
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
      hodgeEval G hdim ⟨_, hreg⟩ = G.wedge ![originParameter G E' i hO] ∧
      G.wedge ![originParameter G E' i hO] ≠ 0 := by
  haveI := abelian_scheme_integral (E.baseChange L).X
  letI := functionFieldAlgebra (E.baseChange L).X.hom
  letI := stalkAlgebra (E.baseChange L).X.hom (identityPoint (E.baseChange L).X)
  haveI := stalk_functionField_tower (E.baseChange L).X.hom (identityPoint (E.baseChange L).X)
  -- the germs `z = -x/y` and `w = -1/y` at the identity point, and the local unit
  have hzo := stalkMapAt_mem i.hom hO (paramZ_mem E')
  have hwo := stalkMapAt_mem i.hom hO (paramW_mem E')
  set zo := (stalkMapAt i.hom hO).hom (paramZ E') with hzo_def
  set wo := (stalkMapAt i.hom hO).hom (paramW E') with hwo_def
  have hρ := originRetraction_algebraMap (E.baseChange L)
  have hu1 : originRetraction (E.baseChange L) (localUnit E' zo wo) = 1 :=
    localUnit_retraction E' _ hρ (retraction_eq_zero_of_mem _ hρ hzo)
      (retraction_eq_zero_of_mem _ hρ hwo)
  have hu : IsUnit (localUnit E' zo wo) := isUnit_of_retraction_eq_one _ hρ hu1
  -- their rational functions
  have hfun : ∀ g, algebraMap _ (E.baseChange L).X.left.functionField
      ((stalkMapAt i.hom hO).hom g) = e (stalkPointOToFunctionField E' g) := by
    intro g
    rw [algebraMap_stalkMapAt, hfield]
    rfl
  have hzF : algebraMap _ (E.baseChange L).X.left.functionField zo =
      -e E'.toAffine.genericX / e E'.toAffine.genericY := by
    rw [hzo_def, hfun, stalkPointOToFunctionField_paramZ, map_div₀, map_neg]
  have hwF : algebraMap _ (E.baseChange L).X.left.functionField wo =
      -1 / e E'.toAffine.genericY := by
    rw [hwo_def, hfun, stalkPointOToFunctionField_paramW, map_div₀, map_neg, map_one]
  have huF : algebraMap _ (E.baseChange L).X.left.functionField (localUnit E' zo wo) =
      localUnit E' (-e E'.toAffine.genericX / e E'.toAffine.genericY)
        (-1 / e E'.toAffine.genericY) := by
    rw [map_localUnit E' _ (fun c => (IsScalarTower.algebraMap_apply L _ _ c).symm), hzF, hwF]
  -- the invariant differential in the parameter `z`
  have hy : e E'.toAffine.genericY ≠ 0 :=
    (map_ne_zero_iff e e.injective).mpr (genericY_ne_zero E')
  have hP : 2 * e E'.toAffine.genericY +
      algebraMap L (E.baseChange L).X.left.functionField E'.a₁ * e E'.toAffine.genericX +
      algebraMap L (E.baseChange L).X.left.functionField E'.a₃ ≠ 0 := by
    have h := (map_ne_zero_iff e e.injective).mpr
      (WeierstrassCurve.Affine.invariantDifferentialDenom_ne_zero E'.toAffine)
    rw [WeierstrassCurve.Affine.invariantDifferentialDenom_def] at h
    simpa only [map_add, map_mul, map_ofNat, AlgEquiv.commutes] using h
  have hu' : localUnit E' (-e E'.toAffine.genericX / e E'.toAffine.genericY)
      (-1 / e E'.toAffine.genericY) ≠ 0 := by
    rw [← huF]
    exact (hu.map _).ne_zero
  have key := invariant_eq_localUnit_inv_smul E' (e E'.toAffine.genericX)
    (e E'.toAffine.genericY) (genericPoint_equation_map E' e.toAlgHom) hy hP hu'
  -- the local differential `u⁻¹ • dz` at the identity point
  set ωo := ((↑hu.unit⁻¹ : (E.baseChange L).X.left.presheaf.stalk
    (identityPoint (E.baseChange L).X)) • D L _ zo) with hωo_def
  have hω : kaehlerTransport e (WeierstrassCurve.Affine.invariantDifferential E'.toAffine) =
      stalkKaehlerMap (E.baseChange L).X.hom (identityPoint (E.baseChange L).X) ωo := by
    rw [kaehlerTransport_invariantDifferential, key]
    change _ = KaehlerDifferential.map L L _ _ ωo
    rw [hωo_def, map_smul, KaehlerDifferential.map_D,
      ← algebraMap_smul (E.baseChange L).X.left.functionField (↑hu.unit⁻¹ :
        (E.baseChange L).X.left.presheaf.stalk (identityPoint (E.baseChange L).X)),
      map_units_inv, IsUnit.unit_spec, huF, hzF]
  have hreg := stalkKaehlerMap_mem_regularAtOrigin (E.baseChange L) ωo
  rw [← hω] at hreg
  refine ⟨hreg, ?_, wedge_originParameter_ne_zero G E' i hO⟩
  have hsub : (⟨_, hreg⟩ : regularAtOrigin (E.baseChange L)) =
      ⟨_, stalkKaehlerMap_mem_regularAtOrigin (E.baseChange L) ωo⟩ := Subtype.ext hω
  have hev : originEval (E.baseChange L) ωo = (maximalIdeal _).toCotangent ⟨zo, hzo⟩ :=
    pointEval_unit_inv_smul_D _ hρ hu.unit (by rw [IsUnit.unit_spec]; exact hu1) hzo
  unfold hodgeEval
  rw [hsub, originValue_stalkKaehlerMap, hev, toModelCotangent_toCotangent]
  unfold GroupModel.wedge originParameter
  congr 2
  funext j
  fin_cases j
  rfl

/-- THEOREM (proved). **Existence form.** For every smooth group model `𝒢` of a one-dimensional
abelian variety `E`, there are Weierstrass data `(E', e, i)` for `E_L` as in the number-field S2a
theorem such that the transported invariant differential is regular at the origin and its
evaluation in the Hodge line is the nonzero wedge of the local parameter `-x/y`. Locator:
`abVar_projectiveWeierstrassModel_numberField`, `hodgeEval_invariantDifferential`. -/
theorem exists_weierstrassModel_hodgeEval (G : GroupModel E L) (hdim : E.dim = 1) :
    letI := abelian_scheme_integral (E.baseChange L).X
    letI := functionFieldAlgebra (E.baseChange L).X.hom
    ∃ E' : WeierstrassCurve L, E'.IsElliptic ∧
      ∃ (e : E'.toAffine.FunctionField ≃ₐ[L] (E.baseChange L).X.left.functionField)
        (i : (E.baseChange L).X.left ≅ Proj E'.toProjective.grading),
        i.hom ≫ projectiveStructure E' = (E.baseChange L).X.hom ∧
        i.hom.functionFieldMap.hom = e.toRingHom.comp (projFunctionFieldEquiv E').toRingHom ∧
        ∃ hO : i.hom (identityPoint (E.baseChange L).X) = pointO E',
          ∃ hreg : kaehlerTransport e (WeierstrassCurve.Affine.invariantDifferential E'.toAffine)
              ∈ regularAtOrigin (E.baseChange L),
            hodgeEval G hdim ⟨_, hreg⟩ = G.wedge ![originParameter G E' i hO] ∧
            G.wedge ![originParameter G E' i hO] ≠ 0 := by
  haveI := abelian_scheme_integral (E.baseChange L).X
  letI := functionFieldAlgebra (E.baseChange L).X.hom
  obtain ⟨E', hE', e, i, hi, hfield, hO⟩ :=
    abVar_projectiveWeierstrassModel_numberField L (E.baseChange L) (baseChange_dim_eq_one hdim)
  haveI := hE'
  exact ⟨E', hE', e, i, hi, hfield, hO, hodgeEval_invariantDifferential G hdim E' e i hfield hO⟩

end ZInQ.Contrib.RC53Assist.HodgeLineBinding

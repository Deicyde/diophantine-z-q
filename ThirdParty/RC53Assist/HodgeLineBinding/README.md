# The invariant differential in the Hodge line of a group model

Setting: `K, L` fields with `L` a number field and `[Algebra K L]`; `E : PkgI3.AbVar K` with
`E.dim = 1`; `B = E.baseChange L`, `X = B.X.left`, `o = identityPoint B.X`;
`G : ZInQ.DefFaltings.GroupModel E L` with `ξ = G.genericUnit`. Weierstrass data
`(E', e, i)` for `B` of the shape of `abVar_projectiveWeierstrassModel_numberField`, of which only
`hfield : i.hom.functionFieldMap.hom = e.toRingHom.comp (projFunctionFieldEquiv E').toRingHom` and
`hO : i.hom o = pointO E'` are used (a point equation, no section equation).

## Constructions (no basis of any line is chosen)

* `pointEval`: Kähler lift of the derivation `a ↦ (a - a(P)) mod 𝔪²` of a local algebra with
  a rational point.
* `originEval`: `pointEval` at `o`; the value `a(o)` is given by the unit section of `B`.
* `regularAtOrigin`: the differentials of `L(X)` coming from `Ω[𝒪_{X,o}/L]`.
* `originValue : regularAtOrigin →ₗ[L] 𝔪_o/𝔪_o²`, through the injective restriction
  `Ω[𝒪_{X,o}/L] → Ω[L(X)/L]`.
* `originStalkEquiv : 𝒪_{𝒢,ξ} ≃+* 𝒪_{X,o}`: the stalk map of `𝒢 ×_{𝓞_L} L → 𝒢` at the identity
  `ξ_L` of the generic fibre, followed by the inverse of the stalk map of `G.gen` at `ξ_L`.
* `toModelCotangent : 𝔪_o/𝔪_o² → G.cotangent`, induced by `originStalkEquiv`.
* `hodgeEval`, `hodgeEvalLinear`: `η ↦ 1 ⊗ ι(toModelCotangent (originValue η))` in
  `G.hodgeSpace 1`; `L`-linear.
* `kaehlerTransport e`: Kähler functoriality of the field isomorphism `e`.
* `paramZ`, `paramW`: the germs at `O` of `-x/y` and `-1/y`.
* `originParameter G E' i hO`: `originStalkEquiv⁻¹` of the stalk map of `i` at `o` applied to
  `paramZ`.
* `lineComparisonEquiv`: the regular Kähler line of `E'` `≃ₗ[L]` `G.hodgeSpace 1`.

## Main results (all proved; standard axioms only, see `Logs/AxiomAudit.txt`)

* `hodgeEval_invariantDifferential`: the transport of `ω = dx/(2y + a₁x + a₃)` is regular at `o`
  and `hodgeEval ω = G.wedge ![originParameter G E' i hO] ≠ 0` (so `c = 1`).
* `exists_weierstrassModel_hodgeEval`: the same, with the Weierstrass data produced by S2a.
* `invariant_eq_localUnit_inv_smul`, `invariantDifferential_eq_localUnit_inv_smul`:
  `ω = u⁻¹ • d(-x/y)`, `u = 1 - a₁z - a₂z² - 2a₃w - 2a₄zw - 3a₆w²`; `u` has value `1` at `o`
  (unit section of `B`) and valuation `1` at infinity on the curve.
* `originStalkEquiv_structMap`: compatibility of `originStalkEquiv` with the constants `𝓞_L ⊆ L`.
* `hodgeEval_smul`, `hodgeEvalLinear`: `L`-linearity.
* `finrank_hodgeSpace_one`, `finrank_hodgeSpace_one_of_dim_one`: `G.hodgeSpace 1` is an `L`-line.
* `exists_smul_wedge_eq`: it is spanned by `G.wedge ![originParameter G E' i hO]`.
* `lineComparison_bijective`, `lineComparisonEquiv_invariant`: the comparison is an isomorphism
  of lines with `c • ω ↦ c • G.wedge ![f]`.
* `wedge_eq_smul_hodgeEval`: for every local parameter `t` at `ξ`,
  `G.wedge ![t] = c • hodgeEval ω` with `c ≠ 0`.

## Not done here

* The integral structure: `G.omega`, `G.detLattice 1`, minimal discriminants, and the analytic
  normalization of periods.
* The identification of the transported `ω` with a global section of the sheaf of differentials
  of `X` (it needs regularity of `ω` at every point of `X`, not only at `o`).

Build: `lake build +ZInQKernel.Contrib.RC53Assist.HodgeLineBinding.All`.

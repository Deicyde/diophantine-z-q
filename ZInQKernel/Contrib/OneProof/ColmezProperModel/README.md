# `ColmezProperModel`: `𝒳(O_{C_p}) = X(C_p)` for a proper model, in Lean

Colmez, *Périodes p-adiques des variétés abéliennes*, Math. Ann. 292 (1992), p. 638, fixes a
proper model `𝒳` of the abelian variety `X` over `O_K` and uses "Par construction, 𝒳(O_{C_p})
s'identifie à X(C_p)". `ColmezTiltIso/PRINTED.md` records this as the one remaining presupposition
of the row `colmez1992DeRhamAbVar` and gives a schematic statement `ProperModelPoints`. This
directory makes that statement precise and proves everything in it except the existence of the
model.

## Files

| File | Imports | Content |
|---|---|---|
| `Valuative.lean` | Mathlib | the valuative criterion as a bijection `X(R)_y ≃ X(K)_y` |
| `Points.lean` | `Valuative`, `G9.I4Layer` | generic fibre, `𝒳(R) ≃ A(K)` for a proper model, equivariance |
| `Colmez.lean` | `Points`, `ColmezTorsionIso.Basic` | `O_F`, `ι`, `ProperModelPoints`, `ProperModelExists` |
| `ModelTate.lean` | `Colmez` | the group `𝒳(O_{C_p})`, `T_p` from it, `≃ TCp`, shape transport |
| `ModelRow.lean` | `ModelTate`, `ColmezTiltIso.RowPrinted` | the row with `T_p = lim 𝒳(O_{C_p})[pⁿ]` |
| `Check.lean` | `ModelRow` | `#print axioms` for the main declarations |
| `MilneLeaf.lean` | `G9.I4Layer` | `ℙᴺ_ℤ` (`projSpaceZ`), the printed leaf `MilneThm71Projective` (Milne, Thm 7.1) |
| `MilneModel.lean` | `MilneLeaf`, `Colmez` | the closure of `A` in `ℙᴺ_{O_F}`, `properModelExists_of_milne` |
| `MilneRow.lean` | `MilneModel`, `ModelRow` | `Colmez1992DeRhamAbVar` from `MilneThm71Projective` and `Colmez1992DeRhamAbVarModel` (`colmez1992DeRhamAbVar_of_model_milne`) |
| `MilneCheck.lean` | `MilneRow` | `#print axioms` for the route from Milne's Theorem 7.1 |

## Main statements

* `restrictPt_bijective`, `restrictEquiv` (`Valuative.lean`): for `f : X ⟶ Y` satisfying the
  valuative criterion (any proper `f`, by Mathlib's `IsProper.eq_valuativeCriterion`, Stacks 0BX5),
  a valuation ring `R` with fraction field `K` and `y : Spec R ⟶ Y`, restriction along
  `Spec K ⟶ Spec R` is a bijection from the `R`-points of `X` over `y` to the `K`-points over
  `Spec K ⟶ Spec R ⟶ Y`.
* `genericEquiv`, `genericEquiv_gal` (`Points.lean`): if the generic fibre
  `𝒳 ×_{Spec O} Spec F` of `π : 𝒳 ⟶ Spec O` is isomorphic to `A` as an `F`-scheme, the `L`-points
  of `𝒳` over `Spec O` are `A.Pt L`, `Aut_F(L)`-equivariantly.
* `modelEquiv`, `modelEquiv_act` (`Points.lean`): for `π` proper, `R` a valuation ring with
  fraction field `K` over `F` and `ι : O →+* R` compatible with `O → F → K`,
  `{x : Spec R ⟶ 𝒳 | x ≫ π = Spec ι} ≃ A.Pt K`, intertwining `x ↦ Spec τ ≫ x` with `A.galAct τK`.
* `Colmez.lean`:
  * `OF p F` is the integral closure of `ℤ_p` in `F` (with `F` a `ℤ_p`-algebra through `ℚ_p`).
    `iotaO p F : O_F →+* 𝓞_ℂ_[p]` is the restriction of the tree's `algCp`. Its values lie in
    `𝓞_ℂ_[p]` because a valuation subring is integrally closed (`algCp_mem_O`).
  * `modelPtsEquiv` and `modelPtsEquiv_gal`: for every proper `π : 𝒳 ⟶ Spec O_F` with generic
    fibre `A`, `𝒳(O_{C_p}) ≃ A.Pt ℂ_[p]`, `G_F`-equivariantly. `σ` acts on `𝒳(O_{C_p})` by
    `x ↦ Spec (oAct (gfToGqp σ)) ≫ x` and on `A.Pt ℂ_[p]` by `A.galAct (cpGal p F σ)`.
  * `ProperModelPoints` is the statement of `PRINTED.md`. `ProperModelExists` is its first half:
    a proper model with generic fibre `A` exists. **`properModelPoints_iff`** proves
    `ProperModelPoints ↔ ProperModelExists`, and `properModelPoints_of_exists` gives one direction.
* `ModelTate.lean`:
  * `ModelGrp`: `𝒳(O_{C_p})` with the group law transported from `A(ℂ_p)`, as Colmez does.
  * `galModelHom`: the geometric action is a group automorphism.
  * `TModel = lim 𝒳(O_{C_p})[pⁿ]`, with `tModelEquiv : TModel ≃ₗ[ℤ_p] TCp p A` and
    `tModelEquiv_gal`, so `T_p` built from the model is the tree's `TCp`.
  * `shape_transport`: the shape of the Colmez rows is invariant under an equivariant isomorphism of
    the `T_p`-side.
* `ModelRow.lean`:
  * `Colmez1992DeRhamAbVarModel` is `Colmez1992DeRhamAbVarPrinted` with
    `T_p(X) = lim 𝒳(O_{C_p})[pⁿ]`, for every proper model.
  * `colmez1992DeRhamAbVarModel_of_printed`.
  * `colmez1992DeRhamAbVarPrinted_of_model` and `colmez1992DeRhamAbVar_iff_model`, both under
    `ProperModelExists`.

## What is not proved: `ProperModelExists`

The tree's abelian variety `ZInQ.Contrib.G9.PkgI4.I3.AbVar F` (`G9/I4Layer.lean`) has these fields:

* an `F`-scheme `X`;
* `GrpObj X`;
* `IsProper`, `Smooth` and `GeometricallyIntegral` for `X.hom`.

It has no projective embedding and no ample line bundle. The model through a projective embedding
(the scheme-theoretic closure of `A ⊂ ℙⁿ_F` in `ℙⁿ_{O_F}`) therefore needs the projectivity of
abelian varieties first. That uses ample line bundles and the theorem of the square, and neither is
in Mathlib. The other route, Nagata compactification of `A → Spec F ⟶ Spec O_F`, is not in Mathlib
either. `MilneModel.lean` takes the first route, with projectivity as an input
(`MilneThm71Projective`, Milne's Theorem 7.1), and proves `ProperModelExists` from it
(`properModelExists_of_milne`); since y3-colmez-1127 that input is the row `milneThm71Projective`.

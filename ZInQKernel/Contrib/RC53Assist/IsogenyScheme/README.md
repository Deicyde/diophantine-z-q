# Projective Weierstrass model, function field and the point at infinity

`ProjectiveModel.lean` (namespace `ZInQ.Contrib.RC53Assist.IsogenyScheme`) supplies, for every
Weierstrass curve `E` over `ℚ`, the three inputs R1, R2 and R4 of the F2 step in
`CloudB3RC53/ModularWeil/IsogenyFunctionField.lean`. Everything is proved; no hypothesis or input is
added, and the curve need not be elliptic. Source: Silverman, *The Arithmetic of Elliptic Curves*,
I.1–I.2, II.1–II.2, III.1, III.4.

## R1: the projective model

`X = Proj A` for the homogeneous coordinate ring
`A = ℚ[X, Y, Z] ⧸ (Y²Z + a₁XYZ + a₃YZ² - X³ - a₂X²Z - a₄XZ² - a₆Z³)`, graded by total degree.

- `irreducibleSpace_proj`, `isIntegral_proj`: `X` is irreducible and integral. The zero ideal of the
  domain `A` is the generic point (`genericPoint_proj`).
- `isProper_proj`: the structure morphism `X ⟶ Spec A₀` is proper, where `A₀ = ℚ`.

## R2: the function field

- `projFunctionFieldEquiv E : X.functionField ≃+* E.toAffine.FunctionField`.
- `projModel E : ModularWeil.SchemeModel E` bundles `X` and this identification.
- The chart ring `A_(Z)` is the affine coordinate ring (`affineEquivZChart`: `x ↦ X/Z`, `y ↦ Y/Z`).
  The homogeneous localization at the zero ideal is its fraction field (`isFractionRing_zChart`).
- On germs the identification is dehomogenization, `a / b ↦ a(x, y, 1) / b(x, y, 1)`
  (`atPrimeEquivFunctionField_mk`, `projFunctionFieldEquiv_germ`).

## R4: `infinityPlace` is the valuation at `O`

`pointO E` is the point `O = [0 : 1 : 0]`.

- `infinityPlace_le_one_iff_mem_stalkPointOImage`, `stalkPointOImage_eq_valuationSubring` and
  `stalkPointOEquivValuationSubring`: the local ring of `X` at `O`, read in the function field, is
  exactly the valuation ring of `infinityPlace`.
- `infinityPlace_lt_one_iff_mem_maximalIdeal`: the maximal ideals match.
- `isDiscreteValuationRing_stalk_pointO`: the local ring at `O` is a discrete valuation ring.
- `dominated_iff_eq_pointO`: `O` is the only point whose local ring is dominated by the place at
  infinity.

## Pointedness and the consumer

- `isPointedMap_iff_apply_pointO`: for a dominant morphism `f` of projective models,
  `ModularWeil.IsPointedMap (projModel E₁) (projModel E₂) f ↔ f (pointO E₁) = pointO E₂`.
- `isogenyOfProjMorphism`, `isogenyOfProjMorphism_fieldPullback`: such a morphism with
  `f(O₁) = O₂` gives a `TauCeti.Isogeny` through `ModularWeil.isogenyOfDominant`, and its
  `fieldPullback` is the pullback of rational functions along `f`.
- `eq_of_fieldMap_eq`, `eq_of_isogenyOfProjMorphism_eq`: a dominant morphism of projective models
  is determined by its pullback of rational functions, so the translation is faithful.
- `isogenyOfProjMorphism_id_fieldPullback`: the identity of the projective model gives the identity
  (non-vacuity on the projective model itself).

## What this does not cover

The source isogeny of abelian varieties still has to be presented as a dominant morphism between
these projective models. That uses the identification of a one-dimensional abelian variety with its
Weierstrass model (item S2 of `NewformPeriodsDictionary/README.md`), now proved in
`GroupDifferentials/S2a.lean` (`abVar_projectiveWeierstrassModel_unconditional`, which sends the
identity to `pointO E`). Once that is done, the morphism
is dominant and sends `O₁` to `O₂`, and this file applies.

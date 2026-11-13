/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-
Ported for the T18 contribution from TauCetiProject/TauCeti@1f9b4414105d86e487a4ac4c3d3397076a44d0d2,
TauCeti/NumberTheory/Cyclotomic/FixedField.lean. Changes: imports relocated to the owned flat contribution directory;
proof and definition bodies initially unchanged. Project pins are not changed.
See docs/research/t18-frobenius-density.md for attribution and license text.
-/
module

public import ZInQKernel.Contrib.FrobeniusDensity.Tau_FieldTheory_Galois_FixedField
public import ZInQKernel.Contrib.FrobeniusDensity.Tau_NumberTheory_Cyclotomic_Adjoin

/-!
# The fixed field of a subgroup meeting the cyclotomic fixers trivially

If `M` contains a primitive `m`-th root of unity and a subgroup `H ≤ Gal(M/K)` meets
`Gal(M/K(μ_m))` trivially, then `M` is an `m`-th cyclotomic extension of the fixed field `M ^ H`.

Only the subgroup `H` is assumed finite; `M / K` need not be finite or Galois. The root of unity
enters as a hypothesis rather than through an ambient cyclotomic tower, so no separately quantified
intermediate field or cyclotomic tower appears among the arguments — the fixed field itself is of
course an `IntermediateField K M`,
being the base of the conclusion.

Nothing here needs `H` to be cyclic. The Chebotarev application takes `H = Subgroup.zpowers (σ, τ)`,
but the argument is the Galois correspondence and uses neither a generator nor cyclicity.

## Main results

* `IsPrimitiveRoot.fixedField_isCyclotomicExtension_of_inf_fixingSubgroup_eq_bot`

## Provenance

The proof is adapted from the private `compositum_isCyclotomic_over_fixedField` in
`CebotarevDensity/Abelian.lean` of
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0,
Birkbeck--Brasca) at commit `8575c9df1ae0a61120ab5c964c7911414254bec7`. That version is stated for
a cyclic subgroup over a tower `K ⊆ L ⊆ M` of number fields; the hypotheses here are weaker.
-/

public section

open IntermediateField

/-- **The fixed field of `H` carries the cyclotomic extension**, whenever `H` meets the fixers of
`K(μ_m)` trivially.

The trivial meet says exactly that `M ^ H` and `K(μ_m)` generate `M`, so adjoining a primitive
root to `M ^ H` recovers all of `M`. -/
theorem IsPrimitiveRoot.fixedField_isCyclotomicExtension_of_inf_fixingSubgroup_eq_bot
    {K M : Type*} [Field K] [Field M] [Algebra K M]
    {m : ℕ} [NeZero m] {ζ : M} (hζ : IsPrimitiveRoot ζ m) (H : Subgroup (M ≃ₐ[K] M)) [Finite H]
    (hmeet : H ⊓ (adjoin K {b : M | b ^ m = 1}).fixingSubgroup = ⊥) :
    IsCyclotomicExtension {m} (fixedField H) M := by
  set F : IntermediateField K M := fixedField H
  set Kμ : IntermediateField K M := adjoin K {b : M | b ^ m = 1}
  have hadjζ : adjoin K {ζ} = Kμ := hζ.adjoin_singleton_eq_adjoin_nth_roots
  -- a trivial meet of fixing subgroups is a sup equal to `⊤`
  have htop : F ⊔ Kμ = ⊤ := (H.fixedField_sup_eq_top_iff Kμ).mpr hmeet
  -- hence `ζ` generates `M` over `F`
  have htopF : adjoin F {ζ} = ⊤ := by
    apply restrictScalars_injective K
    rw [restrictScalars_adjoin_eq_sup, hadjζ, htop, restrictScalars_top]
  have : Algebra.IsIntegral F M := Algebra.IsIntegral.of_finite F M
  have hcyc : IsCyclotomicExtension {m} F (adjoin F {ζ}) :=
    IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension (K := F) hζ
  rw [htopF] at hcyc
  exact IsCyclotomicExtension.equiv (S := {m}) (A := F) (f := topEquiv)

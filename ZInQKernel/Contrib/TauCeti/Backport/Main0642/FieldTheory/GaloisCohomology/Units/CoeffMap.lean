/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 0642eae29e0a, module
-- TauCeti.FieldTheory.GaloisCohomology.Units.CoeffMap), Apache-2.0: declarations of that module absent from its commit-5a01f5fe version, which
-- is vendored as `ZInQKernel.Contrib.TauCeti.FieldTheory.GaloisCohomology.Kummer` (task selmer-2infty).
-- Modified for the Z-in-Q kernel: declarations already in the vendored module removed; imports rewritten.
module

public import ZInQKernel.Contrib.TauCeti.FieldTheory.GaloisCohomology.Kummer
public import ZInQKernel.Contrib.TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Extension
public import ZInQKernel.Contrib.TauCeti.FieldTheory.GaloisCohomology.Coefficients

/-!
# Unit coefficients along an embedding of fields

For a `K`-embedding `σ : L →ₐ[K] Kˢ`, the chosen identification of separable closures
`separableClosureRingEquiv K L σ : Lˢ ≃+* Kˢ` carries the units of `Lˢ` to the units of `Kˢ` and
back. These are the coefficient legs, with unit coefficients, of corestriction and restriction
along `L/K`; they involve no exponent, Kummer map or Hilbert 90, so they live here rather than in
`TauCeti.FieldTheory.GaloisCohomology.Kummer`, which uses them for the Kummer sequence.

## Main definitions

* `TauCeti.unitsCoeffMapSymm`: the units of `Lˢ` as units of `Kˢ`.
* `TauCeti.unitsCoeffMap`: the units of `Kˢ` as units of `Lˢ`, its inverse.

## Main results

* `TauCeti.unitsCoeffMapSymm_smul`, `TauCeti.unitsCoeffMap_smul`: both are equivariant along
  `G_L ≃ₜ* Gal(Kˢ/σ(L))`; `TauCeti.unitsCoeffMap_coe_smul` is the second with `G_L` acting
  through `G_K`.
* `TauCeti.unitsCoeffMapSymm_unitsCoeffMap`, `TauCeti.unitsCoeffMap_unitsCoeffMapSymm`: they are
  inverse to each other, also as additive maps (`TauCeti.unitsCoeffMapSymm_comp_unitsCoeffMap`,
  `TauCeti.unitsCoeffMap_comp_unitsCoeffMapSymm`).
* `TauCeti.unitsCoeffMapSymm_unitsCoeffPow`, `TauCeti.unitsCoeffMap_unitsCoeffPow`: both commute
  with the `n`th power map `TauCeti.unitsCoeffPow`.
* `TauCeti.unitsCoeffMapSymm_coe_baseUnitsEquivInvariants`,
  `TauCeti.unitsCoeffMap_coe_embeddedUnitsInvariants`,
  `TauCeti.unitsCoeffMap_coe_baseUnitsEquivInvariants`: their effect on the invariants attached to
  units of `L` and of `K`.
-/

public section

noncomputable section

namespace TauCeti

variable (K : Type*) [Field K] (L : Type*) [Field L] [Algebra K L]
  (σ : L →ₐ[K] SeparableClosure K)

/-- `TauCeti.unitsCoeffMap_smul` with `g` acting on `(Kˢ)ˣ` through its image in `G_K`, the form
the compatible pair of `TauCeti.galoisResUnits` takes once the inclusion of the subgroup fixing
`σ(L)` is unfolded. -/
@[simp]
theorem unitsCoeffMap_coe_smul (g : AbsoluteGaloisGroup L) (x : UnitsCoeff K) :
    unitsCoeffMap K L σ
        ((absoluteGaloisGroupEquivFixingSubgroup K L σ g : AbsoluteGaloisGroup K) • x) =
      g • unitsCoeffMap K L σ x :=
  unitsCoeffMap_smul K L σ g x

/-- `TauCeti.unitsCoeffMapSymm_unitsCoeffMap` as an equality of additive maps. -/
@[simp]
theorem unitsCoeffMapSymm_comp_unitsCoeffMap :
    (unitsCoeffMapSymm K L σ).comp (unitsCoeffMap K L σ) = AddMonoidHom.id (UnitsCoeff K) :=
  AddMonoidHom.ext (unitsCoeffMapSymm_unitsCoeffMap K L σ)

/-- `TauCeti.unitsCoeffMap_unitsCoeffMapSymm` as an equality of additive maps. -/
@[simp]
theorem unitsCoeffMap_comp_unitsCoeffMapSymm :
    (unitsCoeffMap K L σ).comp (unitsCoeffMapSymm K L σ) = AddMonoidHom.id (UnitsCoeff L) :=
  AddMonoidHom.ext (unitsCoeffMap_unitsCoeffMapSymm K L σ)

/-! ### Interaction with the coefficient operations -/

/-- `unitsCoeffMap` commutes with the `n`th power map of the Kummer sequence. -/
@[simp]
theorem unitsCoeffMap_unitsCoeffPow (n : ℕ) (x : UnitsCoeff K) :
    unitsCoeffMap K L σ (unitsCoeffPow K n x) = unitsCoeffPow L n (unitsCoeffMap K L σ x) :=
  Additive.toMul.injective <| Units.ext <| by simp

/-- `unitsCoeffMap` carries the invariant of `Gal(Kˢ/σ(L))` attached to `b ∈ Lˣ` to the invariant
of `G_L` attached to `b`, inverting `TauCeti.unitsCoeffMapSymm_coe_baseUnitsEquivInvariants`. -/
@[simp]
theorem unitsCoeffMap_coe_embeddedUnitsInvariants (b : Lˣ) :
    unitsCoeffMap K L σ (embeddedUnitsInvariants K L σ b) =
      baseUnitsEquivInvariants L (Additive.ofMul b) :=
  (congrArg (unitsCoeffMap K L σ)
    (unitsCoeffMapSymm_coe_baseUnitsEquivInvariants K L σ b)).symm.trans
    (unitsCoeffMap_unitsCoeffMapSymm K L σ _)

/-- `unitsCoeffMap` carries the invariant of `G_K` attached to `a ∈ Kˣ` to the invariant of `G_L`
attached to the image of `a` in `Lˣ`. -/
@[simp]
theorem unitsCoeffMap_coe_baseUnitsEquivInvariants (a : Additive Kˣ) :
    unitsCoeffMap K L σ (baseUnitsEquivInvariants K a) =
      baseUnitsEquivInvariants L (Additive.ofMul (Units.map (algebraMap K L : K →* L) a.toMul)) :=
  Additive.toMul.injective <| Units.ext <| by
    simp [IsScalarTower.algebraMap_apply K L (SeparableClosure L)]

end TauCeti

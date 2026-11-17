/-
Ported with Codex assistance on 2026-11-14 from trureturing@8af78b5bb176c99b2750222c0dd3d00a475d39eb.
Source: D5/S3/Factorization/Dedekind/HilbertDifferent/RingTheory/Valuation/ValuativeRel/Extension.lean
Original SHA-256: 551b41e5831851de4b54d09afb5ac54a185081427a6a81a20c31fa21f95c80c1
Changes: contribution import paths and namespace; retained proof content.
Full licenses and provenance: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
-/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/- Adapted to the repository-pinned Mathlib API; only declarations needed by the
Hilbert different consumer are retained. Source: TauCeti@33c2099c678ea391f7ea3e0ddaf945a76a625e5d,
TauCeti/RingTheory/Valuation/ValuativeRel/Extension.lean.
Full license and pertinent inherited attribution: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
Replace this port by direct use when this project's pinned Mathlib supplies an equivalent declaration. -/


import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
import ZInQKernel.Contrib.HilbertDifferent.Support.TameDifferent

noncomputable section

section

open ValuativeRel

namespace ValuativeExtension

variable {A B : Type*} [CommRing A] [Ring B] [ValuativeRel A] [ValuativeRel B]
  [Algebra A B] [ValuativeExtension A B]

/- A compatible extension of valuative relations makes the canonical valuation on the larger
ring an extension, in Mathlib's valuation-level sense, of the canonical valuation on the base.
-/
instance valuationHasExtension :
    Valuation.HasExtension (valuation A) (valuation B) where
  val_isEquiv_comap :=
    (ValuativeRel.isEquiv ((valuation B).comap (algebraMap A B)) (valuation A)).symm

end ValuativeExtension

namespace TauCeti

/- Compatibility of valuative relations composes along an algebra tower. -/
variable {K L : Type*} [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [Algebra K L] [ValuativeExtension K L]

local notation "𝒪ᵥ[" K "]" => Valuation.integer (valuation K)
local notation "𝓀ᵥ[" K "]" => IsLocalRing.ResidueField ↥𝒪ᵥ[K]

/- The structure map of a compatible extension restricts to its rings of integers. -/
noncomputable instance integerRingAlgebra : Algebra 𝒪ᵥ[K] 𝒪ᵥ[L] :=
  Valuation.HasExtension.instAlgebra_valuationSubring (valuation K) (valuation L)

/- The local map on rings of integers induces the residue-field extension. -/
noncomputable instance residueFieldAlgebra : Algebra 𝓀ᵥ[K] 𝓀ᵥ[L] :=
  IsLocalRing.ResidueField.instAlgebra

/- Coercing the integer-ring structure map to `L` gives the field structure map. -/
theorem coe_algebraMap_integerRing (x : 𝒪ᵥ[K]) :
    ((algebraMap 𝒪ᵥ[K] 𝒪ᵥ[L] x : 𝒪ᵥ[L]) : L) = algebraMap K L (x : K) :=
  Valuation.HasExtension.coe_algebraMap_valuationSubring_eq (valuation K) (valuation L) x

end TauCeti

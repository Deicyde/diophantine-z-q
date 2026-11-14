/-
Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_Ideal_height_eq_one_of_isDiscreteValuationRing_localization_atPrime.lean
  Retrieved      : 2026-11-14 (raw.githubusercontent.com, byte-for-byte)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original.
The changes are mechanical only; no statement, hypothesis, definition or proof term was
altered, weakened or omitted:
  * 1 internal `import`s retargeted to `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil`.
  * 1 scope(s) the source leaves open at EOF closed explicitly (end P2MW.S_Ideal_height_eq_one_of_isDiscreteValuationRing_localization_atPrime) so the port namespace can be closed; Lean closes these implicitly at EOF in the original, so this is a no-op.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_Ideal_height_eq_one_of_isDiscreteValuationRing_localization_atPrime

set_option autoImplicit false

theorem solution {R : Type*} [CommRing R] [IsDomain R] (p : Ideal R) [p.IsPrime]
    (h : IsDiscreteValuationRing (Localization.AtPrime p)) : p.height = 1 := by
  haveI := h
  have hnf : ¬ IsField (Localization.AtPrime p) := fun hF =>
    IsDiscreteValuationRing.not_a_field (R := Localization.AtPrime p)
      ((IsLocalRing.isField_iff_maximalIdeal_eq).mp hF)
  have hd1 : ringKrullDim (Localization.AtPrime p) = 1 :=
    IsPrincipalIdealRing.ringKrullDim_eq_one (Localization.AtPrime p) hnf
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p)] at hd1
  exact_mod_cast hd1

end P2MW.S_Ideal_height_eq_one_of_isDiscreteValuationRing_localization_atPrime

end ZInQ.Contrib.CloudW03NeronSurj.FLT

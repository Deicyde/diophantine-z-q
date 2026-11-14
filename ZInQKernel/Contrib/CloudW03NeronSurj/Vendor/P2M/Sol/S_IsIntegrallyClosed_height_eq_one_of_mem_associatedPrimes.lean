/-
Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_IsIntegrallyClosed_height_eq_one_of_mem_associatedPrimes.lean
  Retrieved      : 2026-11-14 (raw.githubusercontent.com, byte-for-byte)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original.
The changes are mechanical only; no statement, hypothesis, definition or proof term was
altered, weakened or omitted:
  * 3 internal `import`s retargeted to `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil`.
  * 1 scope(s) the source leaves open at EOF closed explicitly (end P2MW.S_IsIntegrallyClosed_height_eq_one_of_mem_associatedPrimes) so the port namespace can be closed; Lean closes these implicitly at EOF in the original, so this is a no-op.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Theorems.Thm_IsIntegrallyClosed_isDiscreteValuationRing_localization_of_mem_associatedPrimes
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Theorems.Thm_Ideal_height_eq_one_of_isDiscreteValuationRing_localization_atPrime
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_IsIntegrallyClosed_height_eq_one_of_mem_associatedPrimes

theorem solution
    {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]
    {x : B} (hx : x ≠ 0) (P : Ideal B) [P.IsPrime]
    (hP : P ∈ associatedPrimes B (B ⧸ Ideal.span {x})) : P.height = 1 :=
  Ideal.height_eq_one_of_isDiscreteValuationRing_localization_atPrime P
    (IsIntegrallyClosed.isDiscreteValuationRing_localization_of_mem_associatedPrimes hx P hP)

end P2MW.S_IsIntegrallyClosed_height_eq_one_of_mem_associatedPrimes

end ZInQ.Contrib.CloudW03NeronSurj.FLT

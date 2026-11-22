/-
Source-proof reuse from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_Module_depth_quotSMulTop_succ_eq.lean
  Licence        : Apache License, Version 2.0
  Notices        : ZInQKernel/Contrib/CloudW03NeronSurj/NOTICE
                   ZInQKernel/Contrib/CloudW03NeronSurj/ATTRIBUTION

NOTICE OF MODIFICATION — SOURCE-PROOF REUSE (Apache-2.0 §4(b)).
The original duplicated Ws14Port proof core has been removed from this file.
The solution's statement, hypotheses and universe binders are retained literally;
its proof now reuses the exact depth_quotSMulTop_succ_eq theorem in the vendored
S_Module_depth_le_ringKrullDim_quotient_of_mem_associatedPrimes proof core, from
the same locked source revision. The proof term and imports have therefore changed.
This is reuse of the original FLT regular-sequence depth proof, not replacement
by Mathlib's Ext-based depth, and introduces no additional assumptions.
The retained donor carries the source proof and its attribution notices.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_Patching_SystemTypes
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.P2M.Sol.S_Module_depth_le_ringKrullDim_quotient_of_mem_associatedPrimes

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

w03_open "IsLocalRing Module"

namespace P2MW.S_Module_depth_quotSMulTop_succ_eq

open IsLocalRing RingTheory

theorem solution
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    {x : R} (hx : x ∈ maximalIdeal R) (hxreg : IsSMulRegular M x) :
    Module.depth R (QuotSMulTop x M) + 1 = Module.depth R M :=
  _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_Module_depth_le_ringKrullDim_quotient_of_mem_associatedPrimes.Ws14Port.Module.depth_quotSMulTop_succ_eq
    (R := R) M hx hxreg

end P2MW.S_Module_depth_quotSMulTop_succ_eq

end ZInQ.Contrib.CloudW03NeronSurj.FLT

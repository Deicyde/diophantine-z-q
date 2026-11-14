/-
Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : Theorems/Thm_Module_depth_quotient_eq_depth.lean
  Retrieved      : 2026-11-14 (raw.githubusercontent.com, byte-for-byte)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original.
The changes are mechanical only; no statement, hypothesis, definition or proof term was
altered, weakened or omitted:
  * 3 internal `import`s retargeted to `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil`.
  * 1 `p2m_*` command(s) renamed to `w03_*`.
  * 1 `_root_.` reference(s) to source-specific namespaces qualified with `ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * one `w03_open "IsLocalRing"` inserted after the port namespace: this file `open`s `IsLocalRing`, which the port also declares as nested namespace(s), so a
    plain `open` would resolve to the nested one and hide Mathlib's. The dual root+prefix
    shim keeps the Mathlib root namespace(s) visible, exactly as in the original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_Patching_SystemTypes
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.P2M.Sol.S_Module_depth_quotient_eq_depth

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

w03_open "IsLocalRing"

open IsLocalRing RingTheory
theorem Module.depth_quotient_eq_depth
    {R : Type*} [CommRing R] [IsLocalRing R] (I : Ideal R) [IsLocalRing (R ⧸ I)]
    (N : Type*) [AddCommGroup N] [Module R N] [Module (R ⧸ I) N] [IsScalarTower R (R ⧸ I) N] :
    Module.depth (R ⧸ I) N = Module.depth R N := by w03_exact_reverting @_root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_Module_depth_quotient_eq_depth.solution

end ZInQ.Contrib.CloudW03NeronSurj.FLT

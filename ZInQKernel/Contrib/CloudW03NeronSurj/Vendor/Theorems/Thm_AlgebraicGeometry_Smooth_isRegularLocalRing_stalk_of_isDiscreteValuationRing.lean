/-
Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : Theorems/Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk_of_isDiscreteValuationRing.lean
  Retrieved      : 2026-11-14 (raw.githubusercontent.com, byte-for-byte)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original.
The changes are mechanical only; no statement, hypothesis, definition or proof term was
altered, weakened or omitted:
  * 2 internal `import`s retargeted to `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil`.
  * 1 `attribute [-instance]/[-simp]` performance-guard line(s) removed.
  * 1 `p2m_*` command(s) renamed to `w03_*`.
  * 1 `_root_.` reference(s) to source-specific namespaces qualified with `ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * one `w03_open "AlgebraicGeometry"` inserted after the port namespace: this file `open`s `AlgebraicGeometry`, which the port also declares as nested namespace(s), so a
    plain `open` would resolve to the nested one and hide Mathlib's. The dual root+prefix
    shim keeps the Mathlib root namespace(s) visible, exactly as in the original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.P2M.Sol.S_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk_of_isDiscreteValuationRing

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

w03_open "AlgebraicGeometry"

universe u

open CategoryTheory AlgebraicGeometry
theorem AlgebraicGeometry.Smooth.isRegularLocalRing_stalk_of_isDiscreteValuationRing
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t] (x : T) :
    IsRegularLocalRing (T.presheaf.stalk x) := by w03_exact_reverting @_root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk_of_isDiscreteValuationRing.solution

end ZInQ.Contrib.CloudW03NeronSurj.FLT

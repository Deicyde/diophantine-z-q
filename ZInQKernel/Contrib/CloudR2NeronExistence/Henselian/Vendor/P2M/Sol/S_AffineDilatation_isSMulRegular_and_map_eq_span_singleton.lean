import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_AffineDilatation_isSMulRegular_and_map_eq_span_singleton.lean
Original Git blob: cc33d6bad99fb1f428290268039dd56c8d8a1610
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Normalized 1 named/adjacent namespace closers for Lean 4.35.
* Explicitly closed 2 scopes originally left open at EOF.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_RingTheory_AffineDilatation
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_AffineDilatation_isSMulRegular_and_map_eq_span_singleton
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace AffineDilatation
h77_bridge_namespace
h77_export "AffineDilatation" "Ring divElem algebraMap_mul_divElem"
namespace BasicProps
h77_bridge_namespace
h77_open "AffineDilatation"

open scoped nonZeroDivisors

variable {A : Type u} [CommRing A]

theorem isSMulRegular (I : Ideal A) (a : A) : IsSMulRegular (Ring I a) a := by
  intro x y hxy
  apply Subtype.ext
  have h : algebraMap A (Localization.Away a) a * (x : Localization.Away a) =
      algebraMap A (Localization.Away a) a * (y : Localization.Away a) := by
    have := congrArg (fun z : Ring I a => (z : Localization.Away a)) hxy
    simpa [Algebra.smul_def] using this
  exact (IsLocalization.Away.algebraMap_isUnit a).mul_left_cancel h

theorem algebraMap_mem_nonZeroDivisors (I : Ideal A) (a : A) :
    algebraMap A (Ring I a) a ∈ (Ring I a)⁰ := by
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  refine isSMulRegular I a (?_ : a • x = a • (0 : Ring I a))
  rw [Algebra.smul_def, Algebra.smul_def, mul_zero, mul_comm]
  exact hx

theorem map_eq_span (I : Ideal A) (a : A) (ha : a ∈ I) :
    I.map (algebraMap A (Ring I a)) = Ideal.span {algebraMap A (Ring I a) a} := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap, Ideal.mem_span_singleton']
    exact ⟨divElem I a g hg, by rw [mul_comm, algebraMap_mul_divElem]⟩
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_map_of_mem _ ha

end BasicProps
end AffineDilatation

theorem solution
    {A : Type u} [CommRing A] (I : Ideal A) (a : A) (ha : a ∈ I) :
    IsSMulRegular (AffineDilatation.Ring I a) a ∧
      I.map (algebraMap A (AffineDilatation.Ring I a)) =
        Ideal.span {algebraMap A (AffineDilatation.Ring I a) a} :=
  ⟨AffineDilatation.BasicProps.isSMulRegular I a, AffineDilatation.BasicProps.map_eq_span I a ha⟩


end P2MW.S_AffineDilatation_isSMulRegular_and_map_eq_span_singleton
end ZInQ.Contrib.CloudR2NeronExistence.Henselian

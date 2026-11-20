import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_AffineDilatation_finiteType_of_fg.lean
Original Git blob: caee59ded8d2625fb8fcd29828d8b3e288c469d9
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

namespace P2MW.S_AffineDilatation_finiteType_of_fg
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace AffineDilatation
h77_bridge_namespace
h77_export "AffineDilatation" "subalgebra Ring gen_subset"
namespace FiniteTypeProof
h77_bridge_namespace
h77_open "AffineDilatation"

variable {A : Type v} [CommRing A]

theorem fg_of_fg (I : Ideal A) (a : A) (hI : I.FG) : (subalgebra I a).FG := by
  classical
  obtain ⟨T, hT⟩ := hI
  let aa : Submonoid.powers a := ⟨a, Submonoid.mem_powers a⟩
  let f : A → Localization.Away a := fun g => IsLocalization.mk' (Localization.Away a) g aa
  refine ⟨T.image f, le_antisymm ?_ ?_⟩
  · apply Algebra.adjoin_le
    intro x hx
    rw [Finset.coe_image] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    exact gen_subset I a ⟨g, hT ▸ Ideal.subset_span hg, rfl⟩
  · apply Algebra.adjoin_le
    rintro x ⟨g, hg, rfl⟩
    have hg' : g ∈ Ideal.span (T : Set A) := hT ▸ hg
    clear hg
    change f g ∈ Algebra.adjoin A (↑(T.image f) : Set (Localization.Away a))
    have hu : ∀ g : A, f g = algebraMap A (Localization.Away a) g * f 1 := fun g =>
      IsLocalization.mk'_eq_mul_mk'_one g aa
    rw [hu]
    induction hg' using Submodule.span_induction with
    | mem t ht =>
        rw [← hu]
        exact Algebra.subset_adjoin (by rw [Finset.coe_image]; exact ⟨t, ht, rfl⟩)
    | zero => rw [map_zero, zero_mul]; exact Subalgebra.zero_mem _
    | add x y _ _ hx hy => rw [map_add, add_mul]; exact Subalgebra.add_mem _ hx hy
    | smul c x _ hx =>
        rw [smul_eq_mul, map_mul, mul_assoc]
        exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ c) hx

theorem finiteType (I : Ideal A) (a : A) (hI : I.FG) : Algebra.FiniteType A (Ring I a) :=
  (Subalgebra.fg_iff_finiteType _).mp (fg_of_fg I a hI)

end FiniteTypeProof
end AffineDilatation

theorem solution
    {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (I : Ideal A) (a : A) (hI : I.FG) :
    Algebra.FiniteType R (AffineDilatation.Ring I a) :=
  Algebra.FiniteType.trans (S := A) inferInstance
    (AffineDilatation.FiniteTypeProof.finiteType I a hI)


end P2MW.S_AffineDilatation_finiteType_of_fg
end ZInQ.Contrib.CloudR2NeronExistence.Henselian

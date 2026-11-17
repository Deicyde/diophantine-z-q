import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_AffineDilatation_mem_subalgebra_iff_exists_mem_pow.lean
Original Git blob: c12387a81e3ffa3e09faa8daddb1f2816dffbf14
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

namespace P2MW.S_AffineDilatation_mem_subalgebra_iff_exists_mem_pow
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace AffineDilatation
h77_bridge_namespace
h77_export "AffineDilatation" "subalgebra gen_subset"
namespace PowDescription
h77_bridge_namespace
h77_open "AffineDilatation"

variable {A : Type u} [CommRing A]

def den (a : A) (n : ℕ) : Submonoid.powers a := ⟨a ^ n, n, rfl⟩

@[scoped simp] theorem coe_den (a : A) (n : ℕ) : ((den a n : Submonoid.powers a) : A) = a ^ n := rfl

theorem den_add (a : A) (m n : ℕ) : den a (m + n) = den a m * den a n :=
  Subtype.ext (pow_add a m n)

theorem den_zero (a : A) : den a 0 = 1 := Subtype.ext (pow_zero a)

theorem den_one (a : A) : den a 1 = ⟨a, Submonoid.mem_powers a⟩ := Subtype.ext (pow_one a)

noncomputable def frac (a : A) (n : ℕ) (g : A) : Localization.Away a :=
  IsLocalization.mk' (Localization.Away a) g (den a n)

theorem frac_zero_right (a : A) (g : A) : frac a 0 g = algebraMap A (Localization.Away a) g := by
  rw [frac, den_zero, IsLocalization.mk'_one]

theorem frac_eq_mul (a : A) (n : ℕ) (g : A) :
    frac a n g = algebraMap A (Localization.Away a) g * frac a n 1 :=
  IsLocalization.mk'_eq_mul_mk'_one g (den a n)

theorem frac_add_num (a : A) (n : ℕ) (g h : A) :
    frac a n (g + h) = frac a n g + frac a n h := by
  rw [frac_eq_mul, map_add, add_mul, ← frac_eq_mul, ← frac_eq_mul]

theorem frac_add (a : A) (m n : ℕ) (g h : A) :
    frac a m g + frac a n h = frac a (m + n) (g * a ^ n + h * a ^ m) := by
  rw [frac, frac, frac, ← IsLocalization.mk'_add, den_add]
  rfl

theorem frac_mul (a : A) (m n : ℕ) (g h : A) :
    frac a m g * frac a n h = frac a (m + n) (g * h) := by
  rw [frac, frac, frac, ← IsLocalization.mk'_mul, den_add]

theorem frac_mem_of_mem_pow (I : Ideal A) (a : A) :
    ∀ (n : ℕ) (g : A), g ∈ I ^ n → frac a n g ∈ subalgebra I a := by
  intro n
  induction n with
  | zero =>
      intro g _
      rw [frac_zero_right]
      exact Subalgebra.algebraMap_mem _ g
  | succ n ih =>
      intro g hg
      rw [pow_succ] at hg
      refine Submodule.mul_induction_on hg ?_ ?_
      · intro x hx y hy
        rw [← frac_mul]
        refine Subalgebra.mul_mem _ (ih x hx) ?_
        rw [frac, den_one]
        exact gen_subset I a ⟨y, hy, rfl⟩
      · intro x y hx hy
        rw [frac_add_num]
        exact Subalgebra.add_mem _ hx hy

theorem exists_pow_of_mem (I : Ideal A) (a : A) (ha : a ∈ I) (x : Localization.Away a)
    (hx : x ∈ subalgebra I a) : ∃ n : ℕ, ∃ g ∈ I ^ n, frac a n g = x := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨g, hg, rfl⟩ := hx
      refine ⟨1, g, by simpa using hg, ?_⟩
      rw [frac, den_one]
  | algebraMap r =>
      exact ⟨0, r, by simp, frac_zero_right a r⟩
  | add x y _ _ ihx ihy =>
      obtain ⟨m, g, hg, rfl⟩ := ihx
      obtain ⟨n, h, hh, rfl⟩ := ihy
      refine ⟨m + n, g * a ^ n + h * a ^ m, ?_, (frac_add a m n g h).symm⟩
      refine Ideal.add_mem _ ?_ ?_
      · rw [pow_add]; exact Ideal.mul_mem_mul hg (Ideal.pow_mem_pow ha n)
      · rw [add_comm, pow_add]; exact Ideal.mul_mem_mul hh (Ideal.pow_mem_pow ha m)
  | mul x y _ _ ihx ihy =>
      obtain ⟨m, g, hg, rfl⟩ := ihx
      obtain ⟨n, h, hh, rfl⟩ := ihy
      refine ⟨m + n, g * h, ?_, (frac_mul a m n g h).symm⟩
      rw [pow_add]; exact Ideal.mul_mem_mul hg hh

end PowDescription
end AffineDilatation
h77_reactivate "P2MW.S_AffineDilatation_mem_subalgebra_iff_exists_mem_pow.AffineDilatation P2MW.S_AffineDilatation_mem_subalgebra_iff_exists_mem_pow.AffineDilatation.PowDescription"
h77_reactivate "P2MW.S_AffineDilatation_mem_subalgebra_iff_exists_mem_pow.AffineDilatation"

theorem solution
    {A : Type u} [CommRing A] (I : Ideal A) (a : A) (ha : a ∈ I) (x : Localization.Away a) :
    x ∈ AffineDilatation.subalgebra I a ↔
      ∃ (n : ℕ) (g : A), g ∈ I ^ n ∧
        IsLocalization.mk' (Localization.Away a) g (⟨a ^ n, n, rfl⟩ : Submonoid.powers a) = x :=
  ⟨fun hx => by
    obtain ⟨n, g, hg, hgx⟩ := AffineDilatation.PowDescription.exists_pow_of_mem I a ha x hx
    exact ⟨n, g, hg, hgx⟩,
   fun ⟨n, g, hg, hx⟩ => hx ▸ AffineDilatation.PowDescription.frac_mem_of_mem_pow I a n g hg⟩


end P2MW.S_AffineDilatation_mem_subalgebra_iff_exists_mem_pow
end ZInQ.Contrib.CloudR2NeronExistence.Henselian

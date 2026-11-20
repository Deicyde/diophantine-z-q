import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Definitions/Def_RingTheory_AffineDilatation.lean
Original Git blob: 324d75a1c4a4d728718e47aaf0f6e9104ccdddaf
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import Mathlib

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

namespace AffineDilatation
h77_bridge_namespace

variable {A : Type u} [CommRing A]

def gen (I : Ideal A) (a : A) : Set (Localization.Away a) :=
  (fun g : A => IsLocalization.mk' (Localization.Away a) g
    (⟨a, Submonoid.mem_powers a⟩ : Submonoid.powers a)) '' (I : Set A)

def subalgebra (I : Ideal A) (a : A) : Subalgebra A (Localization.Away a) :=
  Algebra.adjoin A (gen I a)

abbrev Ring (I : Ideal A) (a : A) : Type u :=
  ↥(subalgebra I a)

def divElem (I : Ideal A) (a : A) (g : A) (hg : g ∈ I) : Ring I a :=
  ⟨IsLocalization.mk' (Localization.Away a) g (⟨a, Submonoid.mem_powers a⟩ : Submonoid.powers a),
    Algebra.subset_adjoin ⟨g, hg, rfl⟩⟩

@[simp]
theorem coe_divElem (I : Ideal A) (a : A) (g : A) (hg : g ∈ I) :
    ((divElem I a g hg : Ring I a) : Localization.Away a) =
      IsLocalization.mk' (Localization.Away a) g
        (⟨a, Submonoid.mem_powers a⟩ : Submonoid.powers a) :=
  rfl

theorem coe_algebraMap (I : Ideal A) (a : A) (g : A) :
    ((algebraMap A (Ring I a) g : Ring I a) : Localization.Away a) =
      algebraMap A (Localization.Away a) g :=
  rfl

theorem algebraMap_mul_divElem (I : Ideal A) (a : A) (g : A) (hg : g ∈ I) :
    algebraMap A (Ring I a) a * divElem I a g hg = algebraMap A (Ring I a) g := by
  apply Subtype.ext
  change algebraMap A (Localization.Away a) a *
      IsLocalization.mk' (Localization.Away a) g
        (⟨a, Submonoid.mem_powers a⟩ : Submonoid.powers a) =
    algebraMap A (Localization.Away a) g
  rw [mul_comm]
  exact IsLocalization.mk'_spec (Localization.Away a) g
    (⟨a, Submonoid.mem_powers a⟩ : Submonoid.powers a)

theorem mem_gen_iff (I : Ideal A) (a : A) (x : Localization.Away a) :
    x ∈ gen I a ↔ ∃ g ∈ I, IsLocalization.mk' (Localization.Away a) g
      (⟨a, Submonoid.mem_powers a⟩ : Submonoid.powers a) = x :=
  Iff.rfl

theorem subalgebra_eq_adjoin (I : Ideal A) (a : A) :
    subalgebra I a = Algebra.adjoin A (gen I a) :=
  rfl

theorem gen_subset (I : Ideal A) (a : A) :
    gen I a ⊆ (subalgebra I a : Set (Localization.Away a)) :=
  Algebra.subset_adjoin

theorem divElem_mem (I : Ideal A) (a : A) (g : A) (hg : g ∈ I) :
    ((divElem I a g hg : Ring I a) : Localization.Away a) ∈ gen I a :=
  ⟨g, hg, rfl⟩

end AffineDilatation

end


end ZInQ.Contrib.CloudR2NeronExistence.Henselian

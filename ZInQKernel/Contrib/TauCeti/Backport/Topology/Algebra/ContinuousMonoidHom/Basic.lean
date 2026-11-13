/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 97a5b23586f9, module
-- TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic), Apache-2.0: declarations added to that module after commit 5a01f5fe, whose
-- version is vendored as `ZInQKernel.Contrib.TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic`.
module

public import ZInQKernel.Contrib.TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Analysis.Complex.Basic
public import ZInQKernel.Contrib.TauCeti.Topology.Algebra.Group.Units
public import ZInQKernel.Contrib.TauCeti.GroupTheory.GroupAction.FixedPoints
public import ZInQKernel.Contrib.TauCeti.GroupTheory.OrderOfElement.Basic
import Mathlib.RingTheory.RootsOfUnity.Basic

public section

section
namespace ContinuousMonoidHom

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- The restriction of a continuous homomorphism `f : H → G` to the preimage of a subgroup `U`,
both carrying the subspace topology, as a continuous homomorphism `f⁻¹(U) → U`: the continuous
form of `MonoidHom.subgroupComap`. -/
def subgroupComap {H : Type*} [Group H] [TopologicalSpace H] (f : H →ₜ* G)
    (U : Subgroup G) : U.comap (f : H →* G) →ₜ* U where
  toMonoidHom := (f : H →* G).subgroupComap U
  continuous_toFun := (f.continuous.comp continuous_subtype_val).subtype_mk _

end ContinuousMonoidHom
end

section
namespace ContinuousMonoidHom

variable {G : Type*} [Group G] [TopologicalSpace G]

@[simp]
theorem subgroupComap_apply_coe {H : Type*} [Group H] [TopologicalSpace H] (f : H →ₜ* G)
    (U : Subgroup G) (x : U.comap (f : H →* G)) : (f.subgroupComap U x : G) = f x :=
  (rfl)

end ContinuousMonoidHom
end

section
namespace ContinuousMonoidHom

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- An element of `f⁻¹(U)` acts through `f.subgroupComap U` as its image under `f`. -/
theorem subgroupComap_smul {H : Type*} [Group H] [TopologicalSpace H] (f : H →ₜ* G)
    (U : Subgroup G) {α : Type*} [SMul G α] (x : U.comap (f : H →* G)) (a : α) :
    f.subgroupComap U x • a = f x • a :=
  (rfl)

end ContinuousMonoidHom
end

end

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 97a5b23586f9, module
-- TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Mackey.Basic), Apache-2.0: declarations added to that module after commit 5a01f5fe, whose
-- version is vendored as `ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Mackey.Basic`.
module

public import ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Mackey.Basic
public import ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Basic
public import ZInQKernel.Contrib.TauCeti.RepresentationTheory.Induction.Mackey.Basic

public section

open scoped Pointwise
namespace TauCeti.ContCohomology

universe u v
variable (G : Type u) [Group G] (M : Type v) [AddCommGroup M] [DistribMulAction G M]
  (U V : Subgroup G)
variable [U.FiniteIndex]
attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex
variable (r : DoubleCoset.Quotient (V : Set G) (U : Set G) → G)
  (hr : ∀ D, DoubleCoset.mk V U (r D) = D)
variable [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul G M]
  (hU : IsOpen (U : Set G))

/-- The degree-two Mackey summand is the corestriction from the Mackey subgroup of the pullback
along conjugation by `s`. -/
theorem explicitMackeyTerm2_apply (s : G) (x : H2 U M) :
    explicitMackeyTerm2 G M U V hU s x =
      explicitCor2 V M ((mackeySubgroup s U V).subgroupOf V)
        (U.isOpen_mackeySubgroup_subgroupOf V hU s)
        (explicitMap2 U M ((mackeySubgroup s U V).subgroupOf V) M (U.continuousMackeyToH V s)
          (DistribSMul.toAddMonoidHom M s) ((continuous_const_smul s).congr fun _ => rfl)
          (smul_continuousMackeyToH_smul G M U V s) x) :=
  (rfl)

end TauCeti.ContCohomology

end

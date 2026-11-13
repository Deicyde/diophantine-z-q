/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 97a5b23586f9, module
-- TauCeti.NumberTheory.ClassFieldTheory.GlobalExistence.NormSubgroup), Apache-2.0: declarations added to that module after commit 5a01f5fe
-- and not already in `ZInQKernel.Contrib.TauCeti.Backport.NumberTheory.ClassFieldTheory.GlobalExistence.NormSubgroup`
-- (task ring-class).
module

public import ZInQKernel.Contrib.TauCeti.Backport.NumberTheory.ClassFieldTheory.GlobalExistence.NormSubgroup

public noncomputable section

open IntermediateField NumberField

namespace TauCeti.ClassFieldTheory

variable (K : Type) [Field K] [NumberField K]
variable {K}

variable (K) in
/-- The global norm subgroup of `V` is normal in the commutative group `C_K`, so the norm quotient
`C_K / N_{E/K}(C_E)` is a group. -/
instance normal_globalNormSubgroup (V : OpenNormalSubgroup (AbsoluteGaloisGroup K)) :
    (globalNormSubgroup K V).Normal := by
  rw [globalNormSubgroup_eq_range_classField]
  infer_instance

variable (K) in
/-- The ground-level order isomorphism preserves the index of every idele-class subgroup. -/
theorem index_globalGroundOrderIso (N : Subgroup (IdeleClassGroup (𝓞 K) K)) :
    (globalGroundOrderIso K N).toAddSubgroup.index = N.index := by
  have : (globalGroundOrderIso K N).toAddSubgroup =
      N.toAddSubgroup.comap (globalGroundEquiv K).symm.toAddMonoidHom := by
    ext a
    exact mem_globalGroundOrderIso
  rw [this, ← Subgroup.index_toAddSubgroup]
  exact AddSubgroup.index_comap_of_surjective _ (globalGroundEquiv K).symm.surjective


end TauCeti.ClassFieldTheory

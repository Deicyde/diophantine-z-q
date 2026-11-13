/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 97a5b23586f9, module
-- TauCeti.NumberTheory.ClassFieldTheory.GlobalExistence.NormSubgroup), Apache-2.0: declarations added to that module after commit 5a01f5fe, whose
-- version is vendored as `ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.GlobalExistence.NormSubgroup`.
module

public import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.GlobalExistence.NormSubgroup
public import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Formation.NormLimitation
public import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.ClassField
public import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Formation.Refinement
public import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Global.IdeleClass.Norm
public import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Open

public noncomputable section

open IntermediateField NumberField
namespace TauCeti.ClassFieldTheory

variable (K : Type) [Field K] [NumberField K]
local notation "Ω" => FiniteGaloisIntermediateField K (SeparableClosure K)
variable {K}

variable (K) in
/-- **Subgroups of `C_K` are the subgroups of the ground level of the idele-class formation.** The
level of the whole group `G_K` is `C_K`, written additively (`globalGroundEquiv`), so taking
preimages along that identification is an order isomorphism. It carries the global norm subgroups
to the norm subgroups of the idele-class formation (`globalGroundOrderIso_globalNormSubgroup`),
which transports the laws of the norm subgroups of a class formation to `C_K`. -/
def globalGroundOrderIso :
    Subgroup (IdeleClassGroup (𝓞 K) K) ≃o Submodule ℤ ((globalFormation K).level ⊤) :=
  Subgroup.toAddSubgroup.trans <|
    (globalGroundEquiv K).symm.comapAddSubgroup.trans AddSubgroup.toIntSubmodule

end TauCeti.ClassFieldTheory

open IntermediateField NumberField
namespace TauCeti.ClassFieldTheory

variable (K : Type) [Field K] [NumberField K]
local notation "Ω" => FiniteGaloisIntermediateField K (SeparableClosure K)
variable {K}

/-- An element of the ground level lies in the image of a subgroup `H ≤ C_K` under
`globalGroundOrderIso` exactly when the corresponding idele class lies in `H`. -/
@[simp]
theorem mem_globalGroundOrderIso {H : Subgroup (IdeleClassGroup (𝓞 K) K)}
    {a : (globalFormation K).level ⊤} :
    a ∈ globalGroundOrderIso K H ↔ ((globalGroundEquiv K).symm a).toMul ∈ H :=
  Iff.rfl

end TauCeti.ClassFieldTheory

open IntermediateField NumberField
namespace TauCeti.ClassFieldTheory

variable (K : Type) [Field K] [NumberField K]
local notation "Ω" => FiniteGaloisIntermediateField K (SeparableClosure K)
variable {K}

variable (K) in
/-- `globalGroundOrderIso` carries the global norm subgroup of `V` to the norm subgroup of the
layer `V ◁ G_K` of the idele-class formation. -/
@[simp]
theorem globalGroundOrderIso_globalNormSubgroup (V : OpenNormalSubgroup (AbsoluteGaloisGroup K)) :
    globalGroundOrderIso K (globalNormSubgroup K V) = (globalFormation K).normSubgroup V := by
  ext a
  obtain ⟨c, rfl⟩ : ∃ c, globalGroundEquiv K c = a := (globalGroundEquiv K).surjective a
  rw [mem_globalGroundOrderIso, AddEquiv.symm_apply_apply, mem_globalNormSubgroup_iff, ofMul_toMul,
    Formation.mem_normSubgroup]

end TauCeti.ClassFieldTheory

end

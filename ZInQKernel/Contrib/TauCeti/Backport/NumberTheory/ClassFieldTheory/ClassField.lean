/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 97a5b23586f9, module
-- TauCeti.NumberTheory.ClassFieldTheory.ClassField), Apache-2.0: declarations added to that module after commit 5a01f5fe
-- (task ring-class).
-- Modified for the Z-in-Q kernel: the proof of `classField_fixingOpenNormalSubgroup` compares fixing subgroups (`classField` does not unfold outside its module).
module

public import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.ClassField

public noncomputable section

namespace TauCeti.ClassFieldTheory

open IntermediateField

section Basic

variable {F : Type*} [Field F]

/-- **The class field of the subgroup fixing a finite Galois extension `L/F` is `L`**, embedded in
`Fˢ` by any `F`-embedding `ι`. -/
theorem classField_fixingOpenNormalSubgroup {L : Type*} [Field L] [Algebra F L]
    [FiniteDimensional F L] [IsGalois F L] (ι : L →ₐ[F] SeparableClosure F) :
    classField F (fixingOpenNormalSubgroup F L) = ι.fieldRange := by
  -- Modified for the Z-in-Q kernel: `classField` does not unfold outside its module; the proof
  -- compares fixing subgroups instead.
  have : IsGalois F ι.fieldRange := IsGalois.of_algEquiv (AlgEquiv.ofInjectiveField ι)
  have h1 : (classField F (fixingOpenNormalSubgroup F L)).fixingSubgroup =
      ι.fieldRange.fixingSubgroup := by
    rw [fixingSubgroup_classField, fixingOpenNormalSubgroup_toSubgroup ι]
  rw [← InfiniteGalois.fixedField_fixingSubgroup (classField F (fixingOpenNormalSubgroup F L)), h1,
    InfiniteGalois.fixedField_fixingSubgroup]

end Basic

section Layer

variable {F : Type} [Field F]

/-- The open normal subgroup of `G_F` fixing a finite abelian extension `L/F` is an abelian
layer. -/
theorem isAbelianClassFieldLayer_fixingOpenNormalSubgroup {L : Type*} [Field L] [Algebra F L]
    [FiniteDimensional F L] [IsAbelianGalois F L] :
    (fixingOpenNormalSubgroup F L).IsAbelianClassFieldLayer := by
  let ι : L →ₐ[F] SeparableClosure F := IsSepClosed.lift
  have : IsAbelianGalois F ι.fieldRange := .of_algHom (AlgEquiv.ofInjectiveField ι).symm.toAlgHom
  rw [← isAbelianGalois_classField_iff, classField_fixingOpenNormalSubgroup ι]
  infer_instance

end Layer

end TauCeti.ClassFieldTheory

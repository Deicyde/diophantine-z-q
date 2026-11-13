/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 97a5b23586f9, module
-- TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Relative), Apache-2.0: declarations added to that module after commit 5a01f5fe, whose
-- version is vendored as `ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Relative`.
module

public import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Relative
public import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.Adeles.Norm.Continuity
public import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.Ideles.Extension
public import ZInQKernel.Contrib.TauCeti.RingTheory.Norm.Units
public import ZInQKernel.Contrib.TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic
public import ZInQKernel.Contrib.TauCeti.Backport.Topology.Algebra.ContinuousMonoidHom.Basic
import ZInQKernel.Contrib.TauCeti.GroupTheory.QuotientGroup.Index

public section
noncomputable section

open IsDedekindDomain NumberField NumberField.InfinitePlace
open scoped AdicCompletionExtension NumberField.LiesOver
namespace TauCeti.GlobalNumberFields

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

variable {K L} in
/-- **A larger extension has a smaller idele-class norm group**: if `f : L →ₐ[K] M`, then
`N_{M/K}(C_M) ≤ N_{L/K}(C_L)`. Through `f`, `M` is an extension of `L`, and
`N_{M/K} = N_{L/K} ∘ N_{M/L}`. -/
theorem range_ideleClassNormMap_le_of_algHom {M : Type*} [Field M] [NumberField M]
    [Algebra K M] (f : L →ₐ[K] M) :
    (ideleClassNormMap K M : IdeleClassGroup (𝓞 M) M →* IdeleClassGroup (𝓞 K) K).range ≤
      (ideleClassNormMap K L : IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 K) K).range := by
  let _ : Algebra L M := f.toRingHom.toAlgebra
  have : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq fun x ↦ (f.commutes x).symm
  rintro _ ⟨y, rfl⟩
  exact ⟨ideleClassNormMap L M y, DFunLike.congr_fun (ideleClassNormMap_comp K L M) y⟩

end TauCeti.GlobalNumberFields

end
end

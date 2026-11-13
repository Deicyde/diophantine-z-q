/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 97a5b23586f9, module
-- TauCeti.FieldTheory.Galois.Restriction), Apache-2.0: declarations added to that module after commit 5a01f5fe, whose
-- version is vendored as `ZInQKernel.Contrib.TauCeti.FieldTheory.Galois.Restriction`.
module

public import ZInQKernel.Contrib.TauCeti.FieldTheory.Galois.Restriction
public import Mathlib.FieldTheory.Galois.Basic

public section

section
namespace TauCeti

variable {F K M : Type*} [Field F] [Field K] [Field M] [Algebra F K] [Algebra F M]

/-- **Restriction is transitive along composed embeddings**: restricting `σ` along `f : M → K`
and then along `h : N → M` is restricting `σ` along `f ∘ h`. -/
@[simp]
theorem _root_.AlgHom.restrictNormalHom_restrictNormalHom {N : Type*} [Field N] [Algebra F N]
    (f : M →ₐ[F] K) (h : N →ₐ[F] M) [Normal F M] [Normal F N] (σ : Gal(K/F)) :
    h.restrictNormalHom (f.restrictNormalHom σ) = (f.comp h).restrictNormalHom σ :=
  ((f.comp h).restrictNormalHom_eq_iff.2 fun x ↦ by
    rw [AlgHom.comp_apply, AlgHom.comp_apply, h.restrictNormalHom_commutes,
      f.restrictNormalHom_commutes]).symm

end TauCeti
end

end

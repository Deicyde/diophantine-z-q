/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 97a5b23586f9, module
-- TauCeti.FieldTheory.Galois.Abelian.Basic), Apache-2.0: declarations added to that module after commit 5a01f5fe, whose
-- version is vendored as `ZInQKernel.Contrib.TauCeti.FieldTheory.Galois.Abelian.Basic`.
module

public import ZInQKernel.Contrib.TauCeti.FieldTheory.Galois.Abelian.Basic

public section

namespace TauCeti

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]

omit [IsGalois K L] in
open scoped IsMulCommutative in
/-- **The automorphisms of an abelian Galois extension commute.** This is the explicit
commutativity hypothesis taken by constructions on a general Galois group, such as the
ideal-theoretic Artin map, obtained from an `IsAbelianGalois` instance. -/
theorem algEquiv_commute_of_isAbelianGalois [IsAbelianGalois K L] :
    ∀ σ τ : L ≃ₐ[K] L, Commute σ τ :=
  Commute.all

end TauCeti

end

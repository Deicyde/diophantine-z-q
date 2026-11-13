/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 97a5b23586f9, module
-- TauCeti.RingTheory.Polynomial.Cyclotomic.Basic), Apache-2.0: declarations added to that module after commit 5a01f5fe, whose
-- version is vendored as `ZInQKernel.Contrib.TauCeti.RingTheory.Polynomial.Cyclotomic.Basic`.
module

public import ZInQKernel.Contrib.TauCeti.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

public section

section
namespace Polynomial

variable {R : Type*} [Ring R]

/-- `Φ_n(X + 1)` is monic. -/
theorem monic_cyclotomic_comp_X_add_one (n : ℕ) : ((cyclotomic n R).comp (X + 1)).Monic := by
  simpa using (cyclotomic.monic n R).comp_X_add_C 1

end Polynomial
end

end

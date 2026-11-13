/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 97a5b23586f9, module
-- TauCeti.GroupTheory.Abelianization.Basic), Apache-2.0: declarations added to that module after commit 5a01f5fe, whose
-- version is vendored as `ZInQKernel.Contrib.TauCeti.GroupTheory.Abelianization.Basic`.
module

public import ZInQKernel.Contrib.TauCeti.GroupTheory.Abelianization.Basic

public section

namespace Abelianization

variable {G : Type*} [Group G]

/-- The abelianization map of a commutative group is injective. -/
theorem of_injective [IsMulCommutative G] : Function.Injective (of (G := G)) :=
  (MonoidHom.ker_eq_bot_iff _).1 (by rw [ker_of, commutator_eq_bot])

end Abelianization

end

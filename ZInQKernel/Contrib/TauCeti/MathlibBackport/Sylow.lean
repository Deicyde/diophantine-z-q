/-
Released under Apache 2.0 license. Backport of a Mathlib declaration (Mathlib, Apache 2.0, The
Mathlib contributors), needed by the vendored Tau Ceti code (Apache 2.0, The Tau Ceti
contributors). Added by the Z-in-Q tc-port task.
-/
module

public import Mathlib.GroupTheory.Sylow

/-!
# Backport: `Sylow.maximal_isPGroup`

Mathlib PR #44454 ("spell `Sylow` using `Maximal`", after our pin 56a00585) replaced the fields
`isPGroup'` and `is_maximal'` of `Sylow` by a single field `maximal_isPGroup`. Tau Ceti (commit
5a01f5fe) uses that field. This file provides it, with the same name and statement, as a theorem
derived from the two fields present at our pin. Local addition of the Z-in-Q tc-port task.
-/

public section

namespace Sylow

variable {p : ℕ} {G : Type*} [Group G]

/-- A Sylow `p`-subgroup is a maximal `p`-subgroup. -/
theorem maximal_isPGroup (P : Sylow p G) : Maximal (fun Q : Subgroup G ↦ IsPGroup p Q) (P : Subgroup G) :=
  ⟨P.isPGroup', fun _ hQ hle => (P.is_maximal' hQ hle).le⟩

end Sylow

module

public import Mathlib.GroupTheory.Sylow

/-!
# Backport: `Sylow.maximal_isPGroup`

Mathlib PR #44454 ("spell `Sylow` using `Maximal`", after our pin 56a00585) replaced the fields
`isPGroup'` and `is_maximal'` of `Sylow` by a single field `maximal_isPGroup`. Tau Ceti (commit
5a01f5fe) uses that field. This file provides it, with the same name and statement, as a theorem
derived from the two fields present at our pin.

This file is original to the Z-in-Q project (added by its tc-port task); it is not copied from
Tau Ceti. Only the name and statement of `Sylow.maximal_isPGroup` follow Mathlib.
-/

public section

namespace Sylow

variable {p : ℕ} {G : Type*} [Group G]

/-- A Sylow `p`-subgroup is a maximal `p`-subgroup. -/
theorem maximal_isPGroup (P : Sylow p G) : Maximal (fun Q : Subgroup G ↦ IsPGroup p Q) (P : Subgroup G) :=
  ⟨P.isPGroup', fun _ hQ hle => (P.is_maximal' hQ hle).le⟩

end Sylow

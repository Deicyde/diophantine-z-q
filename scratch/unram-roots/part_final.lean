
/-! ## The result -/

namespace UnramRootsTask

variable {p : ℕ} [Fact p.Prime] {ℓ : ℕ} [Fact ℓ.Prime]

/-- **`UnramRoots` (local-glue's textbook Prop, verbatim) is a theorem (proved)**, from Mathlib and
the vendored Tau Ceti (`ZInQKernel/Contrib/TauCeti/`). -/
theorem unramRoots : G15Ram.UnramRoots p ℓ :=
  unramRoots_of_unramProcyclic
    (unramProcyclic_of_frobData fun F hF => by haveI := hF; exact frobData_exists F)

/-- The form used by local-glue (`tail_glue.lean`, `part_pack.lean`): every `p`, `ℓ`. -/
theorem unramRoots_all : ∀ (p : ℕ) [Fact p.Prime] (ℓ : ℕ) [Fact ℓ.Prime], G15Ram.UnramRoots p ℓ :=
  fun _ _ _ _ => unramRoots

/-- The form used at `p = 2` by local-glue (`hU2` in `tail_glue.lean`). -/
theorem unramRoots_two : ∀ (hp : Nat.Prime 2) (ℓ : ℕ) [Fact ℓ.Prime],
    @G15Ram.UnramRoots 2 ⟨hp⟩ ℓ _ :=
  fun hp _ _ => @unramRoots 2 ⟨hp⟩ _ _

end UnramRootsTask

#print axioms UnramRootsTask.unramRoots_all
#print axioms UnramRootsTask.unramRoots

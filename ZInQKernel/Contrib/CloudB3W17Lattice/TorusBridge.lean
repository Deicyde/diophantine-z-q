import ZInQKernel.HDecomp.Analytic.Torus
import ZInQKernel.Contrib.CloudB3W17Lattice.CompactQuotient

/-!
# The compact-quotient criterion on `BPAnalytic.Torus`

`BPAnalytic.Torus Λ` is `E ⧸ Λ.toAddSubgroup`, so `CloudB3W17Lattice.isZLattice_of_compactSpace_quotient`
applies to it verbatim. This file records the complex form used by the uniformization route and closes the
equivalence with the existing `BPAnalytic.compactSpace_torus` (which is the converse direction and is *not*
re-proved here).

* `CloudB3W17Lattice.isZLattice_of_compactSpace_torus` — discrete `Λ` with `Torus Λ` compact is a full lattice.
* `CloudB3W17Lattice.isZLattice_iff_compactSpace_torus` — the two directions together.
* `CloudB3W17Lattice.isZLattice_of_exp` — the shape a Mumford-style exponential supplies: a continuous, open,
  surjective homomorphism `π : E → X` onto a compact group, injective near `0`, has a discrete kernel which is a
  full lattice, and identifies `Torus (ker π) ≃ₜ+ X`.
-/

set_option linter.unusedSectionVars false

namespace CloudB3W17Lattice

open BPAnalytic Submodule

section Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- **Converse of `BPAnalytic.compactSpace_torus`.** A discrete `ℤ`-submodule of a finite-dimensional
complex normed space whose torus is compact is a full lattice. -/
theorem isZLattice_of_compactSpace_torus (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [CompactSpace (Torus Λ)] : IsZLattice ℝ Λ :=
  isZLattice_of_compactSpace_quotient Λ

/-- For a discrete `Λ`, being a full lattice is exactly compactness of `E ⧸ Λ`. -/
theorem isZLattice_iff_compactSpace_torus (Λ : Submodule ℤ E) [DiscreteTopology Λ] :
    IsZLattice ℝ Λ ↔ CompactSpace (Torus Λ) :=
  ⟨fun h => by have := h; exact compactSpace_torus Λ,
   fun h => by have := h; exact isZLattice_of_compactSpace_quotient Λ⟩

/-- **Exponential-kernel supplier.** If `π : E → X` is a continuous, open, surjective homomorphism onto a
compact group `X` and is injective on a neighbourhood of `0`, then its kernel `Λ` is a discrete full lattice
and `Torus Λ ≃ₜ+ X`. This is the lattice half of the classical "compact complex Lie group is a torus"
argument; the exponential `π` itself is not constructed here. -/
theorem isZLattice_of_exp {X : Type*} [TopologicalSpace X] [AddGroup X] [CompactSpace X]
    (Λ : Submodule ℤ E) (π : E →+ X) (hker : ∀ x, π x = 0 ↔ x ∈ Λ) (hcont : Continuous π)
    (hopen : IsOpenMap π) (hsurj : Function.Surjective π) {U : Set E} (hU : U ∈ nhds (0 : E))
    (hinj : Set.InjOn π U) :
    ∃ _ : DiscreteTopology Λ, IsZLattice ℝ Λ ∧ Nonempty ((Torus Λ) ≃ₜ+ X) := by
  have hd : DiscreteTopology Λ := discreteTopology_of_injOn Λ π hker hU hinj
  refine ⟨hd, ?_, ⟨quotientContinuousAddEquiv Λ π hker hcont hopen hsurj⟩⟩
  have := hd
  exact isZLattice_of_isOpenMap Λ π hker hcont hopen hsurj

end Complex

end CloudB3W17Lattice

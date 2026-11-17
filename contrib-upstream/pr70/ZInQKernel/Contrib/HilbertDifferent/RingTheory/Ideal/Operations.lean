/-
Ported with Codex assistance on 2026-11-14 from trureturing@8af78b5bb176c99b2750222c0dd3d00a475d39eb.
Source: D5/S3/Factorization/Dedekind/HilbertDifferent/RingTheory/Ideal/Operations.lean
Original SHA-256: 29069386ceb5665f2a35964e9648c9415b747381ed7ddba1c1f466ba973ab7e5
Changes: contribution import paths and namespace; retained proof content.
Full licenses and provenance: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
-/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/- Adapted to the repository-pinned Mathlib API; only declarations needed by the
Hilbert different consumer are retained. Source: TauCeti@33c2099c678ea391f7ea3e0ddaf945a76a625e5d,
TauCeti/RingTheory/Ideal/Operations.lean.
Full license and pertinent inherited attribution: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
Replace this port by direct use when this project's pinned Mathlib supplies an equivalent declaration. -/


import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Ring.Subgroup
import Mathlib.Algebra.Ring.Subring.Basic
import ZInQKernel.Contrib.HilbertDifferent.Support.TameDifferent

noncomputable section

section

open scoped Pointwise

namespace Ideal

variable {R : Type*} [Ring R] {I J : Ideal R} {S T : Set R}

/- If `S` and `T` additively generate the ideals `I` and `J`, then their pairwise products
additively generate `I * J`. -/
section Mul

variable {R : Type*} [CommSemiring R] {I J : Ideal R}

/- If two ideals multiply to the unit ideal, then the first ideal is the unit ideal. -/
end Mul

section Pi

variable {R : Type*} [Semiring R] {ι : Type*} {M : ι → Type*} [∀ i, AddCommMonoid (M i)]
    [∀ i, Module R (M i)]

/- **Expanding a product expands every factor**: if `I • ⊤ = ⊤` in `∀ i, M i` then `I • ⊤ = ⊤` in
each `M i`. Faithful flatness of a product is decided factorwise through this, since
`Module.FaithfullyFlat` is flatness together with `m • ⊤ ≠ ⊤` at every maximal ideal. -/
end Pi

end Ideal

namespace Ideal

section Span

variable {R : Type*} [CommSemiring R] {a : R} {S S' : Set R}

/- **Replacing one generating set by another**: if every element of `S` is either `a` itself or an
element of `S'`, then `S'` together with `a` generates the unit ideal as soon as `S` together with
`a` does. Note that `S'` need not be contained in `S`, and may be larger: the hypothesis constrains
only where the elements of `S` are found. Both spans contain `a`, so only the rest of `S` has to be
accounted for. -/
variable {A : Type*} [Semiring A] {s : Set A}

/- A left ideal spanned by central elements is two-sided. -/
end Span

end Ideal

universe u

/- For two-sided ideals, the `n`-th power of a supremum is contained in the first ideal
plus the `n`-th power of the second. -/
namespace Subalgebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/- If a subalgebra `T` meets every residue class of `S` modulo a principal ideal `I` and contains
a generator of `I`, then it meets every residue class modulo any power of `I`. -/
theorem toSubmodule_sup_pow_restrictScalars_eq_top {T : Subalgebra R S} {I : Ideal S} {π : S}
    (hπ : Ideal.span {π} = I) (hπT : π ∈ T)
    (h : T.toSubmodule ⊔ I.restrictScalars R = ⊤) (n : ℕ) :
    T.toSubmodule ⊔ (I ^ n).restrictScalars R = ⊤ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hpow : I ^ n = Ideal.span {π ^ n} := by
      rw [← hπ, Ideal.span_singleton_pow]
    refine eq_top_iff.mpr fun s _ => ?_
    obtain ⟨t, ht, m, hm, rfl⟩ := Submodule.mem_sup.mp (ih.ge Submodule.mem_top : s ∈ _)
    obtain ⟨u, rfl⟩ : ∃ u, m = π ^ n * u := by
      rw [Submodule.restrictScalars_mem, hpow, Ideal.mem_span_singleton] at hm
      exact hm
    obtain ⟨t', ht', m', hm', rfl⟩ := Submodule.mem_sup.mp (h.ge Submodule.mem_top : u ∈ _)
    refine Submodule.mem_sup.mpr ⟨t + π ^ n * t', ?_, π ^ n * m', ?_, by ring⟩
    · rw [Subalgebra.mem_toSubmodule] at ht ht' ⊢
      exact add_mem ht (mul_mem (pow_mem hπT n) ht')
    · rw [Submodule.restrictScalars_mem, pow_succ]
      exact Ideal.mul_mem_mul (hpow ▸ Ideal.mem_span_singleton_self _) hm'

end Subalgebra

end

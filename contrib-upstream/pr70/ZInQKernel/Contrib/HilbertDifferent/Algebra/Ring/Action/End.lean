/-
Ported with Codex assistance on 2026-11-14 from trureturing@8af78b5bb176c99b2750222c0dd3d00a475d39eb.
Source: D5/S3/Factorization/Dedekind/HilbertDifferent/Algebra/Ring/Action/End.lean
Original SHA-256: e71e1834de87e573972aeef29d481dd306ba80cba547c532318a22c7cb9d6259
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
TauCeti/Algebra/Ring/Action/End.lean.
Full license and pertinent inherited attribution: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
Replace this port by direct use when this project's pinned Mathlib supplies an equivalent declaration. -/


import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Ring.Action.End
import ZInQKernel.Contrib.HilbertDifferent.Support.TameDifferent

noncomputable section

section

namespace TauCeti.MulSemiringAction

variable {G : Type*} [Group G] {S : Type*} [Semiring S] [MulSemiringAction G S]

/- Membership in the kernel of the automorphism representation means acting trivially on every
element. -/
theorem mem_ker_toRingAut_iff {σ : G} :
    σ ∈ MonoidHom.ker (_root_.MulSemiringAction.toRingAut G S) ↔ ∀ x : S, σ • x = x := by
  simp [MonoidHom.mem_ker, RingEquiv.ext_iff]

/- A faithful action by ring automorphisms has trivial kernel. -/
theorem ker_toRingAut_eq_bot [FaithfulSMul G S] :
    MonoidHom.ker (_root_.MulSemiringAction.toRingAut G S) = ⊥ := by
  ext σ
  rw [mem_ker_toRingAut_iff, Subgroup.mem_bot]
  exact ⟨fun h ↦ eq_of_smul_eq_smul fun x : S ↦ by rw [h x, one_smul],
    fun h x ↦ by rw [h, one_smul]⟩

end TauCeti.MulSemiringAction

namespace TauCeti

variable {G : Type*} [Monoid G] {S : Type*} [Semiring S] [MulSemiringAction G S]
variable {R : Type*} [CommSemiring R] [Algebra R S] [SMulCommClass G R S]

/- For a faithful action by `R`-algebra maps on `S = R[ξ]`, an element fixing the generator `ξ`
is the identity. -/
theorem eq_one_of_smul_eq_of_adjoin_singleton_eq_top [FaithfulSMul G S] {ξ : S}
    (hξ : Algebra.adjoin R {ξ} = ⊤) {σ : G} (h : σ • ξ = ξ) : σ = 1 := by
  refine eq_of_smul_eq_smul fun x : S ↦ ?_
  have hx : x ∈ Algebra.adjoin R {ξ} := hξ ▸ Algebra.mem_top
  rw [one_smul]
  exact (Algebra.forall_mem_adjoin_smul_eq_self_iff {ξ} σ).2 (Set.forall_mem_singleton.2 h) x hx

end TauCeti

namespace TauCeti

variable {G : Type*} [Group G] {S : Type*} [Semiring S] [MulSemiringAction G S]
variable {R : Type*} [CommSemiring R] [Algebra R S] [SMulCommClass G R S]

/- For a faithful action by `R`-algebra maps on `S = R[ξ]`, the orbit map at `ξ` is injective. -/
end TauCeti

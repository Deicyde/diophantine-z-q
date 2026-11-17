/-
Ported with Codex assistance on 2026-11-14 from trureturing@8af78b5bb176c99b2750222c0dd3d00a475d39eb.
Source: D5/S3/Factorization/Dedekind/HilbertDifferent/RingTheory/Ideal/RamificationGroup.lean
Original SHA-256: e9e336f8ed4f4f25c1f82623914fa712fa15ad2022bb9afc031a20fa91724144
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
TauCeti/RingTheory/Ideal/RamificationGroup.lean.
Full license and pertinent inherited attribution: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
Replace this port by direct use when this project's pinned Mathlib supplies an equivalent declaration. -/


import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Ideal.Pointwise
import ZInQKernel.Contrib.HilbertDifferent.Algebra.Group.Subgroup.FiniteFiltration
import ZInQKernel.Contrib.HilbertDifferent.Algebra.Ring.Action.End
import ZInQKernel.Contrib.HilbertDifferent.Support.TameDifferent

noncomputable section

section

open scoped Pointwise

namespace Ideal

variable (G : Type*) [Group G] {B : Type*} [CommRing B] [MulSemiringAction G B]

/- The `i`-th **ramification group** of an ideal `Q` for a group `G` acting on the ring: the
elements of `G` acting trivially on `B ⧸ Q ^ (i + 1)`, that is, the inertia subgroup of
`Q ^ (i + 1)`. -/
def ramificationGroup (Q : Ideal B) (i : ℕ) : Subgroup G :=
  (Q ^ (i + 1)).inertia G

variable {G}

/- The ramification groups are the inertia subgroups of the powers of `Q`. -/
theorem ramificationGroup_def (Q : Ideal B) (i : ℕ) :
    Q.ramificationGroup G i = (Q ^ (i + 1)).inertia G :=
  -- `(rfl)`, not `rfl`: the body of `ramificationGroup` is not exposed.
  (rfl)

/- The defining membership criterion of the ramification groups. -/
@[simp]
theorem mem_ramificationGroup_iff {Q : Ideal B} {i : ℕ} {σ : G} :
    σ ∈ Q.ramificationGroup G i ↔ ∀ x : B, σ • x - x ∈ Q ^ (i + 1) := by
  rw [ramificationGroup_def, mem_inertia]

/- Restricting a ramification group to a subgroup `H` gives the ramification group for the action
of `H`. -/
@[simp]
theorem ramificationGroup_subgroupOf (Q : Ideal B) (i : ℕ) (H : Subgroup G) :
    (Q.ramificationGroup G i).subgroupOf H = Q.ramificationGroup H i := by
  ext σ
  simp only [Subgroup.mem_subgroupOf, mem_ramificationGroup_iff, Subgroup.smul_def]

/- The zeroth ramification group is the inertia group. -/
@[simp]
theorem ramificationGroup_zero (Q : Ideal B) : Q.ramificationGroup G 0 = Q.inertia G := by
  rw [ramificationGroup_def, zero_add, pow_one]

variable (G) in
/- The ramification groups decrease. -/
theorem ramificationGroup_antitone (Q : Ideal B) : Antitone (Q.ramificationGroup G) :=
  fun _ _ hij _ hσ ↦ mem_ramificationGroup_iff.2 fun x ↦
    Ideal.pow_le_pow_right (by omega) (mem_ramificationGroup_iff.1 hσ x)

/- Every ramification group lies in the inertia group. -/
theorem ramificationGroup_le_inertia (Q : Ideal B) (i : ℕ) :
    Q.ramificationGroup G i ≤ Q.inertia G :=
  ramificationGroup_zero (G := G) Q ▸ ramificationGroup_antitone G Q (Nat.zero_le i)

/- Every ramification group lies in the decomposition group, the stabilizer of `Q`. -/
theorem ramificationGroup_le_stabilizer (Q : Ideal B) (i : ℕ) :
    Q.ramificationGroup G i ≤ MulAction.stabilizer G Q :=
  (ramificationGroup_le_inertia Q i).trans (inertia_le_stabilizer Q)

/- Moving the ideal by `g` conjugates its ramification groups by `g`. -/
section Noetherian

variable [IsNoetherianRing B] [IsDomain B]

/- Over a Noetherian domain, the ramification groups of a proper ideal intersect in the kernel
of the action: an element acting trivially modulo every power of `Q` acts trivially, by the Krull
intersection theorem. -/
theorem iInf_ramificationGroup_eq_ker {Q : Ideal B} (hQ : Q ≠ ⊤) :
    ⨅ i : ℕ, Q.ramificationGroup G i = MonoidHom.ker (MulSemiringAction.toRingAut G B) := by
  ext σ
  rw [Subgroup.mem_iInf, TauCeti.MulSemiringAction.mem_ker_toRingAut_iff]
  refine ⟨fun hσ x ↦ ?_, fun h i ↦ mem_ramificationGroup_iff.2 fun x ↦ ?_⟩
  · have hmem : σ • x - x ∈ ⨅ n : ℕ, Q ^ n := Submodule.mem_iInf _ |>.2 fun n ↦
      Ideal.pow_le_pow_right (Nat.le_succ n) (mem_ramificationGroup_iff.1 (hσ n) x)
    rwa [Ideal.iInf_pow_eq_bot_of_isDomain _ hQ, Ideal.mem_bot, sub_eq_zero] at hmem
  · rw [h x, sub_self]
    exact zero_mem _

/- For a faithful action on a Noetherian domain, the ramification groups of a proper ideal
intersect in the trivial group. -/
theorem exists_forall_ramificationGroup_eq_ker {Q : Ideal B} (hQ : Q ≠ ⊤) [Finite (Q.inertia G)] :
    ∃ N : ℕ, ∀ i, N ≤ i →
      Q.ramificationGroup G i = MonoidHom.ker (MulSemiringAction.toRingAut G B) := by
  have : Finite (Q.ramificationGroup G 0) := by rwa [ramificationGroup_zero]
  obtain ⟨N, hN⟩ := TauCeti.Subgroup.exists_forall_eq_iInf_of_antitone _
    (ramificationGroup_antitone G Q)
  exact ⟨N, fun i hi ↦ (hN i hi).trans (iInf_ramificationGroup_eq_ker hQ)⟩

/- For a faithful action on a Noetherian domain with finite inertia group, the ramification
groups of a proper ideal are trivial from some index on. -/
theorem exists_forall_ramificationGroup_eq_bot [FaithfulSMul G B] {Q : Ideal B} (hQ : Q ≠ ⊤)
    [Finite (Q.inertia G)] : ∃ N : ℕ, ∀ i, N ≤ i → Q.ramificationGroup G i = ⊥ := by
  simpa only [TauCeti.MulSemiringAction.ker_toRingAut_eq_bot] using
    exists_forall_ramificationGroup_eq_ker (G := G) hQ

end Noetherian

end Ideal

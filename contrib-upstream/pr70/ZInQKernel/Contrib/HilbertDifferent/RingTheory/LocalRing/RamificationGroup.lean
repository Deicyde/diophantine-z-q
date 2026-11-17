/-
Ported with Codex assistance on 2026-11-14 from trureturing@8af78b5bb176c99b2750222c0dd3d00a475d39eb.
Source: D5/S3/Factorization/Dedekind/HilbertDifferent/RingTheory/LocalRing/RamificationGroup.lean
Original SHA-256: 169f9afa1a0a1102cfd05d3847da5b309daefa205b11e34f9146d155be679ca6
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
TauCeti/RingTheory/LocalRing/RamificationGroup.lean.
Full license and pertinent inherited attribution: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
Replace this port by direct use when this project's pinned Mathlib supplies an equivalent declaration. -/


import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Valuation.RamificationGroup
import ZInQKernel.Contrib.HilbertDifferent.Algebra.Group.Subgroup.FiniteFiltration
import ZInQKernel.Contrib.HilbertDifferent.Algebra.Ring.Action.End
import ZInQKernel.Contrib.HilbertDifferent.RingTheory.DiscreteValuationRing.Basic
import ZInQKernel.Contrib.HilbertDifferent.RingTheory.Ideal.Inertia
import ZInQKernel.Contrib.HilbertDifferent.RingTheory.Ideal.RamificationGroup
import Mathlib.RingTheory.Ideal.Pointwise
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import ZInQKernel.Contrib.HilbertDifferent.Support.TameDifferent
import Mathlib.Combinatorics.Enumerative.DoubleCounting

noncomputable section

section

open IsLocalRing

open scoped Pointwise

namespace TauCeti

namespace IsLocalRing

section Defs

variable (G : Type*) [Group G] (S : Type*) [CommRing S] [IsLocalRing S] [MulSemiringAction G S]

/- The `i`-th **ramification group**, in the lower numbering, of a group `G` acting by ring
automorphisms on a local ring `S`: the subgroup of elements acting trivially on `S ⧸ 𝔪 ^ (i + 1)`.
The index is an integer, and `𝔪 ^ (i + 1)` is read as `𝔪 ^ (i + 1).toNat`, so that the family is
total and constantly `⊤` for `i ≤ -1`. -/
def ramificationGroup (i : ℤ) : Subgroup G :=
  Ideal.inertia G (maximalIdeal S ^ (i + 1).toNat)

/- The ramification groups are the inertia subgroups of the powers of the maximal ideal. -/
variable {G S}

/- The defining membership criterion of the ramification groups. -/
@[simp]
theorem mem_ramificationGroup_iff {i : ℤ} {σ : G} :
    σ ∈ ramificationGroup G S i ↔ ∀ x : S, σ • x - x ∈ maximalIdeal S ^ (i + 1).toNat :=
  Ideal.mem_inertia

/- At a nonnegative index the truncation disappears from the membership criterion. -/
theorem mem_ramificationGroup_natCast_iff {n : ℕ} {σ : G} :
    σ ∈ ramificationGroup G S n ↔ ∀ x : S, σ • x - x ∈ maximalIdeal S ^ (n + 1) := by
  have h : ((n : ℤ) + 1).toNat = n + 1 := by omega
  rw [mem_ramificationGroup_iff, h]

/- At a nonnegative index, the ramification group of the local ring is the ramification group
`Ideal.ramificationGroup` of its maximal ideal. -/
variable (G S)

/- Below the index `0` the filtration is the whole group. -/
theorem ramificationGroup_antitone : Antitone (ramificationGroup G S) := by
  intro i j hij σ hσ
  rw [mem_ramificationGroup_iff] at hσ ⊢
  exact fun x ↦ Ideal.pow_le_pow_right (by omega) (hσ x)

end Defs

section Adjoin

variable {G : Type*} [Group G] {S : Type*} [CommRing S] [IsLocalRing S] [MulSemiringAction G S]
variable {R : Type*} [CommSemiring R] [Algebra R S] [SMulCommClass G R S]

/- **Serre's criterion** for the ramification filtration: when `S` is generated over `R` by a set
`s` and `G` acts by `R`-algebra automorphisms, membership in `G_i` is decided on `s` alone. This
is `TauCeti.Ideal.mem_inertia_iff_of_adjoin_eq_top` at a power of the maximal ideal. -/
end Adjoin

section Normal

variable {G : Type*} [Group G] {S : Type*} [CommRing S] [IsLocalRing S] [MulSemiringAction G S]

/- Every ramification group is normal, because the action fixes the powers of the maximal
ideal. -/
end Normal

section ResidueField

variable (G : Type*) [Group G] (S : Type*) [CommRing S] [IsLocalRing S] [MulSemiringAction G S]

/- The zeroth ramification group is the inertia group: the kernel of the induced action on the
residue field. -/
end ResidueField

section Separated

variable (G : Type*) [Group G] (S : Type*) [CommRing S] [IsLocalRing S] [MulSemiringAction G S]
variable [IsNoetherianRing S]

/- Over a Noetherian local ring the ramification filtration cuts out the kernel of the action:
an element moving no point of `S` into every power of the maximal ideal is one that moves no
point at all. -/
theorem iInf_ramificationGroup_eq_ker :
    ⨅ i : ℤ, ramificationGroup G S i = MonoidHom.ker (MulSemiringAction.toRingAut G S) := by
  ext σ
  rw [Subgroup.mem_iInf, TauCeti.MulSemiringAction.mem_ker_toRingAut_iff]
  refine ⟨fun hσ x ↦ ?_, fun h i ↦ mem_ramificationGroup_iff.2 fun x ↦ ?_⟩
  · have hmem : σ • x - x ∈ ⨅ n : ℕ, maximalIdeal S ^ n := by
      refine Submodule.mem_iInf _ |>.2 fun n ↦ ?_
      have h : (((n : ℤ) - 1) + 1).toNat = n := by omega
      have hx := mem_ramificationGroup_iff.1 (hσ ((n : ℤ) - 1)) x
      rwa [h] at hx
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal S).ne_top,
      Ideal.mem_bot, sub_eq_zero] at hmem
    exact hmem
  · rw [h x, sub_self]
    exact zero_mem _

/- A faithful action on a Noetherian local ring is separated by its ramification filtration. -/
omit [IsNoetherianRing S] in
/- The intersection over the integer indices is already attained over the natural ones, since the
filtration is constantly `⊤` below `0`. -/
private theorem iInf_natCast_ramificationGroup :
    ⨅ n : ℕ, ramificationGroup G S (n : ℤ) = ⨅ i : ℤ, ramificationGroup G S i :=
  le_antisymm
    (le_iInf fun i ↦ (iInf_le _ i.toNat).trans
      (ramificationGroup_antitone G S (Int.self_le_toNat i)))
    (le_iInf fun n ↦ iInf_le _ (n : ℤ))

/- Once the zeroth ramification group is finite, the filtration over a Noetherian local ring
reaches the kernel of the action at a finite index. -/
theorem exists_forall_ramificationGroup_eq_ker [Finite (ramificationGroup G S 0)] :
    ∃ N : ℤ, ∀ i : ℤ, N ≤ i →
      ramificationGroup G S i = MonoidHom.ker (MulSemiringAction.toRingAut G S) := by
  have hanti : Antitone fun n : ℕ ↦ ramificationGroup G S (n : ℤ) :=
    fun _ _ hmn ↦ ramificationGroup_antitone G S (by exact_mod_cast hmn)
  have h0 : (fun n : ℕ ↦ ramificationGroup G S (n : ℤ)) 0 = ramificationGroup G S 0 := by
    norm_num
  have : Finite ((fun n : ℕ ↦ ramificationGroup G S (n : ℤ)) 0) := h0 ▸ ‹_›
  obtain ⟨N, hN⟩ := TauCeti.Subgroup.exists_forall_eq_iInf_of_antitone _ hanti
  refine ⟨(N : ℤ), fun i hi ↦ ?_⟩
  have hi0 : (0 : ℤ) ≤ i := (Int.natCast_nonneg N).trans hi
  have hcast : (i.toNat : ℤ) = i := Int.toNat_of_nonneg hi0
  have hiN : N ≤ i.toNat := by omega
  rw [← hcast, hN i.toNat hiN, iInf_natCast_ramificationGroup, iInf_ramificationGroup_eq_ker]

/- For a faithful action whose zeroth ramification group is finite, the ramification groups over
a Noetherian local ring vanish from some index on. -/
theorem exists_forall_ramificationGroup_eq_bot [FaithfulSMul G S]
    [Finite (ramificationGroup G S 0)] :
    ∃ N : ℤ, ∀ i : ℤ, N ≤ i → ramificationGroup G S i = ⊥ := by
  simpa only [TauCeti.MulSemiringAction.ker_toRingAut_eq_bot] using
    exists_forall_ramificationGroup_eq_ker G S

end Separated

section DiscreteValuationRing

variable {G : Type*} [Group G] {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
variable [MulSemiringAction G S]

/- Over a discrete valuation ring the ramification groups are cut out by the valuation
inequality `v (σ x - x) ≥ i + 1`, which is Serre's definition. -/
theorem mem_ramificationGroup_iff_le_addVal {i : ℤ} {σ : G} :
    σ ∈ ramificationGroup G S i ↔
      ∀ x : S, ((i + 1).toNat : ℕ∞) ≤ IsDiscreteValuationRing.addVal S (σ • x - x) := by
  simp only [mem_ramificationGroup_iff,
    TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal]

variable (S) in
/- Serre's **lower index** `i_G(σ)` of an element `σ` acting on a discrete valuation ring `S`:
the least valuation `v (σ x - x)` over all `x : S`, with value `⊤` when `σ` acts trivially.
Its superlevel sets are the ramification groups:
`σ ∈ G_i ↔ i + 1 ≤ i_G(σ)`. -/
noncomputable def lowerIndex (σ : G) : ℕ∞ :=
  ⨅ x : S, IsDiscreteValuationRing.addVal S (σ • x - x)

/- The lower index is the infimum of the valuations of all displacements. -/
theorem le_lowerIndex_iff {n : ℕ∞} {σ : G} :
    n ≤ lowerIndex S σ ↔ ∀ x : S, n ≤ IsDiscreteValuationRing.addVal S (σ • x - x) :=
  le_iInf_iff

/- The lower index is at most the valuation `v (σ x - x)` at any `x`. -/
theorem lowerIndex_le_addVal (σ : G) (x : S) :
    lowerIndex S σ ≤ IsDiscreteValuationRing.addVal S (σ • x - x) :=
  iInf_le _ x

/- The ramification groups are the superlevel sets of the lower index: `σ ∈ G_i` exactly when
`i + 1 ≤ i_G(σ)`. -/
theorem mem_ramificationGroup_iff_le_lowerIndex {i : ℤ} {σ : G} :
    σ ∈ ramificationGroup G S i ↔ ((i + 1).toNat : ℕ∞) ≤ lowerIndex S σ := by
  rw [mem_ramificationGroup_iff_le_addVal, le_lowerIndex_iff]

/- A natural number bounds the lower index exactly when the automorphism belongs to the
corresponding ramification group. -/
theorem lowerIndex_eq_addVal_of_adjoin_singleton_eq_top {R : Type*} [CommSemiring R]
    [Algebra R S] [SMulCommClass G R S] {ξ : S} (hξ : Algebra.adjoin R {ξ} = ⊤) (σ : G) :
    lowerIndex S σ = IsDiscreteValuationRing.addVal S (σ • ξ - ξ) := by
  refine (lowerIndex_le_addVal σ ξ).antisymm (le_lowerIndex_iff.2 fun x ↦ ?_)
  exact IsDiscreteValuationRing.addVal_le_iff_dvd.2
    (TauCeti.smul_sub_dvd_smul_sub_of_adjoin_singleton_eq_top hξ σ x)

variable {R : Type*} [CommSemiring R] [Algebra R S] [SMulCommClass G R S]

/- When the discrete valuation ring `S` is generated over a base `R` fixed by `G` by a single
element `ξ`, membership in `G_n` for `n : ℕ` is the single inequality `v (σ • ξ - ξ) ≥ n + 1`. -/
theorem mem_ramificationGroup_natCast_iff_le_addVal_of_adjoin_singleton_eq_top {ξ : S}
    (hξ : Algebra.adjoin R {ξ} = ⊤) {n : ℕ} {σ : G} :
    σ ∈ ramificationGroup G S n ↔
      ((n + 1 : ℕ) : ℕ∞) ≤ IsDiscreteValuationRing.addVal S (σ • ξ - ξ) := by
  have h : ((n : ℤ) + 1).toNat = n + 1 := by omega
  rw [mem_ramificationGroup_iff_le_lowerIndex,
    lowerIndex_eq_addVal_of_adjoin_singleton_eq_top hξ, h]

open Finset in
/- **Hilbert's counting identity.** Let a finite group `G` act faithfully on a discrete valuation
ring `S` generated over a base `R` fixed by `G` by a single element `ξ`. Then the sum over the
nontrivial `σ ∈ G` of the valuations `v (σ • ξ - ξ)` is `∑_{i ≥ 0} (#G_i - 1)`, where `G_i` is
the `i`-th ramification group: each `σ ≠ 1` lies in exactly `v (σ • ξ - ξ)` of the groups
`G_0, G_1, …`, and the sum is finite because the filtration is eventually trivial. -/
theorem sum_addVal_smul_sub_eq_finsum_card_ramificationGroup_sub_one [Fintype G] [DecidableEq G]
    [FaithfulSMul G S] {ξ : S} (hξ : Algebra.adjoin R {ξ} = ⊤) :
    ∑ σ ∈ (univ : Finset G).erase 1, IsDiscreteValuationRing.addVal S (σ • ξ - ξ) =
      ((∑ᶠ i : ℕ, (Nat.card (ramificationGroup G S i) - 1) : ℕ) : ℕ∞) := by
  classical
  -- The filtration vanishes from some natural index `N` on.
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ i : ℕ, N ≤ i → ramificationGroup G S i = ⊥ := by
    obtain ⟨N₀, hN₀⟩ := exists_forall_ramificationGroup_eq_bot G S
    exact ⟨N₀.toNat, fun i hi ↦ hN₀ i (by omega)⟩
  -- For `σ ≠ 1`, the valuation `v (σ • ξ - ξ)` counts the indices `i < N` with `σ ∈ G_i`.
  have hval : ∀ σ ∈ univ.erase (1 : G), IsDiscreteValuationRing.addVal S (σ • ξ - ξ) =
      (((range N).filter fun i : ℕ ↦ σ ∈ ramificationGroup G S i).card : ℕ∞) := by
    intro σ hσ
    have hσ1 : σ ≠ 1 := ne_of_mem_erase hσ
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 <|
      IsDiscreteValuationRing.addVal_eq_top_iff.not.2 <| sub_ne_zero.2 fun h ↦
        hσ1 (eq_one_of_smul_eq_of_adjoin_singleton_eq_top hξ h)
    have hnN : n ≤ N := by
      by_contra hlt
      have hmem : σ ∈ ramificationGroup G S N := by
        rw [mem_ramificationGroup_natCast_iff_le_addVal_of_adjoin_singleton_eq_top hξ, ← hn]
        exact_mod_cast (by omega : N + 1 ≤ n)
      rw [hN N le_rfl, Subgroup.mem_bot] at hmem
      exact hσ1 hmem
    have hfilter : ((range N).filter fun i : ℕ ↦ σ ∈ ramificationGroup G S i) = range n := by
      ext i
      simp only [mem_filter, mem_range,
        mem_ramificationGroup_natCast_iff_le_addVal_of_adjoin_singleton_eq_top hξ, ← hn,
        Nat.cast_le]
      omega
    rw [hfilter, card_range, hn]
  rw [sum_congr rfl hval, ← Nat.cast_sum]
  congr 1
  -- Double counting: `∑_{σ ≠ 1} #{i < N | σ ∈ G_i} = ∑_{i < N} #{σ ≠ 1 | σ ∈ G_i}`.
  have hdc := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (fun (σ : G) (i : ℕ) ↦ σ ∈ ramificationGroup G S i) (s := univ.erase 1) (t := range N)
  simp only [bipartiteAbove, bipartiteBelow] at hdc
  rw [hdc, finsum_eq_sum_of_support_subset (s := range N)]
  · refine sum_congr rfl fun i _ ↦ ?_
    rw [filter_erase, card_erase_of_mem (mem_filter.2 ⟨mem_univ _, one_mem _⟩),
      Nat.card_eq_fintype_card, Fintype.card_subtype]
  · intro i hi
    by_contra h
    rw [coe_range, Set.mem_Iio, not_lt] at h
    rw [Function.mem_support, hN i h, Subgroup.card_bot] at hi
    exact hi rfl

end DiscreteValuationRing

section Subgroup

variable (G : Type*) [Group G] (S : Type*) [CommRing S] [IsLocalRing S] [MulSemiringAction G S]

/- The ramification filtration of a subgroup is the trace on it of the ramification filtration of
the ambient group. -/
end Subgroup

section Real

variable (G : Type*) [Group G] (S : Type*) [CommRing S] [IsLocalRing S] [MulSemiringAction G S]

/- The ramification filtration reindexed by a real number, through the ceiling. This is the
indexing convention of Herbrand theory: the resulting step function is constant on `(i - 1, i]`. -/
end Real

section RealDiscreteValuationRing

variable {G : Type*} [Group G] {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
variable [MulSemiringAction G S]

/- When the lower index of `σ` is the natural number `n`, `σ ∈ G_u` for a real `u` exactly when
`u ≤ n - 1`. -/
end RealDiscreteValuationRing

end IsLocalRing

end TauCeti

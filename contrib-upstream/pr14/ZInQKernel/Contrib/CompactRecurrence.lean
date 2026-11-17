module

public import Mathlib.Topology.Algebra.Group.SubmonoidClosure

/-!
# Simultaneous recurrence in two compact groups

Apply pinned Mathlib recurrence to the pair before extracting the index.
Both coordinates return at one positive natural index beyond any given bound.
No commutativity, separation, or infinite-order assumption is needed.

This is an application of existing mathematics, ported from PR #14's optional
examples. It does not prove the geometric interfaces or `CondZQ.HypCC`.
See `docs/research/compact-recurrence.md` for sources and the conditional mapping.
-/

public section

namespace ZInQ.CompactRecurrence

open Filter Set
open scoped Topology

section Additive

variable {A B : Type*}
  [AddGroup A] [TopologicalSpace A] [CompactSpace A] [IsTopologicalAddGroup A]
  [AddGroup B] [TopologicalSpace B] [CompactSpace B] [IsTopologicalAddGroup B]

/-- One positive natural index beyond any bound returns both additive coordinates. -/
theorem exists_nsmul_mem_prod_gt (x : A) (y : B) (U : Set A) (V : Set B)
    (hU : U ∈ 𝓝 (0 : A)) (hV : V ∈ 𝓝 (0 : B)) (N : ℕ) :
    ∃ a : ℕ, N < a ∧ 0 < a ∧ a • x ∈ U ∧ a • y ∈ V := by
  have h : ∃ᶠ a : ℕ in atTop, a • (x, y) ∈ U ×ˢ V :=
    mapClusterPt_iff_frequently.mp (mapClusterPt_zero_atTop_nsmul (x, y))
      (U ×ˢ V) (prod_mem_nhds hU hV)
  obtain ⟨a, ha, hUV⟩ := frequently_atTop.mp h (N + 1)
  exact ⟨a, lt_of_lt_of_le (Nat.lt_succ_self N) ha,
    lt_of_lt_of_le (Nat.zero_lt_succ N) ha, hUV.1, hUV.2⟩

end Additive

section Multiplicative

variable {G H : Type*}
  [Group G] [TopologicalSpace G] [CompactSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [CompactSpace H] [IsTopologicalGroup H]

/-- One positive natural index beyond any bound returns both multiplicative coordinates. -/
theorem exists_pow_mem_prod_gt (x : G) (y : H) (U : Set G) (V : Set H)
    (hU : U ∈ 𝓝 (1 : G)) (hV : V ∈ 𝓝 (1 : H)) (N : ℕ) :
    ∃ a : ℕ, N < a ∧ 0 < a ∧ x ^ a ∈ U ∧ y ^ a ∈ V := by
  have h : ∃ᶠ a : ℕ in atTop, (x, y) ^ a ∈ U ×ˢ V :=
    mapClusterPt_iff_frequently.mp (mapClusterPt_one_atTop_pow (x, y))
      (U ×ˢ V) (prod_mem_nhds hU hV)
  obtain ⟨a, ha, hUV⟩ := frequently_atTop.mp h (N + 1)
  exact ⟨a, lt_of_lt_of_le (Nat.lt_succ_self N) ha,
    lt_of_lt_of_le (Nat.zero_lt_succ N) ha, hUV.1, hUV.2⟩

end Multiplicative

end ZInQ.CompactRecurrence

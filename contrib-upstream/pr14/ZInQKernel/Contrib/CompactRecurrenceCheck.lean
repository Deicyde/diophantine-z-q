import ZInQKernel.Contrib.CompactRecurrence

/-!
Ordinary-importer checks for the complete exported statements. These examples
keep arbitrary identity neighborhoods, independent universes, noncommutative
groups, torsion, and an arbitrary lower bound. This is author validation,
not independent Protocol acceptance.
-/

open Filter Set
open scoped Topology

section Additive

variable {A B : Type*}
  [AddGroup A] [TopologicalSpace A] [CompactSpace A] [IsTopologicalAddGroup A]
  [AddGroup B] [TopologicalSpace B] [CompactSpace B] [IsTopologicalAddGroup B]

example (x : A) (y : B) (U : Set A) (V : Set B)
    (hU : U ∈ 𝓝 (0 : A)) (hV : V ∈ 𝓝 (0 : B)) (N : ℕ) :
    ∃ a : ℕ, N < a ∧ 0 < a ∧ a • x ∈ U ∧ a • y ∈ V :=
  ZInQ.CompactRecurrence.exists_nsmul_mem_prod_gt x y U V hU hV N

end Additive

section Multiplicative

variable {G H : Type*}
  [Group G] [TopologicalSpace G] [CompactSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [CompactSpace H] [IsTopologicalGroup H]

example (x : G) (y : H) (U : Set G) (V : Set H)
    (hU : U ∈ 𝓝 (1 : G)) (hV : V ∈ 𝓝 (1 : H)) (N : ℕ) :
    ∃ a : ℕ, N < a ∧ 0 < a ∧ x ^ a ∈ U ∧ y ^ a ∈ V :=
  ZInQ.CompactRecurrence.exists_pow_mem_prod_gt x y U V hU hV N

end Multiplicative

-- These inspect the complete exported proof terms, not only their suppliers.
/-- info: 'ZInQ.CompactRecurrence.exists_nsmul_mem_prod_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZInQ.CompactRecurrence.exists_nsmul_mem_prod_gt
/-- info: 'ZInQ.CompactRecurrence.exists_pow_mem_prod_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZInQ.CompactRecurrence.exists_pow_mem_prod_gt

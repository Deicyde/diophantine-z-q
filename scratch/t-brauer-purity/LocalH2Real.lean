import Mathlib

/-!
# t-brauer-purity: the real-place half of leaf T15 (`PkgI6.LocalH2CardC`)

`PkgI6.LocalH2CardC` (ZInQKernel/HDecomp/Conductor/I6Base.lean) is the conjunction of
`∀ p, H2TwoClasses (Field.absoluteGaloisGroup ℚ_[p])` and
`H2TwoClasses (Field.absoluteGaloisGroup ℝ)`.  This file proves the second conjunct outright
(no leaf), via a general lemma: every discrete group of order two satisfies `H2TwoClasses`.

The definitions `IsCocycle2`, `IsCoboundary2`, `H2TwoClasses` are copied verbatim from
ZInQKernel/HDecomp/Conductor/I6Base.lean (namespace `PkgI6`).
-/

namespace PkgI6

/-- A continuous inhomogeneous 2-cocycle with values in the trivial module `ℤ/2`. -/
def IsCocycle2 {G : Type*} [Group G] [TopologicalSpace G] (ε : G → G → ZMod 2) : Prop :=
  Continuous (fun x : G × G => ε x.1 x.2) ∧ ∀ a b c, ε b c - ε (a * b) c + ε a (b * c) - ε a b = 0

/-- `ε` is the coboundary of a continuous 1-cochain. -/
def IsCoboundary2 {G : Type*} [Group G] [TopologicalSpace G] (ε : G → G → ZMod 2) : Prop :=
  ∃ f : G → ZMod 2, Continuous f ∧ ∀ a b, ε a b = f b - f (a * b) + f a

/-- `H²(G, ℤ/2)` has exactly two elements, on cochains: a non-trivial class exists, and any two
non-trivial classes differ by a coboundary. -/
def H2TwoClasses (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  (∃ ε, IsCocycle2 (G := G) ε ∧ ¬ IsCoboundary2 ε) ∧
  ∀ ε₁ ε₂, IsCocycle2 (G := G) ε₁ → IsCocycle2 ε₂ → ¬ IsCoboundary2 ε₁ → ¬ IsCoboundary2 ε₂ →
    IsCoboundary2 (ε₁ - ε₂)

end PkgI6

namespace TBrauerPurity

open PkgI6

section Order2

open scoped Classical

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

omit [TopologicalSpace G] [DiscreteTopology G] in
/-- In a group of order two with nontrivial element `s`: every element is `1` or `s`, and
`s * s = 1`. -/
lemma order2_facts (hG : Nat.card G = 2) :
    ∃ s : G, s ≠ 1 ∧ (∀ x : G, x = 1 ∨ x = s) ∧ s * s = 1 := by
  obtain ⟨s, hs, huniq⟩ := (Nat.card_eq_two_iff' (1 : G)).mp hG
  have mem : ∀ z : G, z = 1 ∨ z = s := fun z => by
    by_cases hz : z = 1
    · exact Or.inl hz
    · exact Or.inr (huniq z hz)
  refine ⟨s, hs, mem, ?_⟩
  rcases mem (s * s) with h | h
  · exact h
  · exact absurd (mul_eq_left.mp h) hs

omit [DiscreteTopology G] in
/-- Two cochain identities forced by the cocycle relation: `ε 1 z = ε 1 1` and `ε x 1 = ε 1 1`. -/
lemma cocycle_one_left {ε : G → G → ZMod 2} (h : IsCocycle2 ε) (z : G) : ε 1 z = ε 1 1 := by
  have := h.2 1 1 z
  simp only [one_mul] at this
  linear_combination this

omit [DiscreteTopology G] in
lemma cocycle_right_one {ε : G → G → ZMod 2} (h : IsCocycle2 ε) (x : G) : ε x 1 = ε 1 1 := by
  have := h.2 x 1 1
  simp only [mul_one] at this
  linear_combination -this

lemma zmod2_neg (a : ZMod 2) : -a = a := by revert a; decide

lemma zmod2_one_add_one : (1 : ZMod 2) + 1 = 0 := by decide

/-- **Key criterion.** For a discrete group of order two with nontrivial element `s`, a
2-cocycle is a coboundary iff `ε 1 1 = ε s s`. -/
lemma isCoboundary2_iff_of_order2 {s : G} (hs : s ≠ 1) (mem : ∀ x : G, x = 1 ∨ x = s)
    (hss : s * s = 1) {ε : G → G → ZMod 2} (h : IsCocycle2 ε) :
    IsCoboundary2 ε ↔ ε 1 1 = ε s s := by
  constructor
  · rintro ⟨f, -, hf⟩
    rw [hf 1 1, hf s s, hss]
    simp only [one_mul, sub_self, zero_add]
    have h2 : f s - f 1 + f s = -f 1 := by
      have : (2 : ZMod 2) = 0 := by decide
      linear_combination (f s) * this
    rw [h2, zmod2_neg]
  · intro hd
    refine ⟨fun x => if x = 1 then ε 1 1 else 0, continuous_of_discreteTopology, fun a b => ?_⟩
    rcases mem a with rfl | rfl <;> rcases mem b with rfl | rfl
    · simp
    · simp [hs, cocycle_one_left h]
    · simp [hs, cocycle_right_one h]
    · simp only [hss, hs, ite_false, ite_true]
      rw [← hd]
      simp only [zero_sub, add_zero, zmod2_neg]

/-- **`H²(G, ℤ/2)` on cochains for a discrete group of order two** (the cyclic group case of
the periodicity `H²(ℤ/2, ℤ/2) = ℤ/2`). -/
theorem h2TwoClasses_of_card_two (hG : Nat.card G = 2) : H2TwoClasses G := by
  obtain ⟨s, hs, mem, hss⟩ := order2_facts hG
  have crit := fun {ε : G → G → ZMod 2} (h : IsCocycle2 ε) =>
    isCoboundary2_iff_of_order2 hs mem hss h
  refine ⟨⟨fun x y => if x = s ∧ y = s then 1 else 0, ?_, ?_⟩, ?_⟩
  · refine ⟨continuous_of_discreteTopology, fun a b c => ?_⟩
    rcases mem a with rfl | rfl <;> rcases mem b with rfl | rfl <;> rcases mem c with rfl | rfl <;>
      simp [hs.symm, hss, zmod2_one_add_one]
  · intro hcob
    have hc : IsCocycle2 (G := G) (fun x y => if x = s ∧ y = s then 1 else 0) := by
      refine ⟨continuous_of_discreteTopology, fun a b c => ?_⟩
      rcases mem a with rfl | rfl <;> rcases mem b with rfl | rfl <;>
        rcases mem c with rfl | rfl <;> simp [hs.symm, hss, zmod2_one_add_one]
    have := (crit hc).mp hcob
    simp [hs.symm] at this
  · intro ε₁ ε₂ h₁ h₂ n₁ n₂
    have h₁₂ : IsCocycle2 (ε₁ - ε₂) := by
      refine ⟨h₁.1.sub h₂.1, fun a b c => ?_⟩
      simp only [Pi.sub_apply]
      linear_combination h₁.2 a b c - h₂.2 a b c
    rw [crit h₁] at n₁
    rw [crit h₂] at n₂
    rw [crit h₁₂]
    simp only [Pi.sub_apply]
    generalize ε₁ 1 1 = a₁ at n₁ ⊢
    generalize ε₁ s s = b₁ at n₁ ⊢
    generalize ε₂ 1 1 = a₂ at n₂ ⊢
    generalize ε₂ s s = b₂ at n₂ ⊢
    revert a₁ b₁ a₂ b₂
    decide

end Order2

section Real

/-- `ℂ` is an algebraic closure of `ℝ`. -/
instance isAlgClosure_real_complex : IsAlgClosure ℝ ℂ := ⟨inferInstance, inferInstance⟩

/-- `AlgebraicClosure ℝ ≃ₐ[ℝ] ℂ`. -/
noncomputable def algClosureRealEquiv : AlgebraicClosure ℝ ≃ₐ[ℝ] ℂ :=
  IsAlgClosure.equiv ℝ (AlgebraicClosure ℝ) ℂ

instance finiteDimensional_algClosure_real : FiniteDimensional ℝ (AlgebraicClosure ℝ) :=
  LinearEquiv.finiteDimensional algClosureRealEquiv.symm.toLinearEquiv

lemma finrank_algClosure_real : Module.finrank ℝ (AlgebraicClosure ℝ) = 2 := by
  rw [algClosureRealEquiv.toLinearEquiv.finrank_eq, Complex.finrank_real_complex]

instance isGalois_algClosure_real : IsGalois ℝ (AlgebraicClosure ℝ) := inferInstance

/-- `G_ℝ` has order two. -/
lemma card_absoluteGaloisGroup_real : Nat.card (Field.absoluteGaloisGroup ℝ) = 2 := by
  show Nat.card Gal(AlgebraicClosure ℝ/ℝ) = 2
  rw [IsGalois.card_aut_eq_finrank, finrank_algClosure_real]

/-- `G_ℝ` is discrete in the Krull topology (it is the Galois group of a finite extension). -/
instance discreteTopology_absoluteGaloisGroup_real :
    DiscreteTopology (Field.absoluteGaloisGroup ℝ) :=
  krullTopology_discreteTopology_of_finiteDimensional ℝ (AlgebraicClosure ℝ)

/-- **The real-place half of leaf T15 (`PkgI6.LocalH2CardC`), proved:**
`H²(G_ℝ, ℤ/2)` has exactly two classes, on continuous inhomogeneous cochains. -/
theorem h2TwoClasses_real : H2TwoClasses (Field.absoluteGaloisGroup ℝ) :=
  h2TwoClasses_of_card_two card_absoluteGaloisGroup_real

/-- `LocalH2CardC` is equivalent to its finite-place half. -/
theorem localH2CardC_iff :
    ((∀ (p : ℕ) [Fact p.Prime], H2TwoClasses (Field.absoluteGaloisGroup ℚ_[p])) ∧
      H2TwoClasses (Field.absoluteGaloisGroup ℝ)) ↔
    (∀ (p : ℕ) [Fact p.Prime], H2TwoClasses (Field.absoluteGaloisGroup ℚ_[p])) :=
  ⟨fun h => h.1, fun h => ⟨h, h2TwoClasses_real⟩⟩

end Real

end TBrauerPurity

#print axioms TBrauerPurity.h2TwoClasses_real
#print axioms TBrauerPurity.localH2CardC_iff

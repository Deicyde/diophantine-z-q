import Mathlib

/-!
# Lane RC12-odd: graph dependence by bridge copies (App F, tex 9955–9974)

"Finally the fixed-`U` factorization gives dependence on the entire finite typed graph. For two
disjoint prime realizations of the same graph, choose a fresh bridge copy with the prescribed types
and matching incidences to both realizations. … Replace the vertices of the first copy by bridge
vertices one at a time, then the bridge vertices by those of the second copy. At each step the other
vertices form the same fixed `U`, and the changed vertex has the same elementary Frobenius data for
`S ∪ U`; its symbol therefore agrees. … A vertex and its own replacement are never tested together,
so their mutual bit can be chosen freely."

`replace_chain` is the one-at-a-time replacement, **PROVED** for an abstract reading `A` of prime
sets and an abstract label `lab p W` (the elementary Frobenius data of `p` relative to `W`: its type
and its residue bits with `W`), under the swap invariance that the factorization through the
elementary quadratic quotient supplies (`Traces.factor_through_squares`, tex 9745–9750).
`bridge_copy` composes two chains through a bridge. The existence of the bridge (CRT, Dirichlet,
reciprocity; the finite realization lemma `ex:sec7-realization`, lane RC2) is a hypothesis.
-/

namespace ZInQ.Manuscript.RC.Odd

open Finset

variable {P : Type*} [DecidableEq P] {Data : Type*}

/-- The set `{y_0, …, y_{i−1}} ∪ {x_i, …, x_{k−1}}` after `i` replacements. -/
def chainSet (x y : ℕ → P) (k i : ℕ) : Finset P := (range i).image y ∪ (Ico i k).image x

/-- The other vertices at step `i`: `{y_0, …, y_{i−1}} ∪ {x_{i+1}, …, x_{k−1}}`. -/
def chainRest (x y : ℕ → P) (k i : ℕ) : Finset P := (range i).image y ∪ (Ico (i + 1) k).image x

/-- **PROVED (tex 9960–9964).** One-at-a-time replacement: if `x, y` are injective on `range k` with
disjoint images, the reading `A` is invariant under swapping a vertex for another with the same
label relative to the remaining vertices, and at every step `x_i` and `y_i` have the same label
relative to `chainRest`, then `A({x_0..x_{k−1}}) = A({y_0..y_{k−1}})`. -/
theorem replace_chain (A : Finset P → ZMod 2) (lab : P → Finset P → Data)
    (hswap : ∀ (W : Finset P) (p p' : P), p ∉ W → p' ∉ W → lab p W = lab p' W →
      A (insert p W) = A (insert p' W))
    (x y : ℕ → P) (k : ℕ) (hx : Set.InjOn x (range k)) (hy : Set.InjOn y (range k))
    (hxy : ∀ i < k, ∀ j < k, x i ≠ y j)
    (hlab : ∀ i < k, lab (x i) (chainRest x y k i) = lab (y i) (chainRest x y k i)) :
    A ((range k).image x) = A ((range k).image y) := by
  have step : ∀ i < k, A (chainSet x y k i) = A (chainSet x y k (i + 1)) := by
    intro i hi
    have hxi : x i ∉ chainRest x y k i := by
      simp only [chainRest, mem_union, mem_image, mem_range, mem_Ico, not_or, not_exists, not_and]
      refine ⟨fun j hj h => hxy i hi j (by omega) h.symm, fun j hj h => ?_⟩
      have := hx (by simp; omega) (by simp; omega) h
      omega
    have hyi : y i ∉ chainRest x y k i := by
      simp only [chainRest, mem_union, mem_image, mem_range, mem_Ico, not_or, not_exists, not_and]
      refine ⟨fun j hj h => ?_, fun j hj h => hxy j (by omega) i hi h⟩
      have := hy (by simp; omega) (by simp; omega) h
      omega
    have e1 : chainSet x y k i = insert (x i) (chainRest x y k i) := by
      ext q
      simp only [chainSet, chainRest, mem_insert, mem_union, mem_image, mem_range, mem_Ico]
      constructor
      · rintro (⟨j, hj, rfl⟩ | ⟨j, ⟨hj1, hj2⟩, rfl⟩)
        · exact Or.inr (Or.inl ⟨j, hj, rfl⟩)
        · rcases Nat.eq_or_lt_of_le hj1 with rfl | hlt
          · exact Or.inl rfl
          · exact Or.inr (Or.inr ⟨j, ⟨hlt, hj2⟩, rfl⟩)
      · rintro (rfl | ⟨j, hj, rfl⟩ | ⟨j, ⟨hj1, hj2⟩, rfl⟩)
        · exact Or.inr ⟨i, ⟨le_rfl, hi⟩, rfl⟩
        · exact Or.inl ⟨j, hj, rfl⟩
        · exact Or.inr ⟨j, ⟨by omega, hj2⟩, rfl⟩
    have e2 : chainSet x y k (i + 1) = insert (y i) (chainRest x y k i) := by
      ext q
      simp only [chainSet, chainRest, mem_insert, mem_union, mem_image, mem_range, mem_Ico]
      constructor
      · rintro (⟨j, hj, rfl⟩ | ⟨j, ⟨hj1, hj2⟩, rfl⟩)
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
          · exact Or.inr (Or.inl ⟨j, hlt, rfl⟩)
          · exact Or.inl rfl
        · exact Or.inr (Or.inr ⟨j, ⟨hj1, hj2⟩, rfl⟩)
      · rintro (rfl | ⟨j, hj, rfl⟩ | ⟨j, ⟨hj1, hj2⟩, rfl⟩)
        · exact Or.inl ⟨i, by omega, rfl⟩
        · exact Or.inl ⟨j, by omega, rfl⟩
        · exact Or.inr ⟨j, ⟨hj1, hj2⟩, rfl⟩
    rw [e1, e2]
    exact hswap _ _ _ hxi hyi (hlab i hi)
  have hall : ∀ i ≤ k, A (chainSet x y k 0) = A (chainSet x y k i) := by
    intro i hi
    induction i with
    | zero => rfl
    | succ i ih => rw [ih (by omega), step i (by omega)]
  have h0 : chainSet x y k 0 = (range k).image x := by
    simp [chainSet, Nat.Ico_zero_eq_range]
  have hk : chainSet x y k k = (range k).image y := by
    simp [chainSet]
  rw [← h0, ← hk]
  exact hall k le_rfl

/-- **PROVED (tex 9955–9969).** Graph dependence through a bridge copy `b`: two chains of single
replacements, first `x → b`, then `b → y`. -/
theorem bridge_copy (A : Finset P → ZMod 2) (lab : P → Finset P → Data)
    (hswap : ∀ (W : Finset P) (p p' : P), p ∉ W → p' ∉ W → lab p W = lab p' W →
      A (insert p W) = A (insert p' W))
    (x y b : ℕ → P) (k : ℕ) (hx : Set.InjOn x (range k)) (hy : Set.InjOn y (range k))
    (hb : Set.InjOn b (range k)) (hxb : ∀ i < k, ∀ j < k, x i ≠ b j)
    (hby : ∀ i < k, ∀ j < k, b i ≠ y j)
    (hlab1 : ∀ i < k, lab (x i) (chainRest x b k i) = lab (b i) (chainRest x b k i))
    (hlab2 : ∀ i < k, lab (b i) (chainRest b y k i) = lab (y i) (chainRest b y k i)) :
    A ((range k).image x) = A ((range k).image y) :=
  (replace_chain A lab hswap x b k hx hb hxb hlab1).trans
    (replace_chain A lab hswap b y k hb hy hby hlab2)

end ZInQ.Manuscript.RC.Odd

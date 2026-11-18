import WeilTateBoundedKernelV002

/-!
# Lifting torsion points to Tate vectors from divisibility

If `G` is `ℓ`-divisible, every `x` with `x^{ℓᵏ} = 1` is the `k`-th component of a vector of `T_ℓ(G)`:
below level `k` take `x^{ℓ^{k-n}}`, above it iterated `ℓ`-th roots.  On the actual points `A.Pt Ω` the
divisibility is `WeilTate.Divisible.pt_pow_surjective`.
-/

noncomputable section

namespace WeilTate

open PkgI3

variable {ℓ : ℕ} [Fact ℓ.Prime] {G : Type*} [CommGroup G]

/-- Iterated `ℓ`-th roots of `x`. -/
def rootSeq (hdiv : ∀ g : G, ∃ h : G, h ^ ℓ = g) (x : G) : ℕ → G
  | 0 => x
  | m + 1 => Classical.choose (hdiv (rootSeq hdiv x m))

theorem rootSeq_succ_pow (hdiv : ∀ g : G, ∃ h : G, h ^ ℓ = g) (x : G) (m : ℕ) :
    rootSeq hdiv x (m + 1) ^ ℓ = rootSeq hdiv x m :=
  Classical.choose_spec (hdiv (rootSeq hdiv x m))

/-- The lifting sequence. -/
def liftSeq (hdiv : ∀ g : G, ∃ h : G, h ^ ℓ = g) (x : G) (k : ℕ) (n : ℕ) : G :=
  if n ≤ k then x ^ (ℓ ^ (k - n)) else rootSeq hdiv x (n - k)

theorem liftSeq_succ_pow (hdiv : ∀ g : G, ∃ h : G, h ^ ℓ = g) (x : G) (k n : ℕ) :
    liftSeq hdiv x k (n + 1) ^ ℓ = liftSeq hdiv x k n := by
  unfold liftSeq
  by_cases h1 : n + 1 ≤ k
  · rw [if_pos h1, if_pos (by omega), ← pow_mul, ← pow_succ]
    congr 2
    omega
  · rw [if_neg h1]
    by_cases h2 : n ≤ k
    · have hnk : n = k := by omega
      subst hnk
      rw [if_pos h2, Nat.sub_self, pow_zero, pow_one, show n + 1 - n = 0 + 1 by omega,
        rootSeq_succ_pow]
      rfl
    · rw [if_neg h2, show n + 1 - k = (n - k) + 1 by omega, rootSeq_succ_pow]

/-- **Torsion lifts to `T_ℓ` under `ℓ`-divisibility.** -/
theorem exists_tate_lift_of_divisible (hdiv : ∀ g : G, ∃ h : G, h ^ ℓ = g) (k : ℕ) (x : G)
    (hx : x ^ (ℓ ^ k) = 1) : ∃ t : Tate.T ℓ (Additive G), Additive.toMul (t.1 k) = x := by
  refine ⟨⟨fun n => Additive.ofMul (liftSeq hdiv x k n), ?_, fun n => ?_⟩, ?_⟩
  · change Additive.ofMul (liftSeq hdiv x k 0) = Additive.ofMul 1
    unfold liftSeq
    rw [if_pos (Nat.zero_le k), Nat.sub_zero, hx]
  · change ℓ • Additive.ofMul (liftSeq hdiv x k (n + 1)) = Additive.ofMul (liftSeq hdiv x k n)
    rw [← ofMul_pow, liftSeq_succ_pow]
  · change Additive.toMul (Additive.ofMul (liftSeq hdiv x k k)) = x
    rw [toMul_ofMul]
    unfold liftSeq
    rw [if_pos le_rfl, Nat.sub_self, pow_zero, pow_one]

end WeilTate

#check @WeilTate.exists_tate_lift_of_divisible
#print axioms WeilTate.exists_tate_lift_of_divisible

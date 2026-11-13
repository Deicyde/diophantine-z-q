import Mathlib
open Polynomial
example {K : Type*} [Field K] [IsAlgClosed K] (a0 a1 a2 a3 a4 a5 : K) :
    ∃ x : K, x ^ 6 + a5 * x ^ 5 + a4 * x ^ 4 + a3 * x ^ 3 + a2 * x ^ 2 + a1 * x + a0 = 0 := by
  have hd : (X ^ 6 + C a5 * X ^ 5 + C a4 * X ^ 4 + C a3 * X ^ 3 + C a2 * X ^ 2 + C a1 * X + C a0 :
      K[X]).degree = 6 := by compute_degree!
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root
    (X ^ 6 + C a5 * X ^ 5 + C a4 * X ^ 4 + C a3 * X ^ 3 + C a2 * X ^ 2 + C a1 * X + C a0 : K[X])
    (by rw [hd]; decide)
  exact ⟨x, by simpa using hx⟩

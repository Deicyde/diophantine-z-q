import ZInQKernel.RouteK.Rank5b.Sec3.TYZ
import ZInQKernel.RouteK.Rank5b.Check

/-!
# Cross-checks of Theorem 3.6 on small `n` (tyz-5b §6)

The bits `aBit`, `yBit`, `zBit` are defined through `IsSquare` in `ZMod p` and are not computable, so
`T5b n` cannot be evaluated by `decide`. The values below combine Theorem 3.6 with the kernel
evaluations of `det M_5b` in `Rank5b.Check` (`n = 21`: `T_5b = g(3) g(7) = 1`, the only admissible
partition being `{{3}, {7}}`; `n = 5`: no partition of `{5}` has a block of class 7), and check the
case `n = 5` directly from the definition of `T5b`.
-/

namespace ZInQ.RouteK.Rank5b

open Finset

/-- `T_5b(21) = 1`, by Theorem 3.6 and `det M_5b(21) = 1`. -/
theorem T5b_21 : T5b 21 = 1 := by
  have hsq : Squarefree 21 := by
    rw [show (21 : ℕ) = 3 * 7 from rfl]
    exact (Nat.squarefree_mul (by norm_num)).2
      ⟨Nat.prime_three.squarefree, (by norm_num : Nat.Prime 7).squarefree⟩
  rw [← det_M5b_eq_T5b (by norm_num) hsq]
  exact det_M5b_21

/-- `T_5b(5) = 0`, by Theorem 3.6 and `det M_5b(5) = 0`. -/
theorem T5b_5 : T5b 5 = 0 := by
  rw [← det_M5b_eq_T5b (by norm_num) (by norm_num : Nat.Prime 5).squarefree]
  exact det_M5b_5

/-- `T_5b(5) = 0` directly from the definition: the only block is `{5}`, of class 5. -/
theorem T5b_5_direct : T5b 5 = 0 := by
  unfold T5b
  refine Finset.sum_eq_zero fun P _ => if_neg ?_
  rintro ⟨h7, -, -⟩
  obtain ⟨B, hB⟩ := Finset.card_eq_one.1 h7
  have hBm : B ∈ P.parts.filter (fun B => dProd B % 8 = 7) := hB ▸ Finset.mem_singleton_self B
  obtain ⟨hBp, hB7⟩ := Finset.mem_filter.1 hBm
  have hne := Finpartition.nonempty_of_mem_parts P hBp
  have huniv : B = univ := by
    obtain ⟨q, hq⟩ := hne
    refine Finset.eq_univ_of_forall fun q' => ?_
    have : q' = q := Subtype.ext (by
      have h1 : (q' : ℕ) ∈ ({5} : Finset ℕ) := primeFactors_5 ▸ q'.2
      have h2 : (q : ℕ) ∈ ({5} : Finset ℕ) := primeFactors_5 ▸ q.2
      rw [Finset.mem_singleton] at h1 h2
      rw [h1, h2])
    rw [this]; exact hq
  have : dProd B = 5 := by
    rw [huniv, dProd, Finset.prod_coe_sort (5 : ℕ).primeFactors (fun p => p), primeFactors_5,
      Finset.prod_singleton]
  rw [this] at hB7
  norm_num at hB7

end ZInQ.RouteK.Rank5b

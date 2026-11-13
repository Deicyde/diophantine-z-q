# p-side results log

## P1 — ZInQKernel/Contrib/PSide/APZero.lean (compiles, no sorry; VERIFIED 2026-11-12 22:15)
- `card_solutions_eq` : over a finite field of odd char, #{(x,y): y²=g x} = #F + Σ_x χ(g x).
- `charSum_odd_eq_zero` : χ(−1) = −1 and g odd ⇒ Σ χ(g x) = 0.
- `LFunction_cd_apply_prime_eq_neg_charSum` : a_p(C_d) = −Σ_x χ(x³ − d²x)  (d odd sqfree, p ∤ 2d).
- `LFunction_cd_apply_prime_of_mod_four_eq_three` : p ≡ 3 (4), p ∤ 2d ⇒ a_p(C_d) = 0.  [P1]
- `natCard_point_cd_of_mod_four_eq_three` : #C_d(F_p) = p + 1.  [P1, point-count form]
- `LFunction_cd_apply_prime_of_mod_four_eq_three'` : same with hypothesis p ∤ d.

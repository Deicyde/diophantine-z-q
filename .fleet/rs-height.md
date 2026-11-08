# rs-height report: hypothesis H (six-contact height estimate)

Deliverable: `docs/research/rs-height.md`. Scripts: `scratch/rs-height/` (`curve.py`,
`dihedral.py`, `cmfactor.py`, `smallM.py`).

## Findings

1. **Uses.** H is consumed at exactly two Lean leaves:
   `Compiler.Precision.sixContact_at_heightPrimes` (S = S_ht, R = D; consumer
   `Assembly.ratHeight_le_bound_of_test`) and `Mult.sixContact_at_Smul` (S = S_mul,
   R = Syntax.R; consumer `Mult.slope_height_le_of` → `finite_box`). In both, u is an
   adversarial witness, and only `u ∉ 𝒞` plus a divisibility on M_S(u) is extracted, so H is
   needed for all rationals outside 𝒞.
2. **Weakest form.** One inequality implies both uses:
   H_min: `h(u) ≤ A0·M_{S_mul}(u)^24` for all u ∉ 𝒞. This uses `M_{S_mul} | M_{S_ht}` and
   `A0 ≤ A_ht`. It is the instance (S_mul, R = D) of SixContactEstimate, admissible once
   max S_mul ≤ D (a CAT consequence now, a theorem after the CAT removal).
3. **Slack.**
   - Precision: any computable bound works, including exponential or tower bounds in M,
     because A0 and the bound are an `NExpr` evaluated by the machine; only the program
     numeral changes.
   - Multiplication: the bound must be polynomial in M with exponent below the test valuation
     k = 25 (k can be raised by redesigning the template). The constant may grow until
     log2 log2 log2 T ≈ 65535; it is ≈ 9013 now. An exponential dependence on M cannot be
     absorbed, and the M-dependence itself is intrinsic (completeness forces heights to grow
     with M).
4. **Geometry (verified by computation).**
   - The u's lie on twists of a genus-17 curve (a fibre product of 5 conics, a complete
     intersection of 4 quadrics in P^5).
   - Jac ~ 15 elliptic curves (6 with j=1728, 6 with j=21952/9, 3 with j=35152/9; at least
     12 Q-isogeny classes) × Jac(y² = F(u)), which is geometrically E0² with j(E0) = 0.
   - The contacts form a hexagon: D6 ⊂ PGL2(Q) of order 12 permutes them, and J(u) is exactly
     the D6-quotient map onto X^6/W = P^1_j(4,6,2).
   - H(u) has no rational roots, so rational u never lies over the elliptic points.
   - For S = primes ≤ 13 there are 131 points with M_S = 1 (|a|, b ≤ 6000); the maximum
     height is 7.31.
5. **Obstruction to Baker.** The local tests detect valuations only mod 2. H is therefore
   uniform effective Mordell for rational points on twists of a projective curve (the compact
   Shimura orbifold pulled back by J). Baker's method needs integrality against a divisor,
   and there are no cusps. Detecting all positive valuations, which would reduce H to ternary
   S-unit equations (Stewart–Yu: h ≪ M^{1/3+ε}), is as hard as the main theorem. An
   elliptic-curve redesign (BCDT) fails because cusps give multiplicative reduction
   regardless of parity. Masser–Wüstholz bounds heights within an isogeny class; modularity
   is what supplies the explicit member J_1(N).

## Ranking

1. R1, H_min restatement in Lean. Chance: high. Payoff: small, permanent. **Recommended
   next step.** Success: the main theorem takes `SixContactMin`, the build and
   check_target pass, axioms unchanged.
2. R5.3, show the CM branch is empty for rational u. Method: Elkies' rational CM points on
   X*(6), then solve J(u) = j_Δ over Q. Chance: medium. Would remove A004/A005 and replace
   Fowler at k = D by a bounded class-number input (h ≤ 4).
3. R5.1/R5.2, citation swaps: Faltings' Tate/semisimplicity → Masser–Wüstholz; Scholze →
   Faltings/Tsuji. Chance: high. Payoff: fewer distinct leaves.
4. R2/R3/R4, Baker, S-units, per-curve Chabauty, elliptic redesign. Chance: very low, for
   the structural reasons above.

Overall: the chance of removing H or proving it without modularity is very low.

## Open questions

- Is the index-12 group Γ' of P^1_u(2^6) a congruence subgroup (level structure at the
  ramified prime 2 times an Atkin–Lehner quotient)? Is y² = F(u) a Shimura curve?
- The Q-structure of Jac(y² = F(u)): no Mordell curve y² = x³ + k with k supported on
  {2,3,5} matches its Frobenius traces, so the factors are probably defined over a quadratic
  field only.
- Which rational CM points of X^6/W have rational u-preimages (test R5.3)?

## Suggested follow-up tasks

- Lean: add `SixContactMin`, prove `SixContactEstimate → SixContactMin` (using CAT, or its
  effective replacement, for max S_mul ≤ D), and rewire the two consumers.
- Computation: R5.3. Get the rational CM values on X*(6) (Elkies' table, or compute them via
  the (2,4,6) triangle-group Hauptmodul) in the manuscript's normalization, and factor
  -57600 b F(X)² - a G(X)⁶.
- Audit: check that Masser–Wüstholz (Ann. Math. 1993) gives exactly the semisimplicity and
  Hom statements consumed in A008/A063.

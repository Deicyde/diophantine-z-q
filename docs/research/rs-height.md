# The six-contact height estimate H: uses, slack, trust leaves and cheaper routes

Status labels. **VERIFIED**: checked against the manuscript `diophantine_zq.tex` (line numbers
refer to the frozen 11/5 source), against the Lean development, or by a computation whose
script is in `scratch/rs-height/`. **STANDARD**: a published theorem, with reference.
**SPECULATIVE**: an idea or expectation that is not proved.

Notation. `𝒞 = {0,-15,-20,-24,-30,-60}`, `F(u) = ∏_{c∈𝒞}(u-c)`, `h(a/b) = log max(|a|,b)`,
`M_S(u)` = product of the primes `p ∉ S` with `v_p(u-c)` positive and odd for some `c ∈ 𝒞`.
`S_ht` = primes `≤ 324`; `S_mul = S_ht ∪ 𝓗 ∪ supp(c_*)` (manuscript line 968,
`ZInQ.Mult.S_mul`). `D = 324!·3^(256·(324!)^4)`, with `2^(2^8008) < D < 2^(2^9010)`
(`ZInQ.Size.D_bounds`). `A0 = H₆(S_ht; D)` is the precision constant
(`ZInQ.Compiler.Precision.A0`), `A_ht = H₆(S_mul; R)` the multiplication constant
(`ZInQ.Syntax.Aht`), `T = (48 A_ht)^13` the finite box.

## Summary

- H is used exactly twice: in the precision step of the value relation (instance `S = S_ht`,
  `R = D`) and in the finite-box step of multiplication soundness (instance `S = S_mul`,
  `R = Syntax.R`). In both, the rational number `u` is an adversarial witness. The Lean proof
  extracts from it only `u ∉ 𝒞` and a divisibility statement about `M_S(u)`, so H is needed
  for every rational number outside `𝒞`, not for a structured subset.
- The precision use tolerates **any** bound computable by the precision program, including
  exponential or tower-type bounds in `M`, because the constant and the bound are computed
  by the natural-number machine, not written as literals. The multiplication use needs a
  bound **polynomial** in `M` (exponent below the test valuation 25, which can be raised),
  with a constant `A` such that `log₂log₂log₂ T` stays below about 65 535. The current
  value is about 9 013. So there is enormous slack in the constant and none in the shape: an
  exponential dependence on `M` cannot be absorbed.
- The rationals `u` with given contact support lie on quadratic twists of a fixed curve of
  genus 17, a fibre product of five conics. Its Jacobian is isogenous to fifteen elliptic
  curves times the Jacobian of `y² = F(u)`, which is geometrically the square of the CM
  curve `j = 0`. The six contacts form one orbit of a dihedral group of order 12 in
  `PGL₂(ℚ)`, and the manuscript's map `J` is exactly the quotient by that group. This is
  why the problem is a statement about the compact Shimura curve `X⁶/W`.
- Baker's method cannot reach H in this architecture. The construction's local tests see
  valuations only modulo 2, which turns H into a statement about **rational** points on
  twists of a projective curve. That is effective Mordell, uniform in the twist. Baker-type
  theory bounds only S-integral points, and a compact Shimura curve has no cusps to be
  integral against. The only known effective route goes through modularity, as in the
  manuscript.
- Recommendation: restate the hypothesis in Lean as the single weakest instance that is
  actually used (one inequality, `h(u) ≤ A0·M_{S_mul}(u)^24`). Separately, test whether the
  CM branch of the proof is empty for rational `u`; if so, four trust leaves go. Removing H
  itself has a very low chance: it would need a modularity-free proof of a case of effective
  Mordell that is open.

## 1. The statement and every use

### 1.1 Statement

Manuscript Theorem 4.1 (`thm:height`, lines 404-408): for every finite prime set `S ⊇ S_ht`,
every `R ≥ max(D, max S, 10¹²)` and every `u ∈ ℚ \ 𝒞`,
`h(u) ≤ H₆(S;R)·M_S(u)^24`, with `H₆(S;R) = 2·10¹³·max(1, C_cm, Q_R^17)`,
`Q_R = R^(R·E₀)` (lines 377-401). Lean: `ZInQ.SixContactEstimate`
(`ZInQKernel/Hypotheses/Height.lean`), with `ratHeight`, `contactSet`, `contactSupport`,
`heightH6` matching the manuscript (VERIFIED by reading both).

### 1.2 Uses in Lean (VERIFIED: every occurrence of `SixContactEstimate`, `heightH6`,
`contactSupport` under `ZInQKernel/` was inspected)

The hypothesis `hH` is threaded through `Main.lean`, `Assembly/Top/Assembly.lean`,
`Assembly/Top/ValueRelation.lean` and `Multiplication/Top/Exact.lean` without being used
there. It is consumed at exactly two leaves.

**Use P (precision, value relation).**
`ZInQ.Compiler.Precision.sixContact_at_heightPrimes` applies `hH` at `S = S_ht`, `R = D`
and rewrites `H₆(D) = A0` (`A0_eq_heightH6`). Its only consumer is
`ZInQ.Assembly.ratHeight_le_bound_of_test` (`Assembly/Top/MainBranch.lean`). That lemma takes
from `Test(n, κ, t)` only `t ∉ 𝒞` and `M_{S_ht}(t) ∣ κF(n)` (`test_dvd`, manuscript Lemma
11.1, lines 6151-6200). It concludes `h(t) ≤ 𝓑(n,κ) = A0·|κF(n)|^24`.
`eq_of_close_of_test` combines this with `|t-n| < e^{-𝓑}` (`close_sound`) to get `t = n`
(manuscript lines 6236-6262).

**Use M (multiplication, finite box).** `ZInQ.Mult.sixContact_at_Smul` applies `hH` at
`S = S_mul`, `R = Syntax.R` (`Aht_eq_heightH6`). Its consumer `slope_height_le_of`
(`Multiplication/Soundness/ContactSupport.lean`) takes from the slope predicate only `t ∉ 𝒞`
and `M_{S_mul}(t)^25 ∣ f = n₁n₂ - n₃` (the local congruence). It concludes
`h(t) ≤ A_ht·|f|^{24/25}`. `finite_box_of_slopes` (`FiniteBox.lean`) feeds this into
Proposition 6.1 (`prop:box`, lines 1225-1245): 27 slopes, sums of three slopes giving the
nine coordinates, `2n²ĥ(P₀) ≤ 12A_ht|f|^{24/25} + B₀`. The result is `max|nᵢ| < T`.
`multiply_sound` uses it.

### 1.3 Uses in the manuscript

The proof of Theorem 1.1 uses H "for each of the two sets of constants" (lines 87-88 and
121-123). Use P is at lines 6102-6118 and 6243-6252 (`B(n,κ) = H₆(S_ht)|κF(n)|^24`). Use M
is at lines 1225-1245. The two sets are distinguished at lines 966-970. The constants enter
the size chapter only through `A_ht` in `T = (48A_ht)^13` (Proposition 12.1, lines
6285-6360).

### 1.4 For which u

In both uses `u` (written `t`) is an existentially quantified witness supplied by whoever
satisfies the formula, so soundness must cover the worst case. The witnesses attached to `t`
(points `H, U` in the formal groups and the pole instance) impose only **local** conditions.
Soundness uses Lemma 5.1 (`lem:pole`) and the formal-group congruences, and nothing global
about the solubility of the pole system. Proving a global restriction on which `t` pass
`Test` would require global control of that system, which is the content of PC. So H is
needed for every `t ∈ ℚ \ 𝒞` with the stated divisibility, and the divisibility is
satisfiable for every `t` by choosing `κ` or `f` divisible by `M(t)` (VERIFIED as a reading
of the Lean statements; that every such `t` really passes `Test` is not claimed). The
real-closeness condition of use P does not restrict heights.

## 2. The weakest form needed, and the slack

### 2.1 One inequality implies both uses (VERIFIED)

`M_{S_mul}(u) ∣ M_{S_ht}(u)`, since `S_ht ⊆ S_mul` and a prime counted for `S_mul` is
counted for `S_ht`. Also `A0 = H₆(D) ≤ H₆(R) = A_ht`, since `Syntax.R ≥ D` and `H₆` is
monotone in `R`. So the single statement

> **H_min.** For every `u ∈ ℚ \ 𝒞`, `h(u) ≤ A0 · M_{S_mul}(u)^24`

implies both `sixContact_at_heightPrimes` and `sixContact_at_Smul`. H_min is the instance
`S = S_mul`, `R = D` of `SixContactEstimate`. That instance is admissible once
`max S_mul ≤ D`, i.e. `H_max, c_* < D`, which the size chapter proves from the catalogue
cutoff (`Hmax_lt_D`, `cstar_lt_D`). That cutoff becomes a theorem when CAT is removed. Under
`R = D` (`R_eq_D`), `A_ht = A0` and H_min is literally the multiplication instance.

### 2.2 Use P tolerates any computable shape (VERIFIED)

The precision predicate is decided by a register machine. `A0` is computed by the machine
from the literal 324: the expression `eA` in `Compiler/Precision/CappedTest.lean` is built
from `lit`, `add`, `mul`, `max`, `pow`, `fact`. The test `4ε < 4^{-𝓑}` is decided by capped
arithmetic (`cappedBound_eq`, manuscript lines 5763-5788). The universal halting circuit is
fixed and the program is only a numeral (`|c₃| < 2^(2^24)`, `Size/Majorants/Bound.lean`). So
replacing `A0·M^24` by any monotone bound `Φ(M)` expressible as an `NExpr` in `M`, such as
`2^(2^M)` or a tower of fixed height, changes only the program and its correctness proof. It
does not change the polynomial's shape or the size chapter. What use P needs is:

> **H_P.** There is a monotone function `Φ`, computable (in practice: an `NExpr`), with
> `h(t) ≤ Φ(M_{S_ht}(t))` for every `t ∈ ℚ \ 𝒞`.

Effectivity is essential, though. The machine must certify `ε < 4^{-Φ}`, so it needs an
upper bound on `Φ` that it can compute. A Faltings-type finiteness statement with unknown
bound does not suffice.

### 2.3 Use M needs a polynomial shape (VERIFIED)

Suppose `h(t) ≤ A·M^e` for accepted slopes, and the local tests give `M^k ∣ f` (now
`k = 25`: degree-25 truncated logarithm, valuations `k_j = 25`, lines 1150-1200). Then
`h(t) ≤ A|f|^{e/k}`, and the argument of Proposition 6.1 gives, for `N = max|nᵢ| ≥ 5`,
`N^2 < 24A·N^{2e/k} + 10`, hence `N < (48A)^{k/(2(k-e))}`. With `e = 24`, `k = 25` this is
`(48A)^{12.5} < T`.

- **Shape.** The bound must satisfy `Φ(M) = o(M^k)`. Since `M` can be as large as
  `|f|^{1/k}`, an exponential bound `exp(cM)` gives `N² ≲ exp(c(2N²)^{1/k})`, which bounds
  nothing. The same holds for any bound super-polynomial in `M`. The exponent itself is not
  rigid: raising `k` (the truncation degree of `L` and the test valuations) admits any fixed
  exponent `e`, at the cost of a new multiplication template and new formal-group estimates
  (the "valuation ≥ 28" margin at lines 1150-1157 must be recomputed).
- **Constant.** The target needs `(T+1)^{2048} < 2↑↑7 = 2^(2^(2^65536))`
  (`triplePower_9014_lt_tower_seven`, upstream `NumericalTowerBounds`). So `log₂ T` may be as
  large as about `2^(2^65536 - 11)`, i.e. `log₂log₂log₂ T < 65536`. Today
  `log₂ A_ht < D^7 < 2^(2^9013)` and `T < 2^(2^(2^9013))` (`T_lt`, lines 6352-6359). In terms
  of `D`, `log₂ A` could be raised from `D^7` to about `D^(2^56000)`, but not to `2^D`.

> **H_M.** There are an exponent `e < k` and a constant `A` with
> `log₂log₂log₂ (48A)^{k/(2(k-e))+1} < 65535`, such that `h(t) ≤ A·M_{S_mul}(t)^e` for every
> `t ∈ ℚ \ 𝒞`.

### 2.4 Why the dependence on M is intrinsic (VERIFIED as an argument)

For a true triple with large `|nᵢ|`, completeness must write coordinates of height about
`2nᵢ²ĥ(P₀)` as sums of three accepted slopes. An estimate independent of `M` (the case
`M = 1`) would bound the heights of all accepted slopes, hence the indices of all accepted
triples, true ones included. So H must allow heights to grow with `M`, and soundness then
needs that growth to be sub-`M^k`. Uniformity over infinitely many twists, made precise in
Section 3.3, is therefore unavoidable. Any shape `Φ(M) = o(M^k)` works, including the
conjectural `Φ(M) ≪ log M` (abc-strength).

## 3. The manuscript's proof and its trust leaves

### 3.1 Structure (lines 409-964)

1. **Shimura curve.** Quaternion algebra of discriminant 6, maximal order `O`, principal
   polarization datum; the normalizer quotient is `P¹_j` with branch values `0, ∞, -16/27` of
   indices `4, 6, 2` (lines 409-441). The full level-3 curve `Y₃` has degree `≤ 324` over
   `P¹_j`, and a smooth proper model over `ℤ_p` for `p > 324` is obtained through Buzzard's
   models with auxiliary level 5 (lines 441-544).
2. **Pullback to `P¹_u`.** Pull back along `J(u) = -57600F²/G⁶`, using
   `G⁶ - 97200F² = H²`. The normalized cover of `P¹_u` is branched only at the six contacts,
   with index 2, so the fibre over `u` gives a field `K` of degree `≤ 324!`, unramified
   outside `T = S ∪ supp M_S(u)`, and a QM abelian surface `A/K` with good reduction outside
   `S` (lines 545-563). This is where the parity of contact valuations enters.
3. **Hom field.** `L` with `[L:ℚ] ≤ D`, unramified outside `T` (lines 564-579).
4. **CM case.** `End⁰ = M₂(k)`. Fowler's class-number bound, the CM Faltings height formula,
   a Gaudron–Rémond isogeny `E² → A` and height variation give `h_F(A) ≤ C_cm` (lines
   580-630).
5. **Non-CM case, descent.** Skolem–Noether gives a sign cocycle, which a Dirichlet character
   splits via Brauer reciprocity, giving a field `L'` with `[L':ℚ] ≤ Q·M` (lines 631-716).
6. **Modularity.** A 2-dimensional `ρ_ℓ` of `G_ℚ`, de Rham with weights `0,-1`
   (appendix lemma, lines 10939-11005), potentially semistable (Berger), odd; Pan's theorem
   at `ℓ = 5` gives a weight-2 newform `f` with `r₅ ⊂ V(A_f)` (lines 717-796).
7. **Conductor.** Local ramification bounds give `N ≤ Q·M²` (lines 796-857).
8. **Transfer.** Faltings Hom gives `A × Z ~ J₁(N)`; Javanpeykar gives
   `h_F(J₁(N)) ≤ 1.3·10⁷N^12`; Gaudron–Rémond and height variation give
   `h_F(A) ≤ Q^17 M^24` (lines 858-905). The exponent 24 is `N^12` with `N ≤ QM²`.
9. **Back to `u`.** Lin–Yang/LNY theta formula, Pazuki's theta-versus-Faltings bound and the
   rational root theorem give `h(u) ≤ 10¹³ max(1, h_F(A))` (lines 906-964).

### 3.2 Trust leaves (audit records from `docs/theorem-application-audit/`)

| Step | Imported theorem | Lines | Audit | Kind |
| --- | --- | --- | --- | --- |
| 1 | Baba–Granath, Lin–Yang: QM polarization, quotient `P¹_j`, branch data | 404-443 | A001 | explicit moduli of QM surfaces |
| 1 | Buzzard: integral models of Shimura curves; Stacks | 441-488 | A002 | moduli |
| 1 | Tame covers and branch persistence (Stacks) | 461-534 | A078 | algebraic geometry |
| 3 | Good reduction, endomorphism descent (Milne) | 520-564 | A061 | standard |
| 3 | Abelian varieties from analytic QM data (Milne) | 564-580 | A079 | standard |
| 4 | Fowler, Prop. 2.7: `h(Δ) ≤ k ⇒ √|Δ| ≤ 2k²e^{21000k²}` | 580-596 | A003, A065 | analytic number theory |
| 4 | Barquero-Sanchez et al., CM Faltings height formula | 594-630 | A004 | Chowla–Selberg type |
| 4, 8 | Gaudron–Rémond, Theorem 1.4 (isogeny estimates) | 595-630, 876-905 | A005, A015 | transcendence (Masser–Wüstholz) |
| 4, 8 | Faltings: height variation, additivity | 619-630, 894-903 | A006 | Arakelov |
| 8 | Bost lower bound via Gaudron–Rémond §9 | 893-903 | A016 | Arakelov |
| 5 | Skolem–Noether; Brauer group and class field theory (Milne) | 630-708 | A062, A007 | classical |
| 6 | Faltings: semisimplicity, Tate conjecture, Hom theorem | 712-753, 858-869 | A008, A063 | Faltings 1983 |
| 6 | Scholze, de Rham comparison (appendix); Berger, dR ⇒ pst | 718-753, 10936- | A009, A010 | p-adic Hodge theory |
| 6 | **Pan, Fontaine–Mazur for GL₂ at ℓ = 5**; Conrad, Li, Shimura | 753-775 | A011 | **modularity** |
| 6 | Compatible systems, Chebotarev | 773-796 | A064 | standard |
| 7 | Serre (local fields), Silverberg–Zarhin, formal groups | 794-850 | A012, A013, A071 | elementary local |
| 8 | Javanpeykar: Arakelov invariants of Belyi curves | 858-878 | A014 | Arakelov (Merkl) |
| 9 | Lin–Yang, Lauter–Naehrig–Yang theta formula; Pazuki | 906-961 | A017, A018 | explicit theta and Arakelov |

The core is step 6: modularity of the 2-dimensional Galois representation built from a QM
abelian surface. Steps 1-2 supply the reason a parity condition yields good reduction.
Steps 7-9 are bookkeeping around effective Arakelov estimates.

### 3.3 The Diophantine content of H (VERIFIED computations, `scratch/rs-height/curve.py`, `dihedral.py`)

Write `u = a/b` in lowest terms. For `p ∤ b`, `v_p(u-c) = v_p(a-cb)`. For `p ∣ b` all
`v_p(u-c) = -v_p(b) < 0` are ignored. So the condition `M_S(u) ∣ m` says exactly that
`a - cb ∈ ℤ_{S'}^× · ℚ^{×2}` for all six `c`, with `S' = S ∪ supp m`, and **the denominator `b`
is unconstrained**. Hence `(a:b)` comes from a rational point on a twist

`C_d :  d_c y_c² = a - c b  (c ∈ 𝒞),   d_c ∈ ℤ_{S'}^×/ℤ_{S'}^{×2},`

of a fixed curve `C`. Eliminating `a, b` exhibits `C_d` as a complete intersection of four
quadrics in `P⁵`. Equivalently, `C → P¹_u` is the `(ℤ/2)⁵`-cover obtained by adjoining
`√((u-c)/u)`, `c ≠ 0`, a fibre product of five conics branched over `𝒞`.

- **Genus 17.** Riemann–Hurwitz: `2g-2 = 32(-2) + 6·16 = 32`. Adjunction for four quadrics
  in `P⁵` gives `K = O(2)` and `2g-2 = 2·16`. The two agree.
- **Jacobian (Kani–Rosen).** The index-2 subgroups of `(ℤ/2)⁵` correspond to the 31
  nonempty even subsets `I ⊆ 𝒞`, with quotient `y² = ∏_{c∈I}(u-c)`. So
  `Jac C ~ ∏_{|I|=4} E_I × Jac(C₆)`, `C₆ : y² = F(u)`, and `15·1 + 2 = 17`. For a twist the
  factors are the corresponding quadratic twists.
  - The fifteen `E_I`: six have `j = 1728` (CM by `ℤ[i]`), six have `j = 21952/9 = 2⁶7³/3²`,
    three have `j = 35152/9 = 2⁴13³/3²` (the last two are not CM, since `j ∉ ℤ`). Over `ℚ`
    they fall into at least 12 isogeny classes (a differing trace separates them). Equal traces
    for `p < 400` within each class suggest exactly 12, which is not proved.
  - `C₆`: the L-polynomials at all `7 ≤ p ≤ 43` factor over `ℚ` into two quadratic
    factors, and for `p ≡ 2 (mod 3)` both factors are `1 ± pT²` (trace zero, supersingular).
    Over `ℚ̄`, `C₆ ≅ y² = x⁶ - 1` (next item), so `Jac C₆ ~ E₀²` with `j(E₀) = 0` over `ℚ̄` (STANDARD for `y² = x⁶ - 1`).
- **The hexagon.** Exactly twelve Möbius maps over `ℚ` permute `𝒞`. They form a dihedral
  group `D₆` (element orders 1, 2×7, 3×2, 6×2). The rotation `u ↦ -60(u+60)/(7u+240)`
  cycles the contacts and fixes the two roots of `G(u) = 7u² + 300u + 3600`, which are
  defined over `ℚ(√-3)`. **`J ∘ g = J` for all twelve maps, and `deg J = 12`, so `J` is the
  quotient map `P¹_u → P¹_u/D₆ = P¹_j`.** Under this map the contacts form the orbit over
  `j = 0` (stabilizer of order 2, ramification 2, residual orbifold index `4/2 = 2`), the
  roots of `G` lie over `j = ∞` (index `6/6 = 1`), and the roots of `H` over `-16/27`
  (index `2/2 = 1`). So `P¹_u` with six orbifold points of order 2 is a `D₆`-Galois orbifold
  cover of the Shimura orbifold `X⁶/W = P¹_j(4,6,2)`, and the orbifold Euler characteristics
  match: `12·(-1/12) = -1 = 2 - 6/2`.
- **No rational points over the elliptic points.** `H(u)` has no rational root: its quadratic
  factors have discriminants `10800, 43200, 43200`, none a square, and `disc G = -10800`. So
  for `u ∈ ℚ \ 𝒞`, `J(u)` is never one of the three elliptic values.
- **An illustration** (`smallM.py`). For `S = {2,3,5,7,11,13}`, the search
  `|a|, b ≤ 6000` finds 131 rationals with `M_S(u) = 1`, the same set as for `|a|, b ≤ 1500`.
  The largest height is `h(-1500/61) ≈ 7.31`. Denominators such as 61 are primes outside
  `S`, as predicted. The true heights are tiny compared with `H₆`.

## 4. Candidate cheaper routes

### R1. Restate the hypothesis as H_min (Lean only)

- *Idea.* Replace `SixContactEstimate` in the main theorem by H_min (§2.1), and prove
  `SixContactEstimate → H_min` from `max S_mul ≤ D`.
- *Replaces.* Nothing mathematical; the trust boundary shrinks from a family over all `(S,R)`
  to one inequality.
- *Why it works.* The two consumers need exactly the two consequences derived in §2.1.
- *Obstacle.* Under the current hypotheses `max S_mul ≤ D` uses CAT (`Hmax_lt_D`). After the
  CAT removal it is a theorem. Before that, the bridge `SixContactEstimate → H_min` may use
  CAT, which the main theorem still assumes. The bridge cannot go through the instance with
  constant `A_ht`, because `A_ht ≥ A0` is the wrong direction for the precision instance.
- *First test.* Add `def SixContactMin : Prop` and the two bridge lemmas, then rewire
  `sixContact_at_heightPrimes` and `sixContact_at_Smul`. Success: the build passes,
  `scripts/check_target.py` passes, `#print axioms` is unchanged, and the main theorem takes
  `SixContactMin`.
- *Chance.* High. *Payoff.* Small but permanent. It also makes every later replacement
  (R5, R6) a change of one statement.

### R2. Reduce H to S-unit equations (Baker)

- *Idea.* If the tests controlled **all** positive contact valuations, then `a - cᵢb` would
  be `S'`-units for three contacts, and
  `(c₂-c₃)(a-c₁b) + (c₃-c₁)(a-c₂b) + (c₁-c₂)(a-c₃b) = 0` is a ternary S-unit equation. Its
  solutions are bounded effectively and polynomially in `M`. For example, Stewart–Yu
  (Duke Math. J. 108 (2001)) give `log max ≤ c·R^{1/3}(log R)³`, `R = rad`, which yields
  `h(u) ≪ (P_S·M)^{1/3+ε}`, far below `M^24` (STANDARD). Győry–Yu give explicit S-unit
  bounds (Acta Arith. 123 (2006)).
- *Replaces.* All of §3.2 by linear forms in logarithms (Baker–Wüstholz, Yu).
- *Main obstacle (decisive).* The local tests see only `Q_p^×/Q_p^{×2}`. The pole lemma
  detects negative odd valuations, and the six tests convert odd contact valuation into a
  pole (lines 988-999, 6151-6200). An even positive valuation can always be neutralized by
  the witnesses (scale `q` so that `v_p(R₀q²) = 0`). A predicate detecting `v_p(B) ≥ 0` at
  all `p ∉ S₀`, complete on enough inputs, would make `ℤ[1/S₀]` Diophantine, which is the
  main theorem itself. Iterating square roots `L` times detects valuations not divisible by
  `2^L`. The residual problem is then rational points on twists of
  `Σ λᵢ dᵢ yᵢ^{2^L} = 0`, still a rational-points problem (SPECULATIVE but elementary to
  check).
- *First test.* Look for one local test that, for some fixed finite set of contacts, forces
  `v_p(t-c) = 0` whenever `v_p(t-c)` is even and positive. Success: such a test with a
  completeness proof on integers `t = n`. Any success would be a new Diophantine definition
  of `ℤ_{(p)}`-type sets at all primes at once.
- *Chance.* Very low.

### R3. Effective Mordell for the twists `C_d` directly

- *Idea.* Use the explicit geometry of §3.3: elliptic quotients (elliptic Chabauty, covering
  collections), the CM genus-2 quotient (Chabauty–Kim; Coates–Kim prove finiteness for
  curves with CM Jacobian without Faltings), or Runge-type arguments.
- *Why it might work.* `Jac C` is isogenous to a product of elliptic curves, eight of the
  seventeen factors CM.
- *Obstacles.* (i) Every method listed is per curve. Chabauty needs rank below genus for each
  twist, and the twist ranges over `2^{O(|S'|)}` classes, with `S_mul` containing about
  `22φ(W) ≈ 10^{131}` primes. (ii) None gives a height bound polynomial in the twist.
  Coleman's and Chabauty–Kim's bounds count points; the elliptic logarithm method and Runge's
  method bound **integral** points only. (iii) The elliptic quotients have twists of
  positive rank, so they give no finiteness. A uniform polynomial bound in the twist is
  effective Mordell for an infinite family, which is open except through modularity
  (SPECULATIVE assessment; STANDARD facts about the cited methods).
- *First test.* For `S = {2,3,5,7,11,13}` and all `(ℤ/2)`-twists, prove that the 131 points
  found are all the points, using 2-coverings of the elliptic quotients. Success: a proof for
  this `S` and a mechanism whose cost is polynomial in `|S|`. Expected: the proof is
  feasible, the mechanism is not.
- *Chance.* Very low for a uniform statement.

### R4. Redesign with modular curves and elliptic curves over ℚ

- *Idea.* Replace the QM family by elliptic curves `E_u`, so that modularity is BCDT, which
  is already a leaf of PC (A066), and use an effective Shafarevich for elliptic curves over
  `ℚ` (von Känel; Murty–Pasten), polynomial in the conductor.
- *Obstacle (decisive).* Every non-isotrivial family over `P¹_u` has cusps (poles of `j`).
  Primes where `u` is `p`-adically close to a cusp give multiplicative reduction **whatever
  the parity** of the valuation, and multiplicative reduction is an isogeny invariant. Those
  primes would enter the conductor without being controlled by `M`. Placing the cusps among
  the contacts requires the positivity tests of R2. The compactness of the Shimura curve,
  i.e. potentially good reduction everywhere, is exactly what turns parity into good
  reduction (lines 545-563). VERIFIED as an argument.
- *Chance.* Very low.

### R5. Shrink the trust leaves inside the existing proof

1. **Faltings' Tate conjecture and semisimplicity (A008, A063) → Masser–Wüstholz.** The
   isogeny theorem and semisimplicity for abelian varieties over number fields have a
   transcendence proof (Masser–Wüstholz, Ann. of Math. 137 (1993), STANDARD). That proof is
   Baker-type and is the same theory as Gaudron–Rémond (A005, A015), which is already a
   leaf. Payoff: one fewer independent deep input. Chance high (it is a citation change
   with the same statements), but careful checks of the exact statements are needed.
2. **Scholze's comparison (A009) → Faltings or Tsuji for abelian varieties.** The de Rham
   property of `V_ℓ(A)` with weights `0, -1` is classical for abelian varieties. Payoff:
   cosmetic.
3. **Remove the CM branch (A003, A004, A005, A065).** For rational `u`, a CM fibre means that
   `j = J(u)` is a **rational CM point of `X⁶/W`**. The Galois orbit of a CM point on `X⁶`
   lies in its `W`-orbit of size `≤ 4`, so `h(Δ) ≤ 4` and the class group is generated by
   the classes above 2 and 3 (SPECULATIVE in this form; the ingredients are Shimura
   reciprocity, STANDARD). The rational CM points of `X⁶/W` are tabulated (Elkies,
   *Shimura curve computations*, ANTS 1998). For `u ∈ ℚ` one then needs the rational roots
   of the twelve-degree equations `J(u) = j_Δ`. The three elliptic values have none (§3.3).
   If the other values have none either, the CM case never occurs for rational `u`.
   *First test.* Convert Elkies' table to the manuscript's coordinate (normalized by
   `0, ∞, -16/27` at `Δ = -4, -3, -24`, line 906) and factor
   `-57600bF(X)² - aG(X)⁶` for each `j_Δ = a/b`. Success: no rational roots, or an explicit
   list with explicit heights. *Obstacle.* Completeness of the CM list needs a class-number
   classification. For `h ≤ 2` this is Baker–Stark, i.e. Baker's method. For class group
   `(ℤ/2)²` it is Arno's theorem, which uses Goldfeld–Gross–Zagier, or else an effective
   bound such as Fowler's with `k = 4`, much smaller than the `k = D` used now. *Chance.*
   Medium. *Payoff.* Removes the CM height formula and the CM isogeny bound; replaces Fowler
   at `k = D` by a bounded-class-number statement.
4. **Pan (A011) → Ribet–Pyle + Khare–Wintenberger + Kisin.** The building-block structure
   makes `A` a factor of a `GL₂`-type variety over `ℚ`, modular by Serre's conjecture. This
   is the route of the replaced von Känel–Kret argument (`docs/revision-2.md`). No reduction
   in depth.

### R6. Use the freedom in the shape

- *Precision.* Any computable `Φ` works (§2.2), so a future proof that gives, say, a tower
  in `M` or a bound depending on the full factorization of `κF(n)` could be used for the
  precision step at the cost of a new `NExpr` and a new decision-correctness proof.
- *Multiplication.* Only polynomial shapes work. A worse exponent can be absorbed by raising
  the test valuation `k`; a larger constant by the size slack of §2.3.
- *Payoff.* Only relevant once some alternative proof exists. The shape freedom does not by
  itself make H cheaper, because the difficulty is uniformity in the twist (§2.4), not the
  exponent.

### R7. Change the contact set

Fewer contacts make H false: with four contacts the curve has genus 1 and positive-rank
twists, so heights are unbounded at fixed `M` (VERIFIED by the Kani–Rosen count). The 10/11
manuscript's alternatives also need an H-type estimate. Its fixed-prime congruence test
(`Cong₃`) uses a five-point estimate with `∞` among the contacts, `h(s) ≤ H·M_S(s)^c`
(10/11 PDF, Input H, p. 3, and §15). That changes the curve, not the nature of the problem.
More contacts raise the genus and keep the uniformity problem. No contact set is known that
makes H Baker-accessible.

## 5. Ranking and recommendation

| Route | Payoff | Chance | Reason |
| --- | --- | --- | --- |
| R1 (H_min in Lean) | small, permanent | high | pure refactor of two lemmas |
| R5.3 (CM branch empty for rational `u`) | removes 3-4 leaves | medium | finite computation plus a bounded class-number input |
| R5.1, R5.2 (citation swaps) | fewer distinct leaves | high | same statements, older or transcendence proofs |
| R6 (shape freedom) | enabling only | n/a | the shape is not the bottleneck |
| R2 (S-units / Baker) | would remove H | very low | the tests detect parity only; positivity detection is as hard as the theorem |
| R3 (effective Mordell for `C_d`) | would remove H | very low | per-curve methods, no uniformity in the twist |
| R4 (elliptic curves) | would replace Pan by BCDT | very low | cusps break the parity-to-good-reduction step |

**Recommendation.** The single next step is R1: introduce `SixContactMin` (H_min) and rewire
the two consumers. Success criterion: the main theorem
`exists_bounded_integer_polynomial_defining_integers_of` takes `SixContactMin` in place of
`SixContactEstimate`, the build and `check_target.py` pass, and the axioms are unchanged.
Chance: high, since both consumers already apply H at one `(S,R)` each and §2.1 gives the
two implications. In parallel, run the R5.3 computation as a cheap experiment. If the CM
case is empty for rational `u`, the manuscript's proof of H loses its CM paragraph and four
audit records.

**On removing H.** No route found makes H provable without modularity. The obstruction is
structural. The construction's local information is valuation parity, which turns H into
uniform effective Mordell for rational points on twists of a genus-17 curve, equivalently on
the compact Shimura orbifold `X⁶/W` pulled back by the dihedral quotient `J`. Baker-type
theory needs integrality against a divisor, and a compact curve with no cusps offers none.
Transcendence (Masser–Wüstholz, Gaudron–Rémond) bounds heights **within** an isogeny class.
Modularity is what supplies an explicit member, `J₁(N)`, of the class. Estimated chance that
H can be removed or proved without modularity: very low. The constant, the exponent and the
dependence on `S` all have room to spare, but the uniformity in `M` does not.

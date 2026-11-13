# rv-h-novel: adversarial review of the novel steps in the proof of Theorem 4.1

Status: research note (task rv-h-novel, 2026-11-11; task T2 of `h-map.md`). Source: the frozen
11/5 manuscript `diophantine_zq.tex` (commit 97cec7fd, sha256 `cb1148cd…792b`). "N5 Lxxx" refers to
its lines. Scripts and their outputs are in `scratch/rv-h-novel/`; the working log is
`scratch/rv-h-novel/log.md`.

Marks: **VERIFIED** means checked line by line against N5 or by an exact computation in
`scratch/rv-h-novel/`. **STANDARD** means a published theorem, with reference. No outside source
could be opened from this host, so the statement of a STANDARD result was not re-read here.
**SPECULATIVE** means an assessment.

## Verdict

Every step in scope is **correct**. Two steps are **correct after cosmetic repairs**, and none of
those repairs changes a hypothesis, a constant or an exponent. No gap, wrong constant or
circularity was found in N5 L631-716, L796-877 or the transfer L860-905. The conclusion of
Theorem 4.1, `h(u) ≤ H₆(S;R)·M_S(u)²⁴`, survives this part of the proof unchanged, and so do
`H₆(D)` and the exponent 24 as `SixContactMin` uses them. The verdict depends on the premises
supplied by N5 L441-579 (this is W2, `b11`), on Pan's theorem (h-a011) and on GR14 (W4). Those
links were outside this review's scope and are not certified here.

| # | Step (N5 lines) | Verdict |
| --- | --- | --- |
| 1 | Sign cocycle (631-664) | correct |
| 2 | Brauer step, the character χ, the bound on m (665-693) | correct (one repair adds clarity) |
| 3 | The cochain β, the quadratic cleanup, `[L':ℚ] ≤ QM` (693-716) | correct |
| 4 | ρ_ℓ is a representation; one system at 3 and 5 (720-818) | correct (only the algebra and the system paragraph were reviewed) |
| 5 | Break bound (820-834) | correct |
| 6 | Semistability and wild inertia, odd p (836-848) | correct |
| 7 | The p = 2 paragraph for β (848-865) | correct after cosmetic repairs |
| 8 | Conductor exponents and `N ≤ QM²` (866-877) | correct |
| 9 | Transfer from `J₁(N)` (860-905) | correct; the numerics are VERIFIED |

## Premises taken from earlier in the proof (not reviewed here)

The steps below use the following, and nothing else, from N5 L377-630:

- `A/K` is an abelian surface with QM by `O`.
- `L ⊇ K` is Galois over ℚ, with `d = [L:ℚ] ≤ D`, and `L` is unramified outside `T = S ∪ supp M`.
- `A` has good reduction at every place not above `S`.
- `L` defines every geometric endomorphism of `A` and every homomorphism between its conjugates.
- All conjugates of `A` are geometrically isomorphic. An isogeny would suffice, as the Astra
  descent audit already notes.
- In the non-CM case, `End⁰(A_ℚ̄) = B`.
- `2 ∈ S`, and `S ⊆ [1, R]`.

The second and third premises are exactly what W2 / route B1 of h-map must deliver.

## 1. Sign cocycle (N5 L631-664): correct

- `c(σ,τ) ∈ ℚ^×`. Since `μ_τ·ᵗb = b·μ_τ`, applying σ gives `^σμ_τ · ^{στ}b = ^σb · ^σμ_τ`.
  Hence `c` commutes with `B`, and the centralizer of `B` in `End⁰ = B` is ℚ. (VERIFIED)
- `ε ∈ {±1}`. Degree is multiplicative, `deg ^σμ_τ = deg μ_τ`, and `deg[c] = c⁴` because
  `g = 2`. So `a_σ a_τ / a_στ = 1/|c|`, and the factor is `c/|c|`. Because `μ₁ = 1`, ε is
  normalized, and it is inflated from `Gal(L/ℚ)`. (VERIFIED)
- What makes the step correct is the following. The real algebraic numbers `a_σ` enter only
  through the identity `a_σ a_τ / a_στ = 1/|c|`, whose right side is rational. That identity
  survives any embedding `C ↪ ℚ̄_ℓ`, so the choice of 4th roots after embedding is harmless.
  N5 leaves this implicit. It is not a gap.

## 2. Brauer step (N5 L665-693): correct

- `H²(G_ℚ, ±1) = Br(ℚ)[2]` by Kummer theory and Hilbert 90. (STANDARD; Milne, *Arithmetic
  Duality Theorems*, I)
- `[ε]_p = 0` for `p ∉ T`. The restriction of ε is inflated from `Gal(L_v/ℚ_p)`, which is a
  quotient of `Gal(ℚ_p^ur/ℚ_p) ≅ Ẑ`, and `H²(Ẑ, ℤ/2) = 0`. (VERIFIED reasoning; the cohomology
  fact is STANDARD)
- The local square-root criterion. A finite-order character of `ℚ_p^×` is a square if and only
  if it takes the value 1 at −1. The reason: `ℚ_p^× = ℤ × μ_{p−1} × ℤ_p` for odd p, and
  `ℤ × {±1} × ℤ₂` for p = 2. The finite-order characters of ℤ and of `ℤ_p` are 2-divisible, and
  on a cyclic group of even order the squares are exactly the characters trivial on the element
  of order 2.
  - **VERIFIED** by `c2_sqrt_criterion.py`: on 13 levels `p^k` (135 characters), ψ is the square
    of a character of level `p^{k+2}` exactly when `ψ(−1) = 1`. There were 0 mismatches.
- Agreement of local invariants. Let `ω` be the idele class character of `χ = ∏χ_q`.
  - Then `ω_p(−1) = χ_p(−1)`, because the other components are unramified at p.
  - So `δχ` is nonzero at exactly the primes of `T_−`, and the same is true of `[ε]`.
  - At ∞ the two agree by reciprocity: both have an even number of nonzero invariants.
  - The Hasse principle for `Br(ℚ)` then gives equality.
  - (VERIFIED reasoning; reciprocity and Hasse are STANDARD)
- The bound on m. The order m is the lcm of the orders of the `χ_p`. Each odd character mod p
  exists, because `p − 1` is even. So
  `m ≤ 2∏_{p∈T odd}(p−1) ≤ 2·∏_{p≤R}(p−1)·∏_{p|M}(p−1) ≤ 2R^R M`.
  This holds because `S ⊆ [1,R]` and the primes of M lie outside S. (VERIFIED)
- *Repair R1 (clarity only).* State `ω_p(−1) = χ_p(−1)` explicitly. N5 uses it in "Hence the
  boundary of χ and [ε] agree at every finite place".

## 3. The cochain β and `[L':ℚ] ≤ QM` (N5 L693-716): correct

- Take a pointwise square root `β₀` of χ, with values in `μ_{2m}`. Galois cohomology uses
  continuous cochains, so `ε·(dβ₀)⁻¹` is the coboundary of a continuous sign cochain γ. Put
  `β = β₀γ`. (VERIFIED)
- `β|G_L` is a homomorphism and is invariant under `G_ℚ`, because `ε(g,s) = ε(s,g) = 1` for
  `s ∈ G_L`. Explicitly, `β(gsg⁻¹)β(g) = β(gs) = β(g)β(s)`. (VERIFIED)
- The cleanup.
  - For `p ∉ T` we have `I_p ⊆ G_L` and `(β|I_p)² = χ|I_p = 1`.
  - For odd p, the quadratic characters of `I_p` factor through tame inertia `∏_{ℓ≠p} ℤ_ℓ(1)`,
    which has exactly one subgroup of index 2. So the quadratic Dirichlet character η of the odd
    modulus `P` kills every such restriction.
  - η is unramified on T, including at 2, so N5's "possibly at 2" is vacuous.
  - `η² = 1` and `dη = 1`.
  - (VERIFIED)
- After the cleanup, `β|G_L` has order dividing 2m. So
  `[L':ℚ] ≤ 2md ≤ 4DR^R M ≤ R^{R+2}M ≤ QM`. (VERIFIED, `c1_constants.py`)

## 4. ρ_ℓ and one system at 3 and 5 (N5 L720-730, L797-818): correct

- `ρ(σ)ρ(τ) = β(σ)⁻¹β(τ)⁻¹ε(σ,τ)·ν_στ·στ = ρ(στ)`. The representation commutes with B, so
  `ρ ≅ r ⊕ r`. On `G_{L'}` it is the Tate action. (VERIFIED)
- The system paragraph.
  - On points, arithmetic Frobenius at v is the relative Frobenius `Ā_v → Ā_v^{(p)}`.
  - The map `μ̄_σ ∘ F` is a quasi-endomorphism of `Ā_v`. Its characteristic polynomial on `V_ℓ`
    is rational and does not depend on ℓ (STANDARD; Mumford, *Abelian Varieties*, §19).
  - Chebotarev and Brauer–Nesbitt then identify `r₃` with the modular representation at λ | 3.
  - (VERIFIED reasoning)
- Out of scope: oddness, de Rham + Berger, Pan, and the twist (h-a011 / rv-h-a011, and the Astra
  descent audit).

## 5. Break bound (N5 L820-834): correct

Each of the following holds, and was VERIFIED both in the reasoning and on 15 Galois fields with
PARI's `idealramgroups` (`c3_breaks.py`; 9 fields at p = 2, 4 at p = 3, 2 at p = 5):

- `δ ≤ e − 1 + e·v_p(e)`. The terms of `f'(π)` have distinct valuations mod e (Serre, *Local
  Fields*, III §6). The bound is attained by `ℚ(ζ₃, 3^{1/3})` and `ℚ(ζ₅, 5^{1/5})`.
- `δ = Σ_{i≥0}(|G_i| − 1)` (Hilbert; Serre IV §1 Prop. 4). This was checked against
  `v_P(different)`.
- `δ/e = 1 − 1/e + ∫₀^∞(1 − |G^u|⁻¹) du`. It follows from `φ' = |G_t|/e`, and was checked in
  exact rationals.
- `u_last ≤ 2δ/e`, because the integrand is at least 1/2 below the last break.
- `2δ/e ≤ 2(1 + log₂ a!) ≤ 4a²`. This was VERIFIED on a sample of a in `c1_constants.py`. The
  inequality `log₂ a! ≤ a·log₂ a ≤ 2a² − 1` proves it in general.

What makes the bound absolute is that upper numbering passes to quotients (Herbrand). The break
of the Galois closure is therefore a break of `G_{ℚ_p}`.

## 6. Semistability and wild inertia, odd p (N5 L836-848): correct

- Let `F' = L_v(A[3])`, or `L_v(A[5])` when p = 3. Then `[F':ℚ_p] ≤ D·|GL₄(𝔽₅)|`. Here
  `G₀ = 116064000000 = |GL₄(𝔽₅)|` exactly, and `|GL₄(𝔽₃)| = 24261120 ≤ G₀` (VERIFIED,
  `c1_constants.py`).
- Raynaud's criterion with `n ≥ 3` prime to p (STANDARD; Silverberg–Zarhin 1995 Thm 3.5,
  locator checked by the Astra conductor audit) gives semistable reduction over `F'`. Hence the
  wild inertia of `F'` acts trivially on `V_ℓ` (SGA 7 IX; STANDARD).
- For `u > U₀ = 4(DG₀)²`, the group `G^u` lies in the Galois closure of `F'` and is pro-p. So it
  lies in `P_{F'} = P ∩ G_{F'}`.
- For odd p, `β²` equals χ, which is tame at p. So β has order at most 2 on the pro-p group
  `P_F`, and is therefore trivial there. (VERIFIED)

## 7. The p = 2 paragraph (N5 L848-865): correct after cosmetic repairs

- `β⁴ = (χ₂ ∘ N)² = 1` on `U_F`, because the 2-part of χ has conductor at most 4. The other
  components are unramified at 2. (VERIFIED)
- `log: U^{e+1} ≅ 𝔪^{e+1}`, because `e+1 > e/(2−1)` (STANDARD; Silverman IV.6.4). From this,
  `(U^{e+1})⁴ = U^{3e+1}`. So β is trivial on `U^{3e+1}`, and by local class field theory on
  `G_F^u` for `u > 3e`. **VERIFIED** on 9 dyadic fields with e ≤ 16: `U^{3e+1} ⊆ U⁴` modulo
  `P^n` for `n ∈ {5e+2, 6e+3}` (`c3_breaks.py`).
- The subgroup formula `G^u ∩ G_F = G_F^{ψ_{F/ℚ₂}(u)}` is true **for every u**, not only above the
  last break. This uses `H_x = G_x ∩ H` and the transitivity of ψ, which needs `F = L_v` Galois
  over `ℚ₂`; that holds because L/ℚ is Galois (Serre IV §1 Prop. 2, §3 Prop. 15).
- `max(4D², 3e) ≤ U₀` (VERIFIED).
- *Repair R2.* Replace "If `e = v_F(2) ≤ D`" with "Since …". As written it reads as a case
  hypothesis whose other case is never treated. In fact `e ≤ [L:ℚ] ≤ D` always holds.
- *Repair R3.* Cite the source of the subgroup formula, and note that it uses that `L_v/ℚ₂` is
  Galois.

## 8. Conductor exponents and `N ≤ QM²` (N5 L866-877): correct

- At `p ≤ R`: `a_p(r_ℓ) ≤ codim r^I + Sw ≤ 2 + 2U₀ = 2 + 8(DG₀)² ≤ E₀ = 10(DG₀)²`
  (VERIFIED). This uses `Sw = ∫₀^∞ codim r^{G^u} du` and the fact that `ρ_ℓ` is trivial on
  `G^u` for `u > U₀`.
- At `R < p ∈ T`, so `p | M`: `[L_v:ℚ_p] ≤ D < p`, so the extension is tame. A has good
  reduction there, so `a_p ≤ 2`.
- Outside T: `a_p = 0`.
- Carayol (STANDARD; Carayol 1986) turns this into a bound on the level. The conductor at 5 is
  computed with `r₃`, and at every other p with `r₅`. The result is
  `N ≤ ∏_{p≤R} p^{E₀}·M² ≤ R^{RE₀}M² = QM²`. (VERIFIED)
- What makes `E₀` independent of M is that the bound on β at p ≤ R uses only the local tameness
  of χ (odd p), or that `χ₂` has order at most 2 (p = 2). It never uses `[L':ℚ]`.

## 9. Transfer (N5 L860-905): correct

- Faltings' Hom theorem, absolute simplicity and Poincaré reducibility give an isogeny
  `A × Z → J₁(N)` over L'.
- The index of `Γ₁(N)` is at most `N²`, so the genus and the Belyi degree of `j` are at most `N²`.
- Javanpeykar gives `h_F(J) ≤ 13·10⁶·g·deg_B⁵ ≤ 13·10⁶·N¹²` (STANDARD; ANT 2014, Thm 1.1.1).
- GR14 Thm 1.4 (STANDARD; W4 caveat).
- The arithmetic was **VERIFIED** exactly at `Q = 10¹²` and `M ∈ {1, 2, 7}` (`c1_constants.py`).
  Every quantity is monotone in Q and M.
  - The three logarithms are at most `5QM⁴`, `2QM⁴` and `19QM⁴`.
  - `64g²·5QM⁴ + 40QM⁴ ≤ 360Q⁷M¹²`, and `1024·360 = 368640`.
  - `368640·Q¹⁶M²⁴ ≤ Q¹⁷M²⁴`.
  - `Q¹³M²⁴ + ½Q¹⁷M²⁴ + 2Q³M⁴ ≤ Q¹⁷M²⁴`.
- The direction of the GR isogeny does not matter, since the variation of height under an
  isogeny is symmetric. The normalizations of `h_F` (Faltings vs Deligne, Bost's lower bound)
  move the bounds by `O(g)`. That is absorbed by a factor of Q or more of slack, so any lower
  bound `h_F(Z) ≥ −c·dim Z` with `c ≤ Q¹⁴` suffices.

## Provenance observation (VERIFIED)

The Astra `FINAL_REVIEW.json` records `final_source_sha256 = bfc4192d…`. That is the
manuscript at repository commit 09c0c3f3 (2026-11-04), not N5. Some in-scope text first appears
later: the Herbrand-function derivation of the break bound first appears at 6f37dd99, and the
Silverman IV.6.4 sentence and the `f'(π)` identity were added after 09c0c3f3. So the recorded
hash does not identify the reviewed text of N5 L820-865. This review covers N5 directly.

## SPECULATIVE remarks

- The argument is robust. Every constant has at least a factor Q of slack, so small corrections
  to any STANDARD constant (Javanpeykar, GR14, Bost) cannot affect `H₆` or the exponent 24.
- The real remaining risk in the non-CM branch is outside this scope: the premises from
  L441-579 (W2), the application of Pan with the twist, and GR14's non-circularity (W4).

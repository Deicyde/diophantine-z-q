# el-special log

Notation: `C_d : y² = x³ − d²x`; `T_a = {d ∈ ℚ*/ℚ*² : C_d has a point with x ∈ aℚ*²}`.
By cr3-map-literature R1, `T_a = {a(a²s⁴ − 1) : s ∈ ℙ¹(ℚ)}` (classes). Route K's `Φ` for
multiplier `m` needs `N` with `N ∈ T_β` and `Nθ ∈ T_β` (cr3-map-needs L5).

## S1. Slot freedom does not change existence (algebra; cf. cr3-map-literature R3)
`∃N: N ∈ T_β ∧ Nθ ∈ T_β` ⇔ `θ ∈ T_β·T_β` ⇔ `X_{β,θ}: w² = θ(β²s⁴−1)(β²t⁴−1)` has a rational
point. The auxiliary primes of `N` (slots `q₀, r_p, r_ℓ`, F6/F7) are a choice of fibre; they
cannot create points. Any prime-structured choice of `N` only matters as a proof device.

## C1. Prime APs and explicit points (`c1_triangle_classes.py`, <1 s) — VERIFIED
- Input: coprime `2 ≤ b < a < 40`, `N = b(a−b)a(a+b)` (AP `a−b, a, a+b`, difference `b`).
- Points `x = Na/b, −Nb/a, N(a+b)/(a−b), −N(a−b)/(a+b)` lie on `C_N`: 1892/1892.
- Their abscissa classes are exactly `{±(a²−b²), ±ab}` (all cases).
- 8076 prime 3-APs (`a < 2000`): the class `a²−b²` always has exactly 2 primes; `ab` has `a`
  plus `sqf(b)`. Primality plays no role in the points (they exist for all `a, b`); a prime AP
  only restricts which classes occur. To get class `β` one needs `a²−b² ≡ β` or `ab ≡ ±β`, which
  is the conic parametrization R1/R5 again. Green–Tao adds nothing to point production.

## C2. `β` at the slope site under Proposition AP (`c2_slope_beta.py`, <1 s) — VERIFIED
- Slopes of `slopeRepresentationAP_of_goodPrimeAP` (PropAP.lean): `t₁ = u/v`, `t₂ = (A′v−u)/v`,
  `t₃ = −10`, with `u − bv` prime for `b ∈ 𝒞 ∪ {1}`.
- `R₀ = ηF(t)/(t−1)⁸` (the `ℓ₀²a²` factor is a square), `t = u/v` ⇒
  `R₀ ≡ η·Π_{c∈𝒞}(u − cv)` mod squares. Checked on 10 small `(u, v)` (7 primes each):
  `sqf|R₀|` = product of the six primes, `ω = 6`.
- `t₃ = −10`: `F(−10) = −7·10⁶`, `|R₀| ≡ 7`; with `m = 1`, `β = 7` for every instance.
- So at the slope site `β = sqf(m·Π p_c)` has six large primes (bounded `ω`, residues set by
  `(u, v)` mod small moduli), and `β = 7` at `t₃`. rs-pole §2.3's "`ω(β)` unbounded" is a
  test-site phenomenon only (`R₀ = η2730⁶F(n)`, `n` the instance integer, `t = n` forced by
  Lemma 11.2 `Test(ι(n), ι(κ), n)`).
- Consequence: bounded `ω(β)` does not remove the obstacle, since `θ = sqf(m(m − B(q)))`
  is uncontrolled at both sites; `Φ` still needs `θ ∈ T_β·T_β`.

## S2/C3. Rational multipliers: a Châtelet surface gives explicit witnesses (`c3_chatelet_multiplier.py`, ~2 s)
- **Construction (VERIFIED algebra + 30/30 exact checks).** Any `B ≠ 0`, `m₀`; `β = sqf(m₀B)`,
  `m₀B = βg²`. With `N = β` (torsion point `(β, 0)` on `C_β`), the second curve needs
  `m(m − B) ≡ β²t⁴ − 1`. For `m = m₀k²`: `(m₀k)² − βg² ∈ (β²t⁴−1)ℚ²`, i.e. a point of the
  Châtelet surface `x² − βy² = β²t⁴ − 1`. Since `β²t⁴−1 = −N(1+t√β)·(1+βt²)` and
  `1 + βt² = βY′²` on the conic `Y′² − t² = 1/β`, the point is `x = βtY′, y = Y′`.
  Family: `t = (1/(βλ) − λ)/2`, `Y′ = (1/(βλ) + λ)/2`, `k = gβt/m₀`, then
  `m(m − B) = (β²t⁴−1)(kg/Y′)²` and `x = β(βt²+1)²(kg/Y′)²` lies on `C_{β·m(m−B)}` with
  `x ∈ βℚ*²`. So `Φ_{m₀k²}(B)` holds for every `B` with explicit witnesses.
- **Soundness side (VERIFIED, exhaustive sample).** `B = c/p` (`p ∈ {331, 337, 1009}`,
  `c ∈ {1,2,3,7}`), 2304 values of `λ` each: always `v_p(k) ≤ −1`, so `v_p(m) ≤ −2 < v_p(B)`
  (cr3-map-needs L7 boundary). The explicit family exists exactly because `k` may have
  denominators; Lemma 5.1 needs `k` integral at `p > 324`.
- **Integral `k` (VERIFIED on 30 instance-like `B = b/δ²`, δ with two primes in [400, 5000]).**
  On this family `k = G(ν² − βμ²)/(2m₀δμν)` (`λ = μ/ν`, `G = √(m₀b/β)`); `k ∈ ℤ[1/S]` forces
  `μ | G`, `ν | Gβ` up to `S`-units and `ν² ≡ βμ² (mod δ′)`: finitely many `λ`. Found for 0/30
  (2512 `λ` tested).
- **Budget.** Even an integral `k` would have size about `δG` (unbounded in the instance), while
  multiplier bits give `k < 2^L` for a fixed `L`. An unbounded integer inside the pole call
  needs an existential definition of integers, which is the target itself (circular).

## S3. Barrier lemma: rationally connected witness families contradict Lemma 5.1 (argument; STANDARD inputs)
**Setting.** `P` = instance parameter space (test site: `(n, q)` and the four test points as
coordinates on `E/K₀`; slope site similarly), `B : P → 𝔸¹` the pole input, `Y → P` the pole
witness variety (Route K `polePoly` with guards, multiplier bits included). Local soundness
(rs-pole §4.3, the proof of Lemma 5.1 is `p`-adic): for `p > 324`, `y ∈ P(ℚ_p)`,
`v_p(B(y)) < 0` odd ⇒ `Y_y(ℚ_p) = ∅`.

**Lemma G.** Let `Γ ⊂ P` be a geometrically integral curve over `ℚ` with a smooth rational point
`γ₀` where `B|_Γ` has a pole of odd order `r`. Then `Y_Γ → Γ` has no section over `ℚ̄(Γ)` meeting
the guarded open part.
*Proof.* A section is defined over a number field `K`. Let `t` be a uniformizer at `γ₀` over `ℚ`,
`B = u·t^{−r}` with `u(γ₀) ∈ ℚ*`. For the (infinitely many) `p > 324` split in `K` and prime to
`u(γ₀)` and to the bad primes of the models, Hensel gives `γ ∈ Γ(ℚ_p)` with `t(γ) = p`, so
`v_p(B(γ)) = −r`, negative odd, and the section gives a point of `Y_γ(ℚ_p)` (outside the finitely
many `γ` where it meets the guard locus). Contradiction. ∎

**Corollaries.**
1. Over such `Γ`, the generic fibre of `Y_Γ` contains no geometrically rationally connected
   subvariety dominating `Γ` (Graber–Harris–Starr, JAMS 16 (2003): RC fibrations over curves have
   sections over `ℂ`; for conic and quadric bundles Tsen's theorem suffices).
2. Such curves exist and cover `P`: test site `n = c + λ` (`c ∈ 𝒞`), `q = q₀λ^{−M}`, points fixed
   with `D_j(λ=0) ≠ 0`: `R ~ λ^{3−4M}`, `RC_j² ~ λ^{1−4M}`, `Θ ~ λ^{24M−6}`, `B ~ λ^{15−52M}`
   (odd, negative for `M ≥ 1`; same exponent count as rs-pole §4.3). Varying `(c, q₀, M,
   points)` these curves pass through every point of a dense open of `P`.
3. Hence no witness construction that is uniform over the instances (they are Zariski dense in `P`)
   and given by formulas whose free parameters satisfy only rationally connected conditions
   (rational parametrizations, conics, quadrics via Hasse–Minkowski, Châtelet surfaces, any
   unirational family) can exist for the current `Φ` or for any redesign with a local soundness
   proof. C3 is an instance: its rational family yields `v_p(m) ≤ −2` exactly at the bad primes.
4. Prime tools (Dirichlet, Green–Tao, sieves) certify local or density conditions; points they
   "produce" are formulas in prime data, i.e. algebraic families in which the primes are
   parameters, so they fall under 3 unless the parameter conditions are of genus ≥ 1, where
   existence is again a rank/Sha question.
**Scope.** Not excluded: per-instance constructions not given by one algebraic family over a
dense subset of `P` (e.g. existence theorems such as CR₃, or infinitely many families indexed by
arithmetic data each covering a thin set).

## C5. Odd pole along the curves of S3 Cor. 2 (`c5_pole_order.py`, <1 s) — VERIFIED
Test-site formulas (`R₀ = 2730⁶|F(n)|`, `a₀ = 1 − R₀q²`, `W = Π(1 + R C_j²)` over `ℚ(√2)`,
`Θ = Tr W⁻¹`, `B = R/Θ²`), random fixed `D_j ∈ ℚ(√2)`, `n = c + p`, `q = q₀p^{−M}`:
`v_p(B) = 15 − 52M` in 12/12 cases (`p ∈ {1000003, 998244353}`, `c ∈ {0, −24}`, `M = 1,2,3`).

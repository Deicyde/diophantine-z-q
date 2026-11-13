# el-special: existential freedom, prime configurations and explicit points

Branch `wip/el-special` (from `wip/cr3-maps`). Scripts, outputs and the step log:
`scratch/el-special/` (`log.md`, `c1`–`c5`). Marks: **VERIFIED** (exact computation or checked
derivation; script named), **STANDARD** (published theorem, reference), **SPECULATIVE**.
No Lean was run (none was needed); no files under `ZInQKernel/` or `blueprint/` were changed.

**Question.** Can the free choices in the descent (the auxiliary primes of `n`, the multiplier
`m`, the slots, the witness `q`), together with the prime tools proved in Lean (Dirichlet,
`ZInQ.greenTaoDense`, the Selberg sieve, `goodPrimeDensity`), land every instance on curves
where positive rank is elementary, or reduce the needed curves to a finite or explicitly
parametrized set, so that CR₃ is eliminated?

**Answer.** No. Chance: **very low**. Every route below fails, each for an identified reason.
The strongest obstruction is a general barrier, Lemma G (§4). Suppose a witness construction is
uniform over the instances and is given by formulas whose free parameters satisfy only
rationally connected conditions (rational parametrizations, conics, quadrics, Châtelet surfaces).
Then it contradicts the local soundness proof of Lemma 5.1. Points produced from prime
configurations are such formulas.

## 0. Setting (from cr3-map-needs, cr3-map-literature)

- `C_d : y² = x³ − d²x`. `T_a = {d ∈ ℚ*/ℚ*² : C_d(ℚ) has a point with x ∈ aℚ*²}`.
- `T_a = {a(a²s⁴ − 1) : s ∈ ℙ¹(ℚ)}`, by cr3-map-literature R1.
- For multiplier `m`, `Φ(B)` needs `N` with `N ∈ T_β` and `Nθ ∈ T_β`, where `β = sqf(mB)` and
  `θ = sqf(m(m − B))`.
- `β` is fixed by the instance (and `m`). `θ` moves with `q`, `κ`, the shifts and `m`.
- Soundness is Lemma 5.1, used only at `p > 324` (cr3-map-needs L6). It is proved locally: for
  `y ∈ P(ℚ_p)` with `v_p(B(y)) < 0` odd, the witness variety has no `ℚ_p`-point
  (rs-pole §4.3).

## 1. Route S: slots and auxiliary primes of `n`

**Replacement statement tried.** CR3DL (cr3-map-needs W3), with the slot primes
`q₀, r_p, r_ℓ` chosen so that `C_{d₁}` and `C_{d₂}` have explicit points. For example, choose
`d₁ = b(a−b)a(a+b)` with `a−b, a, a+b` primes in AP (Green–Tao, Dirichlet).

**Result S1 (VERIFIED, algebra; compare cr3-map-literature R3).**
- `∃N : N ∈ T_β ∧ Nθ ∈ T_β` ⇔ `θ ∈ T_β·T_β` ⇔ `X_{β,θ} : w² = θ(β²s⁴−1)(β²t⁴−1)` has a rational
  point.
- Existence therefore does not depend on `N`. The slots (freedoms F6/F7) choose a fibre of
  `X_{β,θ}`; they cannot create points.
- Soundness is untouched: this route changes nothing in `Φ`.

**Experiment C1 (`c1_triangle_classes.py`, VERIFIED).**
- For `N = b(a−b)a(a+b)`, the four points `x = Na/b, −Nb/a, N(a+b)/(a−b), −N(a−b)/(a+b)` lie on
  `C_N`: 1892/1892.
- Their abscissa classes are exactly `{±(a²−b²), ±ab}`.
- Primality plays no role: the points exist for all `a, b`. Over 8076 prime 3-APs, the class
  `a²−b²` always has exactly two primes.
- So a prime configuration only restricts which classes occur. Hitting `β` requires
  `a²−b² ≡ β` or `ab ≡ ±β`, which is the conic parametrization R1/R5 again.

**Verdict.** Fails. Prime structure in `N` is a proof device for Selmer bookkeeping, not a
source of points.

## 2. Route A: the slope site after Proposition AP

**Observation C2 (`c2_slope_beta.py`, VERIFIED).**
- The slopes of `slopeRepresentationAP_of_goodPrimeAP` are `t = u/v` with `u − cv` prime. There
  `R₀ ≡ η·Π_{c∈𝒞}(u − cv)`, so `β = sqf(m·(six AP primes))`. This was checked on 10 slopes, each
  with `ω = 6`.
- The third slope `t₃ = −10` gives `F(−10) = −7·10⁶`, hence `β = 7` (with `m = 1`) for every
  instance.
- So the claim "`ω(β)` unbounded" (rs-pole §2.3) is a test-site phenomenon only. At the test
  site `R₀ = η2730⁶F(n)`, where `n` is the instance integer, and Lemma 11.2 forces `t = n`.
  SC2 forces every odd-valuation prime of `F(n)` into `β`.

**Replacement statement considered.** Use AP freedom (residues of `u, v`) to put `β` in a class
covered by a rank theorem. Two things block it:
- `θ` remains uncontrolled at both sites.
- At the test site, `β` is an arbitrary squarefree class (with the `|β| ≡ 7 (mod 8)` shape).

**Verdict.** Fails. A bounded `ω(β)` helps nothing while `θ` is free, and the test site keeps
unbounded `ω(β)`.

## 3. Route M: multipliers, and an explicit Châtelet family

**Construction (VERIFIED, algebra, plus 30/30 exact checks in `c3_chatelet_multiplier.py`).**
- Let `m = m₀k²`, `β = sqf(m₀B)` and `m₀B = βg²`. Take `N = β` (the torsion point `(β, 0)`).
- The second curve then needs `m(m − B) ≡ β²t⁴ − 1`, i.e. a point on the Châtelet surface
  `x² − βy² = β²t⁴ − 1`.
- Since `β²t⁴ − 1 = −N(1 + t√β)·(1 + βt²)`, and `1 + βt² = βY′²` on the conic
  `Y′² − t² = 1/β`, there is an explicit point `x = βtY′`, `y = Y′`. Parametrize by
  `t = (1/(βλ) − λ)/2` and `Y′ = (1/(βλ) + λ)/2`.
- Put `k = gβt/m₀`. Then `m(m−B) = (β²t⁴−1)(kg/Y′)²`, and `x = β(βt²+1)²(kg/Y′)²` lies on
  `C_{β·m(m−B)}` with `x ∈ βℚ*²`.
- So **for every `B`, `Φ_{m₀k²}(B)` holds with explicit witnesses**, provided `k` may be
  rational.

**Soundness (VERIFIED).**
- For `B = c/p` (`p ∈ {331, 337, 1009}`), over 2304 values of `λ` each, always `v_p(k) ≤ −1`.
- So `v_p(m) ≤ −2 < v_p(B)`, which is the boundary case of L7: Lemma 5.1 fails.
- In general the argument of L7 shows that soundness holds iff `v_p(m)` is even and
  `v_p(m) > v_p(B)` at every bad `p`. With `m` existential, this forces `v_p(m) ≥ 0`, i.e. `k` is
  `p`-integral.

**Completeness with integral `k` (VERIFIED, 30 instance-like `B`).**
- On this family, `k ∈ ℤ[1/S]` forces `λ = μ/ν` with `μ | G` and `ν | Gβ` (up to `S`-units), and
  `ν² ≡ βμ² (mod δ′)`. That leaves finitely many candidates.
- Found: 0/30.
- In any case an integral `k` has size about `δG`, which is unbounded. Multiplier bits give
  `k < 2^L`. An unbounded integer inside the pole call would need an existential definition of
  `ℤ`, which is the target itself.

**Experiment C4 (`c4_bounded_multiplier.py`, `c4_out.txt`, VERIFIED exact search).**
- Inputs: 30 toy test-site `B = R₀(u/w)²`, `m₀ ∈ {1,2,3,5,6,7,10,13}`, `k ≤ 256`.
- `θ = 1` occurs 0 times.
- The torsion shortcut with a point of height ≤ 20 occurs 0 times in 61440. A planted point is
  found by the same search.

**Verdict.** Fails. The multiplier gives a genuinely explicit Châtelet mechanism, but only with
denominators in `k`, and those denominators are exactly what Lemma 5.1 forbids. Integral `k`
is finite under the budget and empirically barren.

## 4. Lemma G: the barrier (argument VERIFIED; inputs STANDARD)

**Setting.**
- `P` is the instance parameter space. At the test site its coordinates are `(n, q)` and the
  four test points on `E/K₀`.
- `B : P → 𝔸¹` is the pole input, and `Y → P` is the pole witness variety (with guards and
  bits).
- Local soundness: for `p > 324`, `y ∈ P(ℚ_p)` and `v_p(B(y)) < 0` odd, we have
  `Y_y(ℚ_p) = ∅`.

**Lemma G.** Let `Γ ⊂ P` be a geometrically integral curve over `ℚ` with a smooth rational point
`γ₀` at which `B|_Γ` has a pole of odd order `r`. Then `Y_Γ → Γ` has no `ℚ̄(Γ)`-section that
meets the guarded open set.

*Proof.*
1. Suppose such a section exists. It is defined over a number field `K`.
2. Let `t` be a uniformizer at `γ₀`, and write `B = u·t^{−r}` with `u(γ₀) ∈ ℚ*`.
3. Take any `p > 324` that splits in `K` and avoids the finitely many bad primes. By Hensel there
   is `γ ∈ Γ(ℚ_p)` with `t(γ) = p`. Then `v_p(B(γ)) = −r`, which is negative and odd.
4. The section gives a point of `Y_γ(ℚ_p)`. This contradicts local soundness. ∎

**Corollaries.**
1. The generic fibre of `Y_Γ` contains no geometrically rationally connected subvariety
   dominating `Γ`. Such a subvariety would have a section over `ℂ`: Graber–Harris–Starr, *Families
   of rationally connected varieties*, JAMS 16 (2003) (STANDARD). For conic and quadric bundles,
   Tsen's theorem suffices.
2. Such curves exist and cover a dense open subset of `P`. Take `n = c + λ` (`c ∈ 𝒞`) and
   `q = q₀λ^{−M}`, with the points fixed. Then `B ~ λ^{15−52M}` (C5, `c5_pole_order.py`:
   12/12 exact `p`-adic checks).
3. **Consequence.** The instances are Zariski dense in `P`. So no witness construction can exist
   that is uniform over the instances and given by formulas whose free parameters satisfy only
   rationally connected conditions. This applies to the current `Φ` and to every redesign whose
   soundness is proved locally. Route M's family is exactly such a construction; C3(b) exhibits
   the predicted failure.
4. The prime tools certify local or density conditions. Points built from prime data are
   algebraic families with the primes as parameters, so they fall under Corollary 3. The only
   alternative is a family whose parameters satisfy genus ≥ 1 conditions, where existence is
   again a rank or Sha question.

**Scope (what Lemma G does not exclude).**
- Non-uniform, per-instance existence arguments. CR₃ (from TYZ) is one; infinitely many
  families, each covering a thin set of instances, would be another.
- Proofs of soundness that are global rather than local.

Both are outside "elementary explicit points".

## 5. Route W: steer `θ` with the witness `q` (assessed, not new)

- Landing `θ(q)` in a set where points are explicit means hitting finitely many square classes
  for any fixed height bound. That puts `q` on finitely many curves `m(m − B(q)) ∈ cℚ²` of large
  genus. Faltings gives finitely many points, and generically none lie in `U`.
- Landing `θ(q)` in all of `T_β·T_β` is a thin-set intersection question (cr3-map-literature T8)
  with no theorem behind it.
- The sieve gives almost-prime `θ`. But even `θ` with boundedly many prime factors leaves a
  Heegner-type rank statement (cr3-map-literature T3), which is not elementary.
- **Verdict.** Fails. (SPECULATIVE beyond the cited facts.)

## 6. Reduction to a finite or explicitly parametrized set of curves

- **Finite.** Impossible. At the test site `β` runs over infinitely many classes (C2 and SC2),
  and `supp β ⊆ supp N` (rs-pole §2.3). So infinitely many curves are needed.
- **Explicitly parametrized curves.** These are available: `C_N` and `C_{Nθ}`, and `X_{β,θ}`.
  But points on them in the needed generality are excluded by Lemma G.

## 7. Verdict

| Route | Replacement | Soundness | Completeness | Outcome |
| --- | --- | --- | --- | --- |
| S (slots, prime APs) | CR3DL with structured `N` | unchanged | needs `θ ∈ T_βT_β`; independent of `N` (S1) | fails |
| A (slope-site AP) | rank theorem for `β = m·Πp_c` | unchanged | `θ` uncontrolled; test site has unbounded `ω(β)` | fails |
| M (multiplier, Châtelet) | `m = m₀k²`, `k` free | breaks for rational `k` (C3b) | explicit for rational `k`; integral `k` barren and over budget (C3c, C4) | fails |
| W (steer `θ` by `q`) | `∃q: θ(q) ∈ T_βT_β` | unchanged | genus / thin-set; no theorem | fails |
| any explicit family | — | Lemma G forbids it | — | barrier |

**Chance of eliminating CR₃ along this angle: very low.**

**Strongest obstruction.** Lemma G. Local soundness forces the witness variety to be free of
rationally connected subfamilies over a covering family of curves. Hence completeness at the
instances is an arithmetic, non-explicit existence problem of genus ≥ 1, i.e. a rank / Sha
statement for `C_N` and `C_{Nθ}`, which is what CR₃ supplies.

**Useful by-products.**
- C3 is a clean, checkable demonstration of why multipliers must be integral.
- C2 shows that `β = 7` at `t₃` and that `β` has six AP primes at the AP slopes. A future
  narrowing of CR₃ could therefore be split: a slope-site part with `β` of bounded `ω` and
  controllable residues, and a test-site part.

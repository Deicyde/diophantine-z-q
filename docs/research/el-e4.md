# el-e4: testing the frozen-Θ redesign (el-gadget E4 = el-cert M1)

Branch `wip/el-e4`, from `d549dabb`. No Lean was run, and no file under `ZInQKernel/`, `blueprint/` or
another note was edited. Scripts are in `scratch/el-e4/`, and the step record is `scratch/el-e4/log.md`.
PARI 2.17 runs through cypari2. Every computation ran sequentially, each in under 15 minutes.

Marks:
- **VERIFIED**: proved here, or computed exactly (script named).
- **STANDARD**: a published theorem (reference given).
- **SPECULATIVE**: a heuristic, or an unproved step.

## 0. Verdict

**E4 does not give a better route than CR₃. Chance: very low (≲ 2%).**

| question | answer |
| --- | --- |
| (1) soundness | **Holds** (VERIFIED). It is the existing proof at `q = 0` plus `2v(a) ≤ 0`, and it costs no variables. |
| (2) local solubility | **Not forced.** On real-data proxies, 4/30 instances are obstructed for all 64 Lean multipliers by the primes found so far; the rest are upper bounds, and most should fall once the cofactors are factored. The multiplier `m = m₀k²` can repair this only through the square class `m₀`, and `k` never helps. A fixed multiplier group of F₂-rank `g` fails once `num Θ₀` has more than about `g` obstruction primes. |
| (3) global | **A Hasse principle is false for this family.** On 240 everywhere locally soluble toy quartics, 74 provably have no rational point: their Jacobian has rank 0, so they are nontrivial elements of Ш[φ]. Only 2 of 240 provably have a point, and no point of height ≤ 2000 was found on any. |
| (4) vs CR₃ | Formally incomparable, and much worse. Per instance, E4 needs a prescribed φ-Selmer class of a non-CM curve with uncontrolled conductor to come from `E(ℚ)`. That needs rank ≥ 1 together with the class avoiding Ш, and it is false for a positive proportion of choices. CR₃^Rk is a positive-rank statement for congruent-number curves `C_d` with minimal 2-Selmer group, and published theorems cover it (Kriz; Tian–Yuan–Zhang with Gross–Zagier). No published theorem covers the E4 statement. |

## 1. The design and its completeness curve

el-gadget E4 and el-cert M1 are the same redesign, with the same normalization. Θ is computed from `R₀`
instead of `R = R₀a²`:
```
W₀ = Π_j (1 + R₀C_j²),  Θ₀ = Tr W₀⁻¹,  B = R₀a²/Θ₀²,  a = 1 − R₀q²       (test site)
W_g = Π_j (1 + ℓ²R₀C_gj²), Θ₀ = Tr Σ_g W_g⁻¹, B = ℓ²a²R₀/Θ₀²             (slope site)
```
**θ = 1 witness** (VERIFIED from `Hypotheses/Pole.lean`). Suppose `c² = m(m − B)`. Take `e = A = mB` and
`z = Bc`. Then `H = A(A − B²) = mB²(m − B) = z²`. So `r₁ = 0`, `Az² = eH`, `r₂ = 0` and `w = 1/(eHz)`
satisfy `polePoly = 0`. Completeness at one pole call therefore needs a rational point on
```
C_m :  h² = m(mΘ₀² − R₀(1 − R₀q²)²)        (q free; m a multiplier)
```
The slope site gives the same family, with `Θ₀ → Θ₀/ℓ`.

**Lemma J (Jacobian and descent; VERIFIED, `s2_jacobian.py`, 20/20 random cases).** Write
`C_m : h² = aq⁴ + bq² + c` with `a = −mR₀³`, `b = 2mR₀²` and `c = m(mΘ₀² − R₀)`.
- `Jac(C_m) = E_J : y² = x(x² − 4mR₀²x + 4m³R₀³Θ₀²)`. This is the quadratic twist by `mB₀` of
  `y² = V(V² − 4B₀V + 4mB₀)`, where `B₀ = R₀/Θ₀²`.
- `C_m` is the φ-covering, for the 2-isogeny `φ : E_J → E`, of the class `c ≡ a·(ac)` (Silverman AEC
  X.4.9; STANDARD). Here `E : y² = x(x² + bx + ac)`.
- Hence `C_m(ℚ) ≠ ∅` iff `−mR₀ ∈ ⟨ac⟩·α(E(ℚ))`, where `α(x, y) = x mod ℚ*²`.
- The two "free" classes are `1` and `ac`. They correspond to `−mR₀ ∈ ℚ*²` and to the point `q = 0`. Every
  other case needs a point of infinite order of `E` in a prescribed class.

## 2. Soundness (question 1): holds, budget-neutral

The rv-cr3-elim3 review VERIFIED this by reading the Lean proofs (§1.1 there). I re-read `pole_step`
(`Assembly/Local/TestDivisibility.lean:225`) and the slope-site use.
- `Φ(B)` with `v_p(R₀) = k` odd and `p > 13` gives `2v(Θ₀) < k + 2v(a)` (`poleSoluble_no_negative_odd`,
  i.e. `poleSystem_no_negative_odd_valuation`).
- `v(a) ≤ 0` holds because `x² − R₀y²` is anisotropic when `v_p(R₀)` is odd. Hence `2v(Θ₀) < k`. This is
  exactly the hypothesis that `trace_val` and `tests_small` use with `R := R₀`, as in the original proof at
  `q = 0`.
- The slope site (`common_group_of`, step `hex`) works the same way, with `r_W = v(ℓ²R₀) = k`.
- Lean repair, as in rv-elim3: `pole_step` must be restated for a numerator `R₀a²` that differs from the
  argument of `W`. This adds one use of `2v(a) ≤ 0`.
- Guards: for `R₀ > 0`, `W₀, Θ₀ > 0` by total positivity. For the slope site with `η = −1`, this is
  unchanged from the present code.
- **Variable budget** (VERIFIED from the formulas): `R₀` replaces `R` inside `W`, and the θ = 1 witness uses
  only the existing pole witnesses and `q`. So FrozenTarget's budget is unchanged.

The redesign is sound. The question is completeness.

## 3. Local solubility (question 2): not forced, and only `m₀` matters

**Local lemmas** (VERIFIED: proofs in log Step 3b; L4 is el-cert's lemma, VERIFIED in rv-elim3 and rechecked
30/30 by `t0_locsol_check.py`). Let `p` be odd with `p ∤ mR₀`.
- L1: `v_p(R₀)` odd and honest (`2v_p(Θ₀) < v_p(R₀)`) implies soluble, via the disc `q ≡ 0`.
- L2: `v_p(Θ₀) < 0` implies soluble.
- L3: `v_p(Θ₀) = 0` and `p ≥ 13` imply soluble (Weil bound on the reduction; the singular case
  `p | mΘ₀² − R₀` reduces to a conic).
- L4: `v_p(Θ₀) ≥ 1` implies that `C_m` is soluble iff `(R₀/p) = 1` or `(−m/p) = −1`.
- L5 (rescaling): `C_{m₀k²}(Θ₀) ≅ C_{m₀}(kΘ₀)` and `C_m(Θ₀, s²R₁) ≅ C_m(Θ₀/s, R₁)`.
  - So only the square class `m₀` matters.
  - `k` only adds the primes `p | k` to `num Θ₀`, and so can create obstructions but never remove one.
  - **Within the allowed set `m = m₀k²`, the repair is a choice of `m₀` alone.**

So outside a finite set (p ≤ 11, `p | m`, primes with even `v_p(R₀)`), the only local obstructions are the
primes of the set `Obs = {p | num Θ₀ : (R₀/p) = −1}`. Each one imposes the linear condition `(−m₀/p) = −1`.

**Real-data proxies** (`s3_real_local.py`, `s3_out.json`). These are 30 test-site instances from the Lean
formulas (`k0.py`): `n = 1..5`, `κ = 1`, six shift pairs.
- `num Θ₀` has 248–1530 digits. Trial division reached `10⁷`.
- All 30 are *dishonest* at some contact prime, because the `κ = 1` tests are not deep. Honest instances
  need astronomically deep `κ` (el-cert) and cannot be computed. As in rv-elim3, the proxies stand in only
  for the arithmetic of `Θ₀`, and the odd-valuation contact primes are skipped (L1).
- `|Obs|` found per instance: 0–7.
- Number of surviving `m` among the 64 Lean multipliers, per instance:
  `8,4,16,4,16,8, 16,0,8,32,64,4, 32,16,32,2,32,16, 8,0,8,0,8,8, 2,8,8,2,8,0`.
  - 4/30 instances are already obstructed for every `m`.
  - Four further instances lose most of their `m` at `p = 2`.
- The cofactors (195–1449 digits) are unfactored, so these counts are upper bounds. The log log heuristic
  predicts about 5 more prime factors, half of them in `Obs` (SPECULATIVE). That would leave most instances
  with no locally soluble `m`, consistent with el-cert X3b and rv-elim3 c2.

**L7 group** (`s4_l7_linear.py`). Take `m₀ ∈ ⟨−1, p ≤ 324⟩`, a group of F₂-rank 68.
- The affine system is solvable on all 30 proxies.
- For `r` random obstruction primes, it is solvable 30/30 up to `r = 60`, then 26/30 at `r = 65`, 13/30 at
  `r = 68`, 4/30 at `r = 70` and 0/30 at `r = 80`.
- So any fixed finite multiplier group fails on instances with too many obstruction primes. Completeness
  would have to steer the prime factors of `Θ₀`, a value built from multiples of `P₀`, through the free
  shifts `(κ, h, s₀)`. No theorem gives such control (SPECULATIVE that it is out of reach; nothing in the
  literature comes close).
- L7 also costs about 61 witness bits per pole call (el-cert). It moves Lemma 5.1 to `p > 324`, which the
  test site does not supply (cr3-map-needs L6).

## 4. Global (question 3): the Hasse principle fails, and points are rare

**Toy instances** (`s5_global.py`, `s5_out.json`). Real `Θ₀` (hundreds of digits) makes 2-descent
impossible, since the discriminant contains `num Θ₀` and `mΘ₀² − R₀`. So the toy instances keep the Lean
`R₀ = 2730⁶F(n)`, with `n ≤ 40`, and use a random `Θ₀ = u/v` with `u, v ≤ 10⁴` that is honest at the
contact primes.
- For each of 30 instances, take the first 8 multipliers with `C_m` everywhere locally soluble. Every
  instance had more than 8. This gives 240 curves.
- Decision by Lemma J: `ellrank(E)` with `effort = 2`, then 2-saturation, then the F₂-span test. The test was
  validated in `s5_validate.py`: on 150 small curves, every curve with a found point is a hit (33/33), and no
  curve with a point fails the test.

| outcome (240 locally soluble `C_m`) | count |
| --- | --- |
| rank `E` = 0 (decided) | 75 |
| rank `E` = 1 (decided bounds) | 119 |
| rank undecided, (0,2) or (1,3) | 46 |
| `C_m(ℚ) ≠ ∅` proved (hit) | **2** (in 2 of 30 instances) |
| `C_m(ℚ) = ∅` proved (rank 0, class ∉ {1, ac}) | **74** |
| of these, PARI's unconditional `s = dim Ш(E_J)[2]/2Ш[4] > 0` | 69 |
| undecided, mostly rank 1 with generator not found | 164 |
| points with `H(q) ≤ 2000` (`hyperellratpoints`) | 0 |

**Retry** (`s7_rank1.py`, `s7_out.txt`). On 30 undecided rank-(1,1) curves, `ellrank` with `effort = 6`
(capped at 90 s per curve) found **no generator on any of them**. The generators have large height, which
fits the absence of small points. So the rank-1 cases remain undecided. Among the decided ones, hits are
2 out of 76.

**Conclusions** (VERIFIED for the counts; the extrapolation to honest data is SPECULATIVE):
- *Not a Hasse principle.* 74 of the 240 locally soluble curves are counterexamples: each is a nontrivial
  element of `Ш(E_J)[φ]`. Even everywhere local solubility, which is itself not forced (§3), would not
  suffice.
- *Not positive rank alone.* Rank ≥ 1 of `E_J` is necessary, but the specific class `−mR₀` must also lie in
  the image `α(E(ℚ))`. With the large φ-Selmer groups typical of a 2-isogeny family, a given class usually
  does not.
- *What is needed.* For every honest instance, some choice `(κ, h, s₀, m₀)` must make the class of `C_m` lie
  in `δ(E(ℚ)) ⊂ Sel^φ(E_J)`. That is a per-instance existence statement about rational points on genus-1
  curves with uncontrolled discriminant (`num Θ₀`, `mΘ₀² − R₀`).

## 5. Comparison with CR₃ (question 4)

- **CR₃^Rk** (`RouteK/Rank/Statements.lean`): for squarefree `d ≡ 5 (mod 8)` with `#Sel₂(C_d) = 8` and the
  2-adic shape `|a| ≡ 7 (mod 8)`, `C_d : y² = x³ − d²x` has positive rank.
  - It concerns CM curves, with **minimal** 2-Selmer group, in a family the gadget controls.
  - Published theorems cover it: Kriz's 2-converse (arXiv:2002.04767, Thm 10.13), or Tian–Yuan–Zhang
    (Asian J. Math. 21, 2017) with Gross–Zagier (STANDARD, as cited in the trust statement). What remains is
    only the formalization gap.
- **E4 statement**: for every honest instance, there exist `(κ, h, s₀, m₀)` with
  `−mR₀ ∈ ⟨ac⟩·α(E(ℚ))` on `E : y² = x(x² + 2mR₀²x − m²R₀³(mΘ₀² − R₀))`.
  - These curves are non-CM, with rational 2-torsion, a discriminant uncontrolled through `num Θ₀`, and
    Selmer groups that are not minimal.
  - Neither statement implies the other: the curve families are disjoint. So the two are **formally
    incomparable**.
  - In strength the E4 statement is much worse. For a fixed choice it is false in a positive proportion of
    cases (§4, Ш). For some choice it is a "steer the factorization of `Θ₀`" statement with no known
    approach.
- **Published theorems.** p-converse theorems (Skinner; W. Zhang; Kriz; Burungale–Castella–Skinner) need a
  corank-1 Selmer hypothesis. E4 cannot enforce one, because the gadget does not control the Selmer group of
  `E` (the data show Ш[2] ≠ 0 routinely). Statistical results on φ-Selmer groups in 2-isogeny families,
  such as Klagsbrun–Lemke Oliver (unbounded average of `Sel^φ`), say nothing about every instance and in
  fact predict that Ш[φ] is common. No published theorem supplies the needed statement (SPECULATIVE in the
  sense of a literature search, not a proof).

**Verdict.** E4/M1 is a sound, budget-neutral cleanup, as el-cert and rv-elim3 found. As a replacement for
CR₃ it trades a published-theorem hypothesis (CR₃, with a formalization gap) for a statement that is
unpublished, and for fixed choices provably false in many cases. **Chance: very low.**

## 6. Single next step

None for elimination. If M1 is kept as a cleanup with CR₃: check the field-2′ caveat of el-cert §2 (Lemma
P smallness of `R` inside `W` is lost when `R₀` is used), then restate `pole_step` for the numerator `R₀a²`
in Lean.

## Scripts (`scratch/el-e4/`)

- `locsol.py`: p-adic local solubility of `y² = quartic`. `t0_locsol_check.py`: its validation.
- `s2_jacobian.py`: Lemma J.
- `k0.py`: copy of el-qfree's Lean-formula implementation.
- `s3_real_local.py` (→ `s3_out.json`): real-data proxies, local solubility for the 64 multipliers.
- `s4_l7_linear.py`: the L7 F₂-system.
- `s5_validate.py`, `s5_global.py` (→ `s5_out.json`): global test. `s6_sha_check.py`: brute-force local and
  `ellrank(E_J)` cross-check. `s7_rank1.py`: rank-1 retry.
- `ref_c2.py`: copy of rv-elim3's `c2_theta0_primes.py` (reference only).

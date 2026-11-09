# The descent lemma of Route K: what the free multiplier and the free witness can do

This note studies the one missing step of Route K for pole completeness (`docs/research/rs-pole.md`
§4.1, `docs/research/rv-route-k.md` §4.4): the uniform descent lemma. It asks how far the freedom the
construction already offers goes, before auxiliary primes are needed:

- the multiplier `m`, which ranges over the 64 signed divisors of 2730;
- the witness `q`, which ranges over a nonempty open set at each call site.

The answer is negative on both counts, and the obstruction is structural. On the positive side the note
gives an exact linear-algebra form of the lemma, a structural criterion for the case without auxiliary
primes, and two necessary conditions on any auxiliary set that the slot construction must respect.

Every claim carries one of three marks.

- **VERIFIED**: checked against the manuscript or the Lean sources, proved here, or established by an
  exact computation. Scripts are in `scratch/descent-alt/`. They reuse the exact 2-Selmer code
  `scratch/rv-route-k/sel2cong.py`, which rv-route-k checked against PARI.
- **STANDARD**: a published theorem, with a reference.
- **SPECULATIVE**: an idea or expectation that is not proved.

**Notation.**

- `C_d : y² = x³ − d²x` is the congruent number curve; its Kummer map is `P ↦ (x, x − d)`.
- For an admissible `B` and a signed divisor `m` of 2730, put `β = sqf(mB)` and `θ = sqf(m(m − B))`.
  `sqf` is the signed squarefree part.
- For `n` squarefree, the *certificate* for a curve `C_d` (with `d = n` or `d = sqf(nθ)`) is one of:
  - `d ≡ ±β` modulo squares (a 2-torsion point has abscissa `±d`); or
  - `dim_{𝔽₂} Sel₂(C_d) = 3` and `β` is a first coordinate of `Sel₂(C_d)`. Kriz's theorem plus
    Poonen–Stoll then give rank one and `Ш[2] = 0`, so the class comes from a point.
- `π₁` is the projection of `Sel₂` to the first coordinate.
- `n = βn'` with `n'` the product of the auxiliary primes.
- `[x/p] ∈ 𝔽₂` is `0` if `x` is a nonzero square mod `p` and `1` otherwise.
- For the primes `p` of `d`: `λ_p = [−1/p]` and `μ_p = [2/p]`.

## Summary

1. **The lemma has an exact finite form** (Proposition 0, VERIFIED). For odd `d`, `Sel₂(C_d)` is the
   solution space of an explicit `𝔽₂`-linear system, written in the Legendre symbols of the primes of
   `d`. The system agrees with the exact descent on 600 random curves. The descent lemma is therefore a
   purely combinatorial statement about Legendre-symbol matrices, plus Dirichlet's theorem.
2. **Without auxiliary primes the class always exists locally** (Proposition A, VERIFIED).
   - `β` always lies in the 2-isogeny Selmer group of `C_{βθ}` that governs abscissas.
   - The Monsky matrix of `βθ` splits into the matrices of `β` and `θ`, coupled only off the diagonal.
   - Whether `β` is a first coordinate of `Sel₂(C_{βθ})` is one linear system `A v = r_β`.
   - If every prime of `θ` is `≡ 1 (mod 4)`, the class `(1, θ)` lies in `Sel₂(C_{βθ})`. Then
     `n = β` can never be certified.
3. **The multiplier cannot do it alone** (VERIFIED, computation).
   - Over random admissible inputs, each multiplier certifies `n = β` with frequency about 5%
     (92 of 1,920 evaluations on 30 inputs).
   - Explicit admissible `B` exist for which none of the 64 multipliers gives a certificate with
     `n = β` (§4.3).
4. **No bounded number of auxiliary primes suffices, whatever the multiplier** (Proposition B,
   VERIFIED).
   - Suppose the primes of `β` outside `S₀` are `k` primes `≡ 1 (mod 21840)` that are pairwise
     quadratic residues (an "isotropic core").
   - Then every certificate with `n' ≠ 1` needs `ω(n') ≥ k`, for every multiplier and every `q`.
   - A certificate with `n' = 1` needs `ω(θ) ≥ k`.
   - This is a counterexample to every "bounded" form of the lemma. It does not affect the
     unbounded form that Route K needs, since the auxiliary primes enter only the free witness `e`.
5. **Symmetric auxiliary sets never work** (Proposition C, VERIFIED). If all auxiliary primes are
   `≡ 1 (mod 4)` and satisfy the natural symmetric residue conditions, then `(1, n')` lies in the
   Selmer group. So some auxiliary prime must break the symmetry at a prime `≡ 3 (mod 4)`. This is the
   role of the manuscript's slot `q₀` of type `(1, 1)` (line 1047).
6. **The free witness `q` cannot be used in a proof** (SPECULATIVE assessment, with a VERIFIED part).
   - VERIFIED: `q` does not move `β`, and it moves `θ` only through the values of one fixed rational
     function.
   - SPECULATIVE: controlling the Legendre symbols of all primes of `θ(q)` is out of reach of
     current methods. Local conditions on `q` can only add primes to `θ`.
7. **The completeness argument needs no change** (VERIFIED). The number of auxiliary primes is
   invisible to `Q_pole` and to the Lean proof.
   - At the slope call site, `β` has at most six primes outside the fixed set `S_b` (the six
     pattern primes under 22P₂).
   - At the test call site, `β` is the square class of `mηF(n)` for the tested integer `n`. It is
     not under the prover's control, so the lemma must be proved in its general form.

**Strongest statement supported.** The descent lemma in the form "auxiliary primes exist, their number
depending on the instance" (SPECULATIVE, consistent with every test). A proof must use at least `k(β)`
slots, where `k(β)` is the size of an isotropic core (Proposition B). It must also break the symmetric
conditions (Proposition C). The slot construction is therefore unavoidable. §5 recommends how to write
it in the language of Proposition 0.

## 1. The statement and every use

### 1.1 Pole completeness and Route K (VERIFIED)

- PC is manuscript Theorem 5.2 (line 1001) and Lean `ZInQ.PoleCompleteness`
  (`ZInQKernel/Hypotheses/Pole.lean`). It asserts `ZInQ.PoleSoluble B` (rational solubility of
  `ZInQ.polePoly`) for every `B` with square reduced denominator, `0 < B < 1/2` and `v_p(B) ≥ 4` on
  `S₀ = {2, 3, 5, 7, 13}`.
- `grep` finds exactly two applications:
  - `ZInQ.Mult.slope_complete` (`Multiplication/Completeness/SlopeCompleteness.lean:187`; manuscript
    line 1751);
  - `ZInQ.Assembly.test_complete` (`Assembly/Local/TestCompleteness.lean:104`; Lemma 11.2,
    line 6233).
- Every other occurrence passes the hypothesis along (`Main.lean:37` and the assembly chain).
- Soundness uses only Lemma 5.1 (line 988).
- Route K replaces `x + 3ℓ` by `x + ℓ` in `Q_pole`. It then derives PC from Kriz's 2-converse for
  congruent number curves (arXiv:2002.04767v5, Theorems 10.13 and 10.17(2)), Poonen–Stoll (record
  A019), and the descent lemma below. rv-route-k checks soundness, the Lean impact (four
  definitions, one copied valuation lemma) and Kriz's hypotheses (rv-route-k §4.1, §4.3, §4.5).

### 1.2 The descent lemma (VERIFIED as the statement Route K needs)

> **DL.** For every admissible `B` there are a signed divisor `m` of 2730 and a squarefree `n` with
> `β | n` such that `C_n` and `C_{nθ}` both carry a certificate.

For `B ≠ 0, m`, `Φ_C(B)` holds as soon as `C_n` and `C_{nθ}` each have a rational point with abscissa in
`βℚ*²` (rv-route-k §4.2). The certificate is a sufficient condition for such a point. In the
manuscript, the analogous step for `E_ℓ` is the "simultaneous construction" at lines 1035–1061.

### 1.3 The instances that actually occur (VERIFIED by reading the Lean sources)

Both call sites feed PC the input `B = R₀ s(q)²`, where `q` is chosen by weak approximation. So
`β = sqf(mR₀)` depends only on `m` and the instance; `q` moves only `θ`.

- **Slope site.**
  - `R₀ = ηF(t)/(t − 1)⁸` (`slopeR0`), with `F(t) = t(t + 15)(t + 20)(t + 24)(t + 30)(t + 60)`
    (`contactPoly`).
  - The slope `t` is an input of `slope_complete`, with hypothesis `GoodSlope B₀ t`, so the proof
    cannot change it. `GoodSlope.contact` and `GoodSlope.few` say:
    - the primes `p ∉ S_b` with `v_p(t − c)` odd form a set `P` with `|P| ≤ 6`;
    - each such `p` has `v_p(t − c) = 1` and is a `GoodSlopePrime`.
  - `GoodSlopePrime` (`Hypotheses/PrimePattern.lean`) requires `r² = 2` in `ZMod p`, so
    `p ≡ ±1 (mod 8)` and `μ_p = 0`.
  - Hence the primes of `β` lie in `S_b ∪ P ∪ {2, 3, 5, 7, 13}`.
  - For pattern slopes `t = u/v`, `R₀ ≡ ηΠ_{c∈𝒞}(u − cv)` modulo squares. Under 22P₂
    (`TwoSlopePattern`) each `|u − cv|` is a good slope prime, so `β` consists of six large
    primes `≡ ±1 (mod 8)` and the primes of `m`.
- **Test site.**
  - `R₀ = η·2730⁶·F(n)` (`testR₀`), where `n` is the integer being tested, for every `n ∉ 𝒞`.
  - The shift `κ` and `q` change `Θ`, hence `θ`, but not `β`.
  - So `β` ranges over the square classes `sqf(mηF(n))`, `n ∈ ℤ`, with no bound on `ω(β)`.

## 2. The weakest form the proof needs, and the slack

**(a) Unbounded auxiliary sets.** The number of auxiliary primes is free (VERIFIED).

- `PoleSoluble` is an existential statement over rationals.
- The auxiliary primes enter only the square class of the witness `e` (`n = sqf(e)`).
- The template's degree (75) and its majorant `poleTemplate_maj` do not involve witness sizes.
- Nothing downstream bounds `e`. A descent lemma with any instance-dependent number of auxiliary
  primes suffices.

**(b) One input per instance (PC⁻ of rs-pole §2.1).** Only one `q` per instance is needed, from an
open set. The lemma may therefore be stated for the pairs `(β, θ)` that actually occur. Since `θ(q)` is
uncontrolled (§4.5), this gains nothing in a proof: the lemma has to treat `θ` as an arbitrary integer
with the properties of §3.1.

**(c) Certificates.** For each curve, one of two certificates suffices: torsion, or `dim Sel₂ = 3` with
the class `β`.

- Kriz is used only on curves with `dim Sel₂ = 3`, and only in the form
  `corank Sel_{2^∞} = 1 ⟹ rank = 1, #Ш < ∞`.
- With the TYZ variant, each such curve needs one extra bordered-determinant condition.

**(d) The multiplier.** The multiplier is used for the 2-adic class of `β`; all 64 values are allowed.

- `θ ≡ 1 (mod 8)` and `sqf(βθ) ≡ sqf(βn'θ) ≡ sqf(βn')` in `ℚ₂*/ℚ₂*²`, so both curves have the same
  root number.
- For a certificate, `|d| ≡ 5, 6, 7 (mod 8)` is needed: by 2-Selmer parity, `dim Sel₂ − 2` is odd
  exactly then (Monsky, appendix to Heath-Brown, Invent. Math. 118 (1994); STANDARD).
- In the experiments with auxiliary primes, `m` is chosen with `β` odd and `|β| ≡ 5, 7 (mod 8)`;
  16 of the 64 multipliers qualify.

## 3. The manuscript's proof and its trust leaves

### 3.1 The input pairs (VERIFIED)

Let `B` be admissible and `m` any signed divisor of 2730. Then `θ c² = 1 − βt²` for rationals `c, t`,
because `θ ≡ 1 − B/m` and `B/m ≡ β` modulo squares. The following hold:

- `θ > 0` and `θ ≡ 1 (mod 8)`, since `v₂(B/m) ≥ 3`;
- `gcd(θ, 2730) = 1`;
- `β` and `θ` have disjoint supports, because a prime of `β` has `v_p(B) > 0`;
- `(β/ℓ) = 1` for every prime `ℓ | θ`, and `(θ/p) = 1` for every odd prime `p | β`.

This is the manuscript's remark at lines 1027–1033: `θ` is a norm from `ℚ(√β)`.

### 3.2 The proof of PC, and its leaves

The proof of PC from RC is at lines 1019–1121:

1. multiplier bookkeeping;
2. the slot construction with the matrix `K`, the rank-one correction and the block
   `(D₁ C₁; C₁ᵗ 0)`;
3. the corank lemma (line 1072, Poonen–Stoll, A019);
4. RC (line 1005; Sections 7–9 and Appendices E–G);
5. the forward lemma (line 1086, A020, A066, A082);
6. rescaling.

rs-pole §3 and rv-route-k §3 list the leaves: 39 audit records used only inside RC, and the shared
records A020, A057, A065, A066, A082.

Route K's leaves are:

- Kriz (an unrefereed preprint; rv-route-k §4.3);
- Poonen–Stoll (A019);
- Dirichlet's theorem (A057) and quadratic reciprocity, for the auxiliary primes;
- 2-Selmer parity (STANDARD), which is used only to know which `d` can be certified.

With TYZ instead of Kriz, Tian–Yuan–Zhang (Asian J. Math. 21 (2017)) and Gross–Zagier–Kolyvagin
(A020) replace Kriz and Poonen–Stoll.

## 4. Results and candidate routes

### 4.1 Proposition 0: the 2-Selmer group of `C_d` as a linear system (VERIFIED)

**Setup.**

- Let `d > 0` be odd and squarefree, with primes `p₁, …, p_k`.
- Put `L_ij = [p_j/p_i]` for `i ≠ j` and `L_ii = 0`, and `A = L + diag(L·𝟏)` (Monsky's matrix).
- Write a candidate class as `a = (−1)^{a₀}2^{a₁}Πp_i^{u_i}`, `b = (−1)^{b₀}2^{b₁}Πp_i^{v_i}`.

**Statement.** `(a, b) ∈ Sel₂(C_d)` if and only if the following hold:

```
A u + D_λ v = a₀ λ + a₁ μ,        D_μ u + (A + D_λ) v = b₀ λ + b₁ μ,        a₀ = b₀,
d ≡ 1 (8): a₁ = 0, μ·u = 0, λ·v = λ·u        d ≡ 3 (8): a₁ = 0, b₀ = λ·v, b₁ = μ·u
d ≡ 5 (8): a₁ = 0, b₁ = μ·u, λ·v = λ·u       d ≡ 7 (8): a₁ = 0, μ·u = 0, b₀ = λ·v
```

**Proof.**

- *Odd `p | d`.* The local image is spanned by the torsion images `(d, 2)` and `(−1, −d)`, a space of
  dimension 2, and `#E(ℚ_p)/2E(ℚ_p) = 4`. Write classes at `p` as (valuation, residue symbol). The
  four valuation patterns of `(a, b)` give

  ```
  ρ_p(a) = u_p[d_p/p] + v_p[−1/p],        ρ_p(b) = u_p[2/p] + v_p[−d_p/p],
  ```

  where `ρ_p` is the residue symbol of the unit part and `d_p = d/p`. Both are linear, and they are
  the two displayed equations.
- *Real place.* `d > 0` gives `{(+,+), (−,−)}`, hence `a₀ = b₀`.
- *Place 2.* The images were computed from genuine 2-adic points until the dimension reached 3. For
  example, for `d ≡ 5`: `{(1,1),(1,5),(7,7),(7,3),(5,10),(5,2),(3,6),(3,14)}`. Reading off the
  `(valuation, ε, ω)` bits gives the table. The 2-adic class of `a` is `(a₁, a₀ + λ·u, μ·u)`.

**Checks.**

- `symsel.py` implements the system. `validate_symsel.py` compares it with the exact descent of
  `sel2cong.py` on 600 random odd `d` (1 to 7 primes below 2,750, all four classes mod 8).
- The dimensions agree, and so does membership of a random divisor as a first coordinate: 0
  mismatches.

### 4.2 Proposition A: the case `n = β` (VERIFIED)

Let `(β, θ)` be as in §3.1 with `β > 0` odd (the sign of `β` is immaterial, since `−1` is the first
coordinate of the torsion point `(0, 0)`). Let `d = βθ`, with prime index sets `B` and `Θ`.

**(i) `β` always lies in the abscissa Selmer group.** The quartic `N² = β(M⁴ − θ²e⁴)` is soluble
everywhere locally. It is the 2-covering for the isogeny dual to the one with kernel `(0, 0)`. Place by
place:

- at `∞`: take `e = 0`;
- at `ℓ | θ`: take `e = 0`, using `(β/ℓ) = 1`;
- at `p | β`: take `e = 1` and `M² ≡ θ (mod p)` with `v_p(M² − θ) = 1`; the unit part of
  `(M² − θ)/p` can be chosen freely;
- at `p ∤ 2βθ`: the unramified condition holds;
- at 2: take `M`, `e` odd and write `M² − θe² = (M − τe)(M + τe)` with `τ² = θ` in `ℤ₂`. Every class
  with valuation at least 4 occurs. `check_2adic.py` confirms solubility for twelve values `θ ≡ 1 (8)`
  and all sixteen 2-adic classes of `β`.

So no local condition ever obstructs a point with abscissa class `β` on `C_{βθ}`. The obstruction is
entirely global (the second descent).

**(ii) Decoupling and the exact criterion.**

- By §3.1, `L_{ΘB}𝟏_B = 0` and `L_{BΘ}𝟏_Θ = 0`. Hence

  ```
  A = ( A_β     L_{BΘ} )
      ( L_{ΘB}  A_θ    ),
  ```

  where `A_β` and `A_θ` are the Monsky matrices of `β` and of `θ` alone. The diagonals do not mix.
- Then `A 𝟏_B = 0`, and Proposition 0 with `a = β` (`a₀ = a₁ = 0`, `u = 𝟏_B`) reduces to the
  following. **`β` is a first coordinate of `Sel₂(C_{βθ})` if and only if `A v = r_β` has a solution
  `v` supported on the primes `≡ 1 (mod 4)`**, where:
  - `r_β = (0, μ_Θ)` if `β ≡ 5 (8)`;
  - `r_β ∈ {(μ_B, 0), (0, μ_Θ)}` if `β ≡ 7 (8)`;
  - for `β ≡ 1, 3 (8)` the root number is `+1` and no certificate exists.
- The certificate for `n = β` holds if and only if this system is solvable and `dim Sel₂(C_{βθ}) = 3`.
- Checked against the exact descent on 400 pairs `(B, m)`: 0 mismatches (`check_propA.py`).

**(iii) A structural obstruction.** Suppose every prime of `θ` is `≡ 1 (mod 4)`.

- Then `(1, θ) ∈ Sel₂(C_{βθ})`: put `u = 0`, `v = 𝟏_Θ`. Then `A 𝟏_Θ = 0` by decoupling,
  `D_λ 𝟏_Θ = 0`, and the 2-adic rows hold because `θ ≡ 1 (8)`.
- `(1, θ)` is not torsion. If `β` is also a first coordinate, then `dim Sel₂ ≥ 4`. So `n = β` is
  never certified.
- Checked on the 118 such pairs among the 400 above.
- More generally, by the same count, any non-torsion class `(1, b)` in `Sel₂(C_{βθ})` blocks the
  certificate.

**Heuristic size** (SPECULATIVE). `A` restricted to the columns `≡ 1 (mod 4)` has rank at most the
number of such primes. So solvability fails with probability of order `2^{−k₃}`, where `k₃` is the
number of primes `≡ 3 (mod 4)` of `βθ`. This matches the steep decline of `n = β` successes when `β`
has many such primes (§4.3).

### 4.3 The multiplier alone (VERIFIED, computation)

`e1_multiplier_stats.py` evaluates, for each of the 64 multipliers, the root number,
`dim Sel₂(C_{βθ})` and whether `β ∈ π₁`. Inputs are generated as in rv-route-k: admissible
`B = N/D²` with `v_p(N) ∈ {4, …, 7}` on `S₀`.

**Random inputs.** 30 inputs (`out_e1_random30.txt`).

- Among 1,920 multiplier evaluations, 92 were certified (4.8%).
- Another 441 had `dim Sel₂ = 3` with `β ∉ π₁`. There the extra Selmer class has another first
  coordinate, or first coordinate 1 as in Proposition A(iii) (`e1b_inspect.py` shows both kinds).
  Since `β` is always in the abscissa Selmer group (A(i)), the failure is a second-descent
  phenomenon.
- Half of the multipliers have root number `+1`, and their dimensions are even, as parity predicts.
- The number of certifying multipliers per input ranges over 0–6. Two inputs (#7 and #22) have none.
  This agrees with rv-route-k, where `n = β` sufficed for 29 of 30 inputs.

**`β` with six extra primes `≡ 3 (mod 4)`.** 10 inputs (`out_e1_p3x6.txt`).

- 15 of 640 multiplier evaluations were certified (2.3%).
- 3 of the 10 inputs (#0, #2, #5) have **no** certifying multiplier.

**Explicit inputs without any certifying multiplier** (`e7_counterexample.py`, `e11_core_check.py`).
For each of the following, all 64 multipliers fail the certificate with `n = β`:

```
B₁ = 2940617998660874091927347858922135000000 / 28396755925539315301025111067910716303889
B₂ = 17280246562649556021336818126510626680000 / 80761023146150018763106321014944171609929
B₃ = 4291211885438170688127484392173498582608618500000 / 17786998416186532268721491637667246182720797752009
```

- For `B₃` (isotropic core of size 6, §4.4), `dim Sel₂(C_{β_mθ_m})` ranges over 4–18 across the
  multipliers.
- For the multipliers with `β ∉ π₁`, `C_{βθ}` has no rational point with abscissa class `β` at all.
  For the others the certificate fails because `dim Sel₂ ≠ 3`.

So the statement "some multiplier always works without auxiliary primes" is **false at the level of
certificates**. (For the multipliers with `β ∈ π₁` and `dim Sel₂ ≥ 4`, a point with abscissa class `β` may still
exist, but no converse theorem certifies it.)

### 4.4 Proposition B: a lower bound on the number of auxiliary primes (VERIFIED)

**Setup.** Let `K = {p₁, …, p_k}` be primes with the following properties:

- `p_i ≡ 1 (mod 21840)`, where `21840 = 8·3·5·7·13`;
- `(p_i/p_j) = 1` for all `i ≠ j`.

Let `β` be squarefree with `K ⊆ supp β ⊆ K ∪ {2, 3, 5, 7, 13}`. This is what the 64 multipliers do
to an instance with core `K`.

**Proposition B.** Let `n' ≠ ±1` be squarefree and coprime to `β`. If `C_{βn'}` carries a
certificate (`dim Sel₂ = 3` and `β ∈ π₁`), then `n'` has at least `k` odd prime factors. The same
holds with `n'` replaced by `n'θ`. In particular:

- `C_{βθ}` (the case `n = β`) can be certified only if `ω(θ) ≥ k`;
- `C_{βn'θ}` can be certified only if `ω(n'θ) ≥ k`.

**Proof.** Put `d = βn'`.

1. *A necessary condition.* The first coordinates equivalent to `β` modulo torsion are `±β` and
   `±n'`. For each, the `a`-equation of Proposition 0 at `p ∈ K` (where `λ_p = 0`) reads
   `[n'/p] = 0`. So `(n'/p) = 1` for every `p ∈ K`.
2. *The family.* For `u, w ∈ 𝔽₂^K`, put `a_u = Π p_i^{u_i}` and consider the class `(a_u, a_w)`.
   - *At `p ∈ K`.* All symbols among `K`, and between `K` and `2, −1, 3, 5, 7, 13`, vanish, and
     `[n'/p] = 0`. So both equations hold.
   - *At a prime of `S₀ ∩ supp β`, and at 2.* Both coordinates are `≡ 1` locally.
   - *At the real place.* Both coordinates are positive.
   - *At an odd prime `q | n'`.* The conditions are `Σ_i u_i[q/p_i] = 0` and
     `Σ_i w_i[q/p_i] = 0`, using `p_i ≡ 1 (4)` and reciprocity.
3. *Counting.* The family has dimension at least `2(k − ω_odd(n'))` and meets the torsion trivially,
   because `d` has a prime outside `K`. So `dim Sel₂(C_d) ≥ 2(k − ω_odd(n')) + 2`. Then
   `dim Sel₂ = 3` forces `ω_odd(n') ≥ k`.
4. *The second curve.* The argument applies verbatim to `d = βn'θ`. The necessary condition
   becomes `(n'θ/p) = 1`, which for `n' = 1` holds automatically by §3.1. ∎

Odd primes `q | n'` with `[q/p_i] = 0` for all `i` (for instance `q ∈ {3, 5, 7, 13}`) impose no
condition, so the bound really counts the auxiliary primes that are "visible" to the core.

**Checks.**

- *Exhaustive* (`e4_lowerbound.py`): all symbolic data of `r` auxiliary primes (class mod 8, all
  symbols), for every odd `S₀`-part of `β`. No certificate for `k = 2`, `r ≤ 2` (16 `S₀`-parts), nor
  for `k = 3`, `r ≤ 3` (two `S₀`-parts). For `k = 2`, `r = 3` certificates exist when
  `β ≡ 1, 3, 7 (8)`. So the bound is sharp up to one.
- *On admissible inputs with core `k = 3`* (`e10_core_instance.py`, random symbolic search). The least
  `r` found per multiplier was 4–6. The only `r = 0` success came from a multiplier with
  `ω(θ_m) = 5 ≥ k`.
- *On actual curves with core `k = 6`* (`e11_core_check.py`, two inputs, all 64 multipliers, exact
  descent). No violation of `dim Sel₂(C_{β_mθ_m}) ≥ 2(6 − ω(θ_m)) + 2`, and no certified multiplier.

**Consequences.**

- No form of DL with a bounded number of auxiliary primes is true. This holds even when the
  multiplier is free, and for every `q`:
  - for `n' ≠ 1` the first curve `C_{βn'}` does not involve `θ` at all;
  - for `n' = 1` one needs `ω(θ(q)) ≥ k`.
- The manuscript's slot count (`d − 1` slots of one type plus `q₀`, with `d = ω(β)`, line 1046) is of
  the right order.
- **Does this occur at the call sites?**
  - Slope site: under 22P₂ the primes of `β` outside `S₀` are the six pattern primes, so a core has
    size at most 6. (The pattern primes are `≡ ±1 (8)`; their mutual symbols are not controlled.)
    Under 22P, `β` may also contain primes `≤ 324` and catalogue primes. The clean form above does
    not cover those; with extra primes in `β`, the family of the proof must also satisfy one
    condition per extra prime.
  - Test site: `β ≡ mηF(n)` for an arbitrary integer `n`. Whether `F(n)` contains arbitrarily large
    isotropic cores, with few other primes, is a question about prime factors of values of a sextic.
    It is plausible but not proved here (SPECULATIVE). PC as stated, for all admissible `B`,
    certainly contains such inputs.

### 4.5 The free witness `q`

**What `q` controls (VERIFIED).**

- `β = sqf(mR₀)` is independent of `q`, at both sites.
- `θ = sqf(1 − R₀s(q)²/m)`, where `s(q) = ℓ₀a/Θ` or `a₀/Θ`, with `a = 1 − R₀q²` and `Θ` the trace of
  sums of inverses of products. This is a fixed rational function of `q` of large degree. So
  `{θ(q)}` is the set of values of one function on an open set.

**Why it cannot be used in a proof** (SPECULATIVE assessment).

- The certificate for `C_{βθ}` depends on the Legendre symbols among all primes of `θ(q)`.
- Imposing extra `ℓ`-adic conditions on `q` can force a chosen prime `ℓ` to divide `θ(q)` exactly
  once. It cannot exclude the other primes, which are of the size of `θ` itself (20 digits and more).
- Proving that some value `θ(q)` has a prescribed symbol pattern is at least as hard as producing
  values of a high-degree polynomial with prescribed factorization type, which is open.
- Making `θ(q) = 1` means a rational point on a curve `m(m − R₀s(q)²) = □` of large genus.
- Heuristically, each `(m, q)` certifies `n = β` with probability around 5% on random inputs. With a
  `k`-core this falls sharply, since `ω(θ(q)) ≥ k` and further symbol conditions are needed
  (Proposition B).

**Conclusion.** The freedom in `q` neither removes the auxiliary primes nor reduces their number in
any provable way.

### 4.6 Proposition C: symmetric auxiliary sets are degenerate (VERIFIED)

**Proposition C.** Let `β > 0` be odd and squarefree, and let `n' = q₁⋯q_r` with every
`q_i ≡ 1 (mod 4)` and `gcd(n', 2β) = 1`. Suppose `(n'/p) = 1` for every prime `p | β` and
`(β/q_i) = 1` for every `i`. Then
`(1, n') ∈ Sel₂(C_{βn'})`, and `C_{βn'}` carries no certificate. The same holds for `C_{βn'θ}` if,
in addition, every prime of `θ` is `≡ 1 (mod 4)`.

**Proof.** Put `u = 0` and `v = 𝟏_Q`.

- `D_λ v = 0`.
- `(A𝟏_Q)_p = [n'/p] = 0` for `p | β`, and `(A𝟏_Q)_q = [β/q] = 0` for `q | n'`.
- The 2-adic rows reduce to `λ·𝟏_Q = 0`, in each of the four classes of `d` mod 8.
- `(1, n')` is not torsion. If `β ∈ π₁`, then `dim ≥ 4`. ∎

**What it implies for slots.**

- Necessity forces `(n'/p) = 1` at the primes `p ≡ 1 (4)` of `β`, and `(β/q) = 1` at the
  auxiliary `q ≡ 1 (4)`.
- So a certifying auxiliary set must contain a prime `≡ 3 (mod 4)`, or have `(n'/p) = −1` at some
  prime `p ≡ 3 (mod 4)` of `β`.
- If all primes of `β` are `≡ 1 (mod 4)`, a prime `≡ 3 (mod 4)` among the auxiliary primes is
  forced. This matches the manuscript's slot `q₀` with `s = [−1/q₀] = 1` (line 1047).
- In the experiments, the restricted family (all `q ≡ 1 (8)` with these conditions) never produced a
  certificate with `r ≥ 1` (`e6_family.py … sym`, 6 inputs × 16 multipliers, up to 6 primes).

### 4.7 One auxiliary prime, and greedy descent (VERIFIED, computation; conclusions SPECULATIVE)

**One auxiliary prime.**

- `e3b_first.py` (1,500 random `β`, all symbolic single primes): a single auxiliary prime can make
  `C_{βq}` good only if `s(β) = dim Sel₂(C_β) − 2` is small. That means `s ∈ {0, 2}` for
  `β ≡ 1 (8)`, `s = 0` for `β ≡ 3`, and `s = 1` for `β ≡ 5, 7`. Never for larger `s(β)`, although a
  single prime can lower `s` by up to 5 without the class condition (`e3c_drop.py`).
- `e3_one_aux_full.py` (24 pairs `(B, m)`, exhaustive): a single auxiliary prime works for 12 of the
  24 multipliers tested; for the other 12, no symbol pattern works at all.

**Greedy descent.** The potential is `Φ = φ(C_{βn'}) + φ(C_{βn'θ})`, where `φ = dim Sel₂ − 3` if
`β ∈ π₁` and `dim Sel₂ − 1` otherwise. The step adds one prime chosen by full enumeration of its
symbols (`e8_greedy.py`, `out_e8_greedy_random30.txt`, 30 inputs, one random admissible multiplier
each).

- The greedy reaches a certificate in 23 of 30 inputs, within 4 auxiliary primes; 3 of these were
  already certified with `n = β`.
- It stalls on the plateau `(φ₁, φ₂) = (1, 1)` in the other 7 (six with `β ≡ 5 (8)`, one with
  `β ≡ 7 (8)`) and stays there for 5 primes.
- For the same multiplier, random symbolic search solves all 7 with 2 or 3 auxiliary primes. So
  all 30 inputs admit a certificate for the multiplier drawn. The stall is a property of the greedy
  order, not of the instance.
- So a proof by "one prime at a time lowers `Φ`" fails as stated. A potential that sees the root
  number class, or a two-prime step, would be needed.

### 4.8 Candidate routes

**R1. Multiplier only (no auxiliary primes).**

- *Idea:* some `m` certifies `n = β`.
- *Status:* **refuted** (§4.3; Proposition B with `k > ω(θ_m)` for all `m`).
- *Would replace:* the slot construction.

**R2. The free witness `q`.**

- *Idea:* choose `q` so that `θ(q)` makes `C_{βθ}` certifiable.
- *Obstacle:* the values `θ(q)` cannot be controlled (§4.5). Proposition B still requires
  `ω(θ(q)) ≥ k(β)`.
- *First test:* none that could become a proof.
- *Chance:* very low.

**R3. A bounded number of auxiliary primes** (possibly with the best `m`).

- *Status:* **refuted** by Proposition B for PC as stated. At the slope site alone, a bound of the
  form `6 + O(1)` is not excluded.

**R4. The slot construction in the language of Proposition 0** (the main route; this is what task
pole-descent-k transposes).

- *Idea:* choose `≥ k(β)` slots, with types dictated by Propositions B and C, so that both systems
  have corank exactly one with kernel containing the class `β`.
- *Why it should work:*
  - the necessary conditions (`(n'/p) = 1` at the primes `p ≡ 1 (4)` of `β`, `(β/q) = 1` at the
    auxiliary `q ≡ 1 (4)`) give the decoupling of Proposition A(ii) at the primes `≡ 1 (mod 4)`.
    Proposition C says it must fail at some prime `≡ 3 (mod 4)`; the slot design decides where;
  - the diagonal entries at the primes of `β` are the same for both curves;
  - every input tested so far was solved (here and in rv-route-k).
- *Main obstacle:* the simultaneous corank condition for `n` and `nθ`, with `θ` arbitrary.
- *First test:* write the construction as an algorithm on symbol matrices. Run it on the core
  instances of `e10_core_instance.py`, the smooth-`θ` family of rv-route-k, and 30 random inputs.
- *Success criterion:* every output passes `good_cfg` and `sel2cong.py`, with at most
  `ω(β) + ω(θ) + 2` slots.

**R5. Reachability instead of explicit slots** (SPECULATIVE).

- *Idea:* Swinnerton-Dyer's Markov-chain analysis of 2-Selmer ranks under adding primes
  (Math. Proc. Cambridge 145 (2008)) and Kane (Algebra Number Theory 7 (2013)) show that the
  2-Selmer ranks of twists by products of many primes follow a limit law independent of the starting
  curve (STANDARD). In particular, every admissible rank is reached from any start.
- *Obstacle:*
  - DL needs two curves twisted by the same `n'`, a prescribed class, and restricted symbol data;
  - none of these is covered;
  - the greedy plateaus of §4.7 show that the chain for pairs has nontrivial structure.
- *First test:* exhaustive two-step reachability from the plateau states of §4.7.
- *Chance:* low to medium.

**R6. Change the construction.**

- *More multipliers, or extra factors `(A − cB²)` in `H` with fixed integers `c`.*
  - Soundness survives (VERIFIED by the valuation count of Lemma 5.1): for `p ∤ c` with `v_p(B) = k`
    negative and odd, the valuation of `A(A − B²)(A − cB²)` is `5k`, which is odd.
  - This adds more candidate `θ`, but leaves `β` and Proposition B untouched.
  - Not worth the change.
- *Restricting PC to the slope site.* Bounded `ω(β)` would help there, but the test site needs the
  general form, and its `β` is fixed by the tested integer.
- *Curves of another shape.* The lower bound comes from Selmer classes supported on an isotropic set
  of primes, a phenomenon common to quadratic twist families with full 2-torsion. No family was
  found that avoids it (SPECULATIVE).

**R7. TYZ instead of Kriz.**

- *Idea:* use the published converse; each curve also needs Smith's bordered determinant.
- *Status:* rv-route-k solved 60 of 60 inputs with it.
- *Obstacle:* the slots must also satisfy one more condition per curve. Propositions B and C apply
  unchanged.

## 5. Ranking and recommendation

| Rank | Route | Gain | Chance |
| --- | --- | --- | --- |
| 1 | R4: slot construction in the language of Proposition 0, with at least `k(β)` slots of the types forced by Proposition C | proves DL, hence PC from Kriz | medium |
| 2 | R7: R4 plus one bordered determinant per curve (TYZ) | only published deep inputs | medium-low |
| 3 | R5: reachability (Markov chain) proof of existence | existence without explicit slots | low-medium |
| 4 | R3 restricted to the slope site | bounded slots there | irrelevant while the test site needs the general form |
| 5 | R1, R2 | none | refuted / very low |

**Recommendation.** Write the slot construction directly in the linear system of Proposition 0 and the
block form of Proposition A(ii). It should treat `θ` as an arbitrary integer satisfying §3.1. A
plausible design (SPECULATIVE) uses:

- `ω(β) + O(1)` slots `≡ 1 (mod 8)` to kill the `β`-block (Proposition B shows that about `k(β)` are
  necessary);
- one slot `≡ 3 (mod 4)` to break the symmetric class `(1, n')` (Proposition C);
- free symbols of the slots at the primes of `θ` to make the `θ`-block nonsingular. This is the
  manuscript's argument "the determinant's full-product coefficient is one" (line 1052).

Test it as described under R4.

- *Success criterion:* a written proof, together with an implementation of the choice of symbols that
  certifies every test input (30 random inputs, the core instances with `k = 3` and `k = 6`, and the
  smooth-`θ` family) under the exact descent.
- *Chance: medium.*
  - For: the deep input fits; the problem is now an explicit finite one in `𝔽₂`-linear algebra; and
    the manuscript carried out the analogous argument for `E_ℓ`.
  - Against: the propositions here show that the construction cannot be shortcut. It needs
    unboundedly many slots and a symmetry-breaking slot, and both curves must be handled at once
    with `θ` uncontrolled. The greedy plateaus of §4.7 show that the order of the choices matters.

## Scripts (in `scratch/descent-alt/`)

| Script | Purpose | Output |
| --- | --- | --- |
| `common.py` | generators of admissible inputs, `β`, `θ`, certificates (exact descent of `sel2cong.py`) | |
| `symsel.py`, `validate_symsel.py` | Proposition 0 and its check (600 curves) | |
| `auxsym.py` | symbolic auxiliary primes (class mod 8, symbols; reciprocity) | |
| `check_2adic.py`, `check_propA.py` | Proposition A(i) at 2; Proposition A(ii), (iii) on 400 pairs | |
| `e1_multiplier_stats.py`, `e1b_inspect.py` | the multiplier alone | `out_e1_random30.txt`, `out_e1_p3x6.txt` |
| `e7_counterexample.py`, `e11_core_check.py` | inputs without a certifying multiplier; Proposition B on actual curves | `out_e11_core6.txt` |
| `e2_one_aux.py`, `e3_one_aux_full.py`, `e3b_first.py`, `e3c_drop.py` | one auxiliary prime | |
| `e4_lowerbound.py`, `e10_core_instance.py` | Proposition B, exhaustive and on admissible inputs | |
| `e6_family.py` | random auxiliary sets, free and symmetric (Proposition C) | |
| `e8_greedy.py` | greedy descent on the potential `Φ` | `out_e8_greedy_random30.txt` |

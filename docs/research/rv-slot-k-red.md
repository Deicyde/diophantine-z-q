# Referee report on the slot construction for the descent lemma: counterexamples and edge cases

This report examines the proof of the descent lemma DL in `docs/research/slot-k.md` §2, together
with the input pairs of `docs/research/descent-alt.md` §3.1 and the Selmer system of descent-alt
Proposition 0. Its focus is adversarial: to find admissible inputs on which a choice prescribed by
the construction is impossible, or on which the curves it produces fail the certificate. Every step
was rechecked by hand, and the construction was reimplemented from the text of slot-k §2.4 and run
against an exact 2-Selmer computation written from the definition (independent of Proposition 0
and of the code of slot-k and descent-alt).

## Verdict

**DL is proved as written.** The construction has no counterexample (its proof is correct), and the
adversarial search found none.

- **Every step holds.** Each step of slot-k §2, together with the input properties (θ1)–(θ4) and
  the parts of Proposition 0 that the proof uses (odd places, real place, place 2 for `d ≡ 5 (mod 8)`),
  is CORRECT. No GAP was found.
- **No prescribed choice can be impossible.** Every slot condition is a residue or non-residue
  condition modulo a distinct prime, plus a class mod 8. This holds in all the edge cases:
  `θ = 1`; `ω(β) = 1`; primes of `β` all `≡ 3 (mod 4)`; `P ⊆ {3, 5, 7, 13}`; either sign of `β`;
  every choice of `p₀`; slots as small as `q₀ = 3`.
- **The produced curves never failed the certificate.** On 363 runs over 16 adversarial families
  of admissible inputs (including isotropic cores and both call sites), both curves were certified
  every time by an exact 2-Selmer computation independent of Proposition 0. The theorem also holds
  on every abstract configuration with `|P| + |T| ≤ 5` except `(|P|, |T|) = (5, 0)` (exhaustive,
  117,076 cases), and on 6,000 random configurations with `|P| ≤ 6`, `|T| ≤ 5`.

The findings are minor and none needs a repair for correctness (§3):

- **F1.** One prescribed condition, `[q₀/ℓ] = 0` for `ℓ ∈ T`, is superfluous, and the stated reason
  for it is wrong.
- **F2.** The comparison with Proposition B ("within one of the bound") is overstated.
- **F3–F5.** Remarks: every other condition is load-bearing; small slots are allowed; an unused
  by-product of the input argument.

Outside the scope of this report (UNCHECKED here): the deep input (Kriz's 2-converse with
Poonen–Stoll, or TYZ), and the passage from the two points to `PoleSoluble` (rv-route-k §4.2).

## Marks

Each step examined is marked:

- **CORRECT**: checked here, by hand or by an exhaustive computation;
- **GAP**: missing or wrong, with what fails and whether it can be repaired;
- **UNCHECKED**: not examined here.

## 1. Setting

**Notation** (as in slot-k). `C_d : y² = x³ − d²x`; Kummer map `P ↦ (x, x − d)`. For an admissible
`B` and a signed divisor `m` of 2730, `β = sqf(mB)` and `θ = sqf(m(m − B))`. `[x/p] ∈ 𝔽₂` is the bit
of the Legendre symbol, `λ_p = [−1/p]`, `μ_p = [2/p]`. `P` and `T` are the prime sets of `|β|` and
`θ`, `s = [β < 0]`, `x = s + 1`.

**DL.** For every admissible `B` there are `m` and a squarefree `n` with `β | n` such that `C_n` and
`C_{nθ}` both carry a certificate: `dim_{𝔽₂} Sel₂ = 3` and `β ∈ π₁(Sel₂)` (or a torsion
certificate, which the construction never uses).

**The construction** (slot-k §2.4). Choose `m` with `β` odd and `|β| ≡ 7 (mod 8)`; fix `p₀ ∈ P`;
choose a prime `q₀ ≡ 3 (mod 8)` with `[q₀/p] = 1 + λ_p x` for `p ∈ P ∖ {p₀}`, `Σ_{p∈P} [q₀/p] = x`
and `[q₀/ℓ] = 0` for `ℓ ∈ T`; glue primes `r_p ≡ 1 (mod 8)` (`p ∈ P ∖ {p₀}`) linked exactly to `p`
and `p₀`; glue primes `r_ℓ ≡ 1 (mod 8)` (`ℓ ∈ T`) linked exactly to `ℓ` and `q₀`; and
`n = β q₀ Π r_p Π r_ℓ`.

## 2. Step-by-step audit

### 2.1 The input pairs (slot-k §1.1, descent-alt §3.1)

- **Step 0, existence of the multiplier.** CORRECT. `v₂(m) ∈ {0, 1}` is chosen with
  `v₂(m) ≡ v₂(B) (mod 2)`. A prime of `m` that also divides the odd squarefree kernel `b` of `B`
  cancels in `sqf(mB)`, but it contributes an odd square to `m_odd · b`, so
  `|β| ≡ |m_odd| · b (mod 8)` still holds. The odd parts `1, 3, 5, 7` of divisors of 2730 cover all
  classes. For each `B` exactly 8 of the 64 multipliers qualify: 4 odd parts of each class, times
  two signs. `P ≠ ∅` because `|β| ≠ 1`.
- **(θ1).** CORRECT. `v_p(B/m) ≥ 3` on `S₀`, so `1 − B/m` is `≡ 1 (mod 8)` and a unit square at
  `3, 5, 7, 13`; `0 < 1 − B/m` since `|B/m| ≤ B < 1/2`. The proof gives slightly more than (θ1)
  states: `(θ/p) = 1` for `p ∈ {3, 5, 7, 13}`. The construction does not need this. It matters only
  when admissible inputs with a prescribed `θ` are generated: `θ` must then be a square at these
  primes.
- **(θ2), (θ4).** CORRECT. At an odd `p | β` the valuation `v_p(B/m)` is odd. If `p | m`, then
  `p ∈ S₀` and `v_p(B/m) ≥ 3`. If `p ∤ m`, an odd negative valuation would contradict the square
  denominator. So `v_p(B/m) > 0`, and `1 − B/m` is a `p`-adic unit square.
- **(θ3).** CORRECT. At `ℓ | θ` (odd, `ℓ ∤ 2730`) the valuation of `1 − βt²` is odd. This forces
  `v_ℓ(βt²) = 0` and `βt² ≡ 1 (mod ℓ)`; since `v_ℓ(t²)` is even, `ℓ ∤ β` and `(β/ℓ) = 1`.
- On every admissible input generated for this report (§4), all four properties were checked
  directly on the factored `β` and `θ`. No violation occurred.

### 2.2 The Selmer system (slot-k §2.1, descent-alt Proposition 0)

- **Odd places.** CORRECT. `#C_d(ℚ_p)/2 = 4`, and the torsion images `(d, 2)`, `(−1, −d)` are
  independent at `p | d`. The four valuation patterns give the residue rules
  `ρ(a) = u_p[d_p/p] + v_p[−1/p]` and `ρ(b) = u_p[2/p] + v_p[−d_p/p]`. Expanding the unit parts of
  `a = (−1)^{a₀}2^{a₁}Π x^{u_x}` and `b` gives exactly `E1_p` and `E2_p`, with the diagonal of `K`
  coming from `[d_p/p] = Σ_{x≠p} [x/p]`.
- **Real place.** CORRECT (`d > 0`: image `{(+,+), (−,−)}`).
- **Place 2, `c = 5`.** CORRECT. `C_d ≅ C_5` over `ℚ₂` by a scaling that preserves Kummer classes.
  The generators `(5, 2)`, `(−1, −5)` and `(1, 5)` (from `x = 1/4`: `x(x − 5)(x + 5) = −399/64`, and
  `−399 ≡ 1 (mod 8)`) have bits `(0,0,1|1,0,0)`, `(0,1,0|0,1,1)` and `(0,0,0|0,0,1)`. They are
  independent, and `#C(ℚ₂)/2 = 8`, so they span the image. That span is cut out by
  `a_v = 0`, `a_ε = b_ε`, `b_v = a_ω`, which with `(R)` are the rows of `(D)` for `c = 5`.
- **Place 2, `c = 1, 3, 7`.** Not used by the proof. Every configuration in the proof, virtual or
  actual, has `c = 5`, because the glue primes and `θ` are `≡ 1 (mod 8)` and `7 · 3 ≡ 5`. These rows
  were nonetheless checked by computation (§4.1): the system agrees with the definition-based
  descent on 600 curves in all four classes.
- **Virtual configurations.** CORRECT. For virtual configurations `Σ(𝒞)` is a definition. Lemmas 1
  and 2 are statements about these linear systems. Proposition 0 is applied only to the actual
  `d₁ = |n|`, `d₂ = |n|θ`, both `≡ 5 (mod 8)`.

### 2.3 The lemmas (slot-k §2.2, §2.3)

- **Lemma 1 (partner).** CORRECT. `E1_r` and `E2_r` force `u_r = u_y` and `v_r = v_y`. The only
  other occurrence of `u_r` is the term `[r/y](u_r + u_y)` in `E1_y`, and that term then vanishes.
  `λ_r = μ_r = 0`, so `(D)` and `c` are unchanged.
- **Lemma 2 (gluing).** CORRECT. Steps 1–4 were redone by hand.
  - In `Σ_{x∈X} E1_x` each `u_{r_ℓ}` occurs twice, in `[r_ℓ/ℓ](u_{r_ℓ} + u_g)` and
    `[r_ℓ/g](u_{r_ℓ} + u_g)`, and cancels.
  - The terms inside `X` vanish because all `u_x` are equal. No symmetry among the symbols of `X` is
    used.
  - `λ` and `μ` are additive in the class mod 8, so `λ_{g*}` and `μ_{g*}` are correct, and so is the
    `μ_x u_x` part of the `E2` sum.
  - Formula (2.1) is `E1_ℓ` solved for `u_{r_ℓ}`; (2.2) is `E2_ℓ` solved for `v_{r_ℓ}`.
  - Injectivity and surjectivity are as stated.
  - The hypothesis "`[r_ℓ/x] = 0` for every other `x`" must include the other glue primes; the
    construction provides this.
- **Lemma 3 (base).** CORRECT. With `w = u_{p*} + u_{q₀}`, the `E1` rows give
  `v_{p*} = a₀ + xw` and `v_{q₀} = a₀ + (x + 1)w`. `E2_{p*}` reduces to `a₀ = b₀` and `E2_{q₀}` to
  `u_{q₀} + a₀ = b₀ + b₁`. `(D)` holds, the free unknowns are `a₀`, `u_{p*}`, `u_{q₀}`, and the
  dimension is 3.
  - Exhaustively (`t_base.py`): a configuration `{p*, q}` has dimension 3 and `±p* ∈ π₁` exactly
    for the classes `(7, 3)` and `(3, 7)`, for both symbols. With two auxiliary symbols, bases exist
    for every class of `p*`. This confirms slot-k §2.3.

### 2.4 The slots (slot-k §2.4)

- **Existence.** CORRECT. Each slot has one condition mod 8 and, for each odd prime already fixed,
  one condition "residue" or "non-residue". These are conditions modulo distinct primes, each
  satisfiable by `(y − 1)/2 ≥ 1` invertible classes. By CRT and Dirichlet the slot exists, and it
  can be taken outside any finite set. No choice can be impossible: the conditions never refer
  twice to the same modulus, and none of them involves `θ` or `β` beyond their prime sets. In
  particular nothing breaks when:
  - `ω(β) = 1` (no `r_p`; Lemma 2 with `G = ∅` is the identity, and `[q₀/p₀] = x`);
  - `θ = 1` (no `r_ℓ`; `d₂ = d₁`);
  - `P ⊆ {3, 5, 7, 13}` (`β ∈ ±{7, 15, 39, 455}`);
  - a slot is a small prime such as `q₀ = 3` or `q₀ = 11`. Only `q₀ ∤ 2βθ` is required. The search
    in §4 also took every slot as the least prime with its symbol pattern.
- **Reverse symbols.** CORRECT: `[y/r] = [r/y]` for `r ≡ 1 (mod 4)`, and `[y/q₀] = [q₀/y] + λ_y`.
- **The condition `[q₀/ℓ] = 0` (`ℓ ∈ T`) is never used.** See Finding F1. It is harmless.

### 2.5 The theorem (slot-k §2.5)

- **Reduction to `d₁ = |n|`, `d₂ = |n|θ`.** CORRECT. Both are odd, positive and squarefree, by
  (θ1), (θ2) and the choice of the slots.
- **Step 1 (Lemma 1 for the `r_ℓ` on `𝒞₁`).** CORRECT. Inside `S₁`, each `r_ℓ` is linked only to
  `q₀`, since `ℓ ∉ S₁` and the symbols with `P`, `R_P` and the other `r_ℓ'` vanish. Removing the
  `r_ℓ` one at a time keeps the hypothesis.
- **Step 2 (Lemma 2 with `g = p₀`, `G = P ∖ {p₀}`, `S' = {q₀}`).** CORRECT.
  - `[r_p/q₀] = 0`, and `[r_p/r_{p'}] = 0` in both directions: the later slot's condition, plus
    symmetry.
  - The glued class is `|β| mod 8 = 7`, and `[q₀/p*] = Σ_P [q₀/p] = x`.
- **Step 3 (dimension 3).** CORRECT, by Lemma 3 and Proposition 0 for `c = 5`.
- **Step 4 (lift of `β` to `𝒞₁`).** CORRECT. With `a₀ = s` and `w = 1`, Lemma 3 gives
  `v_{p*} = s + x = 1` and `v_{q₀} = s + x + 1 = 0`. Then (2.1) gives
  `u_{r_p} = [q₀/p] + 1 + λ_p x = 0`, and Lemma 1 gives `u_{r_ℓ} = u_{q₀} = 0`. So `u = 𝟏_P`, and the
  first coordinate is `(−1)^s|β| = β`.
- **Step 5 (Lemma 2 with `g = q₀`, `G = T` on `𝒞₂`).** CORRECT.
  - `c_{q₀*} = 3θ ≡ 3 (mod 8)` by (θ1).
  - `[q₀*/p] = [q₀/p] + [θ/p] = [q₀/p]` by (θ4).
  - `[p/q₀*] = [p/q₀] + [p/θ]`, and `(p/θ) = (θ/p) = 1` by Jacobi reciprocity (`θ > 0`,
    `θ ≡ 1 (mod 4)`).
  - The symbols between `R_P` and `T` vanish.
  - The glued configuration is `𝒞_Σ`. The symbols `[q₀/ℓ]` are internal to `X = T ∪ {q₀}` and do
    not enter (F1).
- **Step 6 (lift of `β` to `𝒞₂`).** CORRECT.
  - By (2.1), `u_{r_ℓ} = Σ_P [p/ℓ] + Σ_{R_P}[r_p/ℓ]u_{r_p} + λ_ℓ(v_{q₀} + a₀)`.
  - Here `Σ_{R_P}[r_p/ℓ]u_{r_p} = 0` and `v_{q₀} + a₀ = s`, so `u_{r_ℓ} = [|β|/ℓ] + sλ_ℓ = [β/ℓ] = 0`
    by (θ3).
- **Non-torsion.** CORRECT. `n/β` and `nθ/β` are not `±1`, so `β ∉ {±1, ±d}` modulo squares. The
  class `β` is therefore not a torsion class, and a point realizing it has `x ∈ βℚ*²` with
  `y ≠ 0`.

**Sign remark.** Because `(−1, −d) ∈ Sel₂(C_d)`, `β ∈ π₁` if and only if `−β ∈ π₁`. The sign of `β`
therefore never decides membership. It enters only through `x = s + 1` in the prescribed symbols
of `q₀`, which change the configuration. That is what slot-k means by "this is where the sign of
`β` enters", and the negative controls confirm it (F3, §4.5).

## 3. Findings

No step of the proof fails, and no input was found on which a prescribed choice is impossible or
the produced curves fail the certificate. The findings below concern the presentation and the side
claims. None of them affects the validity of DL.

**F1 (minor; the proof is unaffected). The condition `[q₀/ℓ] = 0` for `ℓ ∈ T` is superfluous, and
the reason slot-k gives for it is wrong.**

- slot-k §2.5 ("What each slot does") says that the symbols of `q₀` at `T` are dictated "by the
  transfer to the second curve". They are not used anywhere.
  - In `𝒞₁` the primes `ℓ ∈ T` do not occur.
  - In `𝒞₂` they are glued to `q₀` by Lemma 2 with `X = T ∪ {q₀}`. Symbols between two elements of
    `X` drop out of every row, since they multiply `u_x + u_{x'} = 0` or `v_x + v_{x'} = 0`; slot-k's
    own remark 1 in §5.1 says so.
  - Formula (2.1) for `u_{r_ℓ}` involves only `y ∈ S'`.
- Computation agrees:
  - with `[q₀/ℓ]` random, all 30 runs of an actual-prime batch were still certified (§4.5);
  - so were 1,000 random abstract configurations (F3) and all 2,048 cases of the exhaustive check
    with `|P| = |T| = 2` (§4.4).
- *Repair.* Drop the condition, or keep it and delete the justification. Dropping it removes
  `ω(θ)` residue conditions from the Lean lemma L3.

**F2 (minor; a side claim). "Within one of the bound" (slot-k §2.6) holds only when
`ω(β) = k(β) + 1`.**

- On the first curve the construction uses `ω(β)` auxiliary primes visible to `β` (`q₀` and the
  `r_p`). Proposition B gives the lower bound `k(β)`, the size of an isotropic core.
- `|β| ≡ 7 (mod 8)` forces `ω(β) ≥ k(β) + 1`, but `ω(β)` can be much larger than `k(β)`.
  - On the core inputs of §4.3, where `β` is the core times the `S₀`-part supplied by `m`,
    `ω(β) − k(β)` ranges over 1–3 across the multipliers.
  - Extra primes of `β` outside the core widen the gap without bound.
- *Repair.* Say "uses `ω(β) ≥ k(β) + 1` visible auxiliary primes, against the lower bound `k(β)`".

**F3 (remark). Every other prescribed condition is load-bearing.** This was measured on random
abstract data satisfying (θ1)–(θ4), replacing one family of prescribed symbols at a time by random
bits (1,000 trials each, `ω(β) ≤ 6`, `ω(θ) ≤ 5`). The share of trials whose conclusion fails is:

| Family replaced by random bits | Failures |
| --- | --- |
| `[q₀/p]`, `p ∈ P ∖ {p₀}` | 68% |
| `r_p` at `T` | 34% |
| `r_p` at `q₀` | 44% |
| `r_p` at `P ∖ {p, p₀}` | 61% |
| `r_p` at earlier `r_p` | 46% |
| `r_ℓ` at `P` | 78% |
| `r_ℓ` at `T ∖ {ℓ}` | 34% |
| `r_ℓ` at `R_P` and earlier `r_ℓ` | 62% |
| `q₀ ≡ 7` instead of `3 (mod 8)` | 100% (dimension 4) |
| sign rule `x = s` instead of `s + 1` | 47–53% |

- With the sign rule `x = s`, only the second curve fails. It loses the class `β`, and it does so
  exactly when `θ` has a prime `≡ 3 (mod 4)`: 470 of 1,000 trials, against 530 certified trials
  without such a prime. This confirms the negative control of slot-k §3.3.
- So, apart from F1, the construction has no redundant condition that a reader might be tempted to
  weaken.

**F4 (remark). Small and special slots.**

- Nothing in the proof requires the slots to be large or prime to 2730. `q₀ = 3` or `q₀ = 11`,
  and `r = 17` or `r = 41`, are allowed whenever they satisfy the symbol conditions and do not
  divide `2βθ`.
- The family `small_slots` of §4.3, which takes every slot to be the least prime with its pattern,
  exercises this (`q₀ = 3` in 4 runs).
- Whether the downstream use (the witness `e` of `PoleSoluble`) tolerates auxiliary primes in
  `{3, 5, 7, 13}` was not examined here (UNCHECKED). descent-alt §2(a) states that nothing
  downstream constrains `e`. If a constraint appeared, it would be met by excluding these primes in
  the Dirichlet step, which costs nothing.

**F5 (remark). An unused consequence of the input argument.**

- The proof of (θ1) shows that `θ` is a square modulo 3, 5, 7 and 13, since `1 − B/m` is a unit
  square there. The construction does not use this.
- Test generators that prescribe `θ` must respect it. Abstract tests that ignore it, as in slot-k
  §3.3 and here, test a superset of the actual inputs, which is harmless.

## 4. Computations

All scripts are in `scratch/rv-slot-k-red/`. None imports code from `scratch/slot-k/`,
`scratch/descent-alt/` or `scratch/rv-route-k/`.

### 4.1 An independent exact 2-Selmer computation

`sel2.py` computes `Sel₂(C_d)` for odd squarefree `d > 0` directly from the definition, as the
classes `(a, b)` in `⟨−1, 2, p | d⟩²` whose local class lies in the local image at `∞`, at 2 and at
every `p | d`. Outside `2d∞` the condition holds automatically. The local images are computed as
follows:

- at odd `p | d`, the span of the two torsion images;
- at `∞`, the span of `(−, −)`;
- at 2, the span of the Kummer images of 2-adic points. The points are found by searching rationals
  `x` with `x(x − d)(x + d)` a nonzero 2-adic square. The search stops when the span reaches
  dimension `3 = log₂ #C_d(ℚ₂)/2`; the script asserts that it does.

**Checks.**

- *Against PARI.* On 27 small `d` the dimensions agree with PARI's `ellrank`, as
  `dim Sel₂ = 2 + R + s`. Examples: `d = 17` has `Ш[2]` of rank 2, and `d = 113` has `R = 2`.
- *Against Proposition 0.* `prop0.py` implements the system of slot-k §2.1 from the text. On 600
  random `d` (1–8 primes below 3000; 128, 162, 153 and 157 curves in the classes 1, 3, 5, 7 mod 8),
  the two computations give the same subspace of `(ℚ*/ℚ*²)²`, not merely the same dimension
  (`t_prop0_full.py`). Proposition 0 is therefore confirmed in all four classes, beyond the class 5
  that the proof uses.

### 4.2 The construction on adversarial admissible inputs

`construct.py` implements slot-k §2.4 from its text:

- it computes `β` and `θ` from `B` and `m`, factoring with PARI, and checks (θ1)–(θ4);
- it chooses `q₀` by CRT modulo 8 and the primes of `βθ`;
- it chooses the `r_p`, then the `r_ℓ`, by CRT modulo 8, the primes of `βθ` and `q₀`, followed by a
  search for the symbols at the earlier slots;
- it certifies `C_{|n|}` and `C_{|n|θ}` with `sel2.py`.

`p₀` is chosen at random, or set to every element of `P` in turn. One option instead takes every
slot to be the least prime with its prescribed symbol pattern, so that slots such as `q₀ = 3`
occur.

**Generators** (`gens.py`, `families.py`).

- For a prescribed signed `β` the input is `B = mβt²` with `t = 2730²a/b`. Then `sqf(mB) = β` and
  `θ = sqf(1 − βt²)`, and inputs are kept when they are admissible and `θ` has the wanted shape.
- `θ = 1` comes from the conic `βt² + c² = 1` through `(0, 1)`, that is `t = 2k/(β + k²)`.
- Isotropic cores are primes `≡ 1 (mod 21840)` that are pairwise quadratic residues, as in
  Proposition B.
- The slope site uses `t = u/v` with all six `|u + cv|` (`c ∈ {0, 15, 20, 24, 30, 60}`) prime and
  `≡ ±1 (mod 8)`, `R₀ = ηF(t)/(t − 1)⁸` and `B = R₀s²`, exactly as `slopeR` gives
  (`B = ℓ²a²R₀/Θ²`).
- The test site uses `R₀ = η·2730⁶F(n)` with integer `n`, and `B = R₀s²`, exactly as `testR` gives.

Batches have at most 30 runs and were run one after another. A run is one input with one
multiplier.

### 4.3 Results on admissible inputs

Every run satisfied (θ1)–(θ4), and every run was certified: both curves have `dim Sel₂ = 3` with
`β ∈ π₁`, and both have `d ≡ 5 (mod 8)`.

| Family | What it attacks | Runs | Certified | `ω(β)` | `ω(θ)` | Slots | Signs |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `theta1` | `θ = 1`; `β = ±7, ±15, ±39, ±455` and others with `ω(β) ≤ 4` | 21 | 21 | 1–4 | 0 | 1–4 | ± |
| `omega1` | `ω(β) = 1`: `β = ±p`, `p ∈ {7, 23, 31, 47, 71, 10079, 999983, 46216991}`; `θ` with primes `≡ 3, 5, 7 (mod 8)` | 16 | 16 | 1 | 1–4 | 2–5 | ± |
| `all3mod4` | every prime of `β` `≡ 3 (mod 4)` | 28 | 28 | 1–7 | 1–9 | 2–14 | ± |
| `mostly1mod4` | one prime `≡ 3 (mod 4)`, the others `≡ 1 (mod 4)` | 18 | 18 | 2–7 | 1–6 | 4–13 | ± |
| `thetacls` | `θ` with `{3, 5, 7} ⊆` its classes; only 3s; only 5s; only 7s; only 1s; two primes `≡ 3 (mod 4)` | 30 | 30 | 1–4 | 1–5 | 3–9 | ± |
| `s0beta` | `P ⊆ {3, 5, 7, 13}`, every `p₀` | 26 | 26 | 1–3 | 1–6 | 2–8 | ± |
| `allm` | all 8 eligible multipliers per input | 24 | 24 | 2–9 | 1–6 | 3–15 | ± |
| `p0var` | every choice of `p₀` | 15 | 15 | 7–8 | 3–4 | 11 | − |
| `cores` | isotropic cores `k = 3, 4, 5, 6`, all eligible `m` | 30 | 30 | 4–9 | 1–7 | 6–14 | ± |
| `cores_extra` | core plus a large prime `≡ 3, 7 (mod 8)` | 30 | 30 | 4–8 | 1–7 | 7–14 | ± |
| `slope_site` | six good slope primes `≡ ±1 (mod 8)`, `B = R₀s²` | 30 | 30 | 6–9 | 2–6 | 9–14 | ± |
| `test_site` | `β = sqf(mηF(n))`, `|n| ≤ 10⁶` | 17 | 17 | 4–14 | 1–6 | 7–18 | ± |
| `test_site_b` | the same, `|n| ≤ 3000` | 13 | 13 | 6–11 | 1–4 | 7–13 | ± |
| `small_slots` | each slot the least prime with its pattern (`q₀ = 3` in 4 runs) | 26 | 26 | 1–6 | 0–5 | 1–10 | ± |
| `large` | `ω(β) = 9–12`, `ω(θ) ≥ 3` | 9 | 9 | 9–12 | 3–8 | 13–17 | ± |
| `random30` | random admissible `B` | 30 | 30 | 1–9 | 1–6 | 3–14 | ± |
| **total** | | **363** | **363** | 1–14 | 0–9 | 1–18 | |

**Notes on the families.**

- The primes of `β` and of `θ` occur in all four classes mod 8.
- `θ` has a prime `≡ 3 (mod 4)` in at least 264 of the 363 runs (2 runs have too many primes for the
  log to show their classes). That is the case in which the sign rule matters.
- In `large` a tenth run was abandoned: the search for a slot with about 19 symbol conditions at
  earlier slots exceeded its budget of `10⁷` candidates. This is a limit of the implementation,
  which imposes the conditions at earlier slots by trial. It is not a failure of the construction,
  whose slots exist by Dirichlet's theorem.

### 4.4 Exhaustive and random checks of the theorem on abstract data

`t_symbolic_exh.py` enumerates every configuration with `|P| = a`, `|T| = b`:

- all classes mod 8, with `Π_P ≡ 7` and `Π_T ≡ 1`;
- all symbols inside `P`, inside `T` and from `P` to `T`, with the reverse symbols fixed by
  reciprocity, subject to (θ3) and (θ4);
- both signs of `β`, and every `p₀`.

It adds the slots symbolically and checks both systems with Proposition 0. There were no failures
in any of the following.

| `(a, b)` | (1,0) | (2,0) | (3,0) | (4,0) | (1,1) | (2,1) | (3,1) | (4,1) | (1,2) | (2,2) | (3,2) | (1,3) | (2,3) | (1,4) |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| cases | 2 | 32 | 768 | 32768 | 2 | 32 | 768 | 32768 | 16 | 512 | 24576 | 256 | 16384 | 8192 |

- With `[q₀/ℓ]` arbitrary, all 2,048 cases for `(2, 2)` also pass.
- `t_variants.py` on random abstract data (`ω(β) ≤ 6`, `ω(θ) ≤ 5`) found no failure in 6,000
  trials. The same script produces the table of F3.

### 4.5 Negative controls on actual primes

On the 30 inputs of `random30` with seed 5, three variants of the construction were run:

| Variant | Certified |
| --- | --- |
| sign rule `x = s` | 6/30 |
| `[q₀/p]` flipped for `p ≠ p₀` (keeping `Σ_P [q₀/p] = x`) | 0/30 |
| `[q₀/ℓ]` random (F1) | 30/30 |

The check is therefore sensitive to the conditions that matter, and confirms that `[q₀/ℓ]` does
not.

## 5. Repairs

None is needed for the validity of DL. For the final text:

1. **F1.**
   - In slot-k §2.4 either delete the condition `[q₀/ℓ] = 0 (ℓ ∈ T)`, or keep it as a harmless
     normalization.
   - In either case, replace "its symbols at `T` by the transfer to the second curve" (§2.5, "What
     each slot does") with: "the symbols of `q₀` at `T` are internal to the glued set `T ∪ {q₀}` and
     play no role".
   - Dropping the condition shortens the Lean lemma L3.
2. **F2.** In slot-k §2.6, replace "This is within one of the bound" with "the bound is `k(β)` and
   `ω(β) ≥ k(β) + 1`; the two agree up to one exactly when `β` has a single prime outside its core".
3. **Optional, for the write-up.** State the sign remark of §2.5 above: `±β` are simultaneously in
   `π₁`. The sign of `β` enters only through the prescribed symbol `[q₀/p*] = s + 1`.
4. **Optional, for the Lean formalization.** The proof uses Proposition 0 only for `d ≡ 5 (mod 8)`,
   and its place-2 rows only in the form verified in slot-k §2.1. CR₃ can therefore be stated for
   `d ≡ 5 (mod 8)` alone without losing anything, as slot-k §4.1 already suggests.

## Scripts (in `scratch/rv-slot-k-red/`)

| Script | Purpose |
| --- | --- |
| `sel2.py` | exact `Sel₂(C_d)` from the definition (local images at `∞`, 2, `p | d`) |
| `prop0.py` | the Selmer system of slot-k §2.1, from the text |
| `t_prop0_vs_sel2.py`, `t_prop0_full.py` | Proposition 0 against `sel2.py` (600 curves, subspace equality) |
| `construct.py` | the construction of slot-k §2.4 with actual primes; negative-control variants |
| `gens.py`, `families.py` | generators of admissible inputs and the 16 families of §4.3 |
| `run_batch.py`, `summarize.py` | driver (at most 30 runs per batch) and the table of §4.3 |
| `t_symbolic_exh.py` | exhaustive check of the theorem on abstract configurations (§4.4) |
| `t_variants.py` | randomizing one prescribed condition at a time (F3) |
| `t_base.py` | base configurations (slot-k §2.3) |
| `out_*.txt` | outputs of the batches |

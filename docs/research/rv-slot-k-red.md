# Referee report on the slot construction for the descent lemma: counterexamples and edge cases

This report examines the proof of the descent lemma DL in `docs/research/slot-k.md` §2, together
with the input pairs of `docs/research/descent-alt.md` §3.1 and the Selmer system of descent-alt
Proposition 0. Its focus is adversarial: to find admissible inputs on which a choice prescribed by
the construction is impossible, or on which the curves it produces fail the certificate. Every step
was rechecked by hand, and the construction was reimplemented from the text of slot-k §2.4 and run
against an exact 2-Selmer computation written from the definition (independent of Proposition 0
and of the code of slot-k and descent-alt).

Each step examined is marked:

- **CORRECT**: checked here, by hand or by an exhaustive computation;
- **GAP**: missing or wrong, with what fails and whether it can be repaired;
- **UNCHECKED**: not examined here.

<!-- VERDICT -->

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
- **Lemma 2 (gluing).** CORRECT. I redid steps 1–4 by hand.
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
`β` enters", and the negative control confirms it (§4.3).

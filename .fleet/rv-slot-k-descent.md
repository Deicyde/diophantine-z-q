# rv-slot-k-descent: referee report on the 2-descent behind the slot proof of DL

Deliverable: `docs/research/rv-slot-k-descent.md`. Scripts and outputs: `scratch/rv-slot-k-descent/`
(new code; nothing imported from `scratch/slot-k/`, `scratch/descent-alt/` or `scratch/rv-route-k/`).
Running log: `scratch/rv-slot-k-descent/log.md`.

## Verdict

**DL is proved as written** in `docs/research/slot-k.md` §2. No finding affects its validity. There
are three minor findings (an incomplete written proof in descent-alt, an implicit half-step, and
citations) and two cosmetic ones. Repairs are recommended before the argument goes into the
manuscript or the Lean hypothesis CR₃.

## What was checked

- **Proposition 0, from first principles: CORRECT, in all four classes of `d mod 8`.** Checked:
  - the Kummer map `(x, x − d)` and the torsion images;
  - the odd primes of `d` (local image = torsion span, since the valuation vectors are independent
    and `#E(ℚ_p)/2E(ℚ_p) = 4`);
  - the primes not dividing `2d`, and the real place;
  - the place 2. A single 2-adic point, `x = 1/4`, lies on `C_d(ℚ₂)` for every odd `d`, with class
    `(1, 5)`. With the two torsion images it spans the dimension-3 image.

  The derived rows agree row by row with descent-alt §4.1 and slot-k §2.1 `(D)`. For `c = 1, 5` the
  tables use `(R)` to write `λ·u = λ·v`, which is legitimate. The construction only ever meets
  `d ≡ 5`.
- **Certificate: CORRECT.**
  - `lem:corank` (manuscript l.1072) applies verbatim to `C_d`, which has full 2-torsion.
  - Kriz's Theorem 10.13 applies: `f₀ ≥ 21`.
  - `r + dim Ш[2] = 1` gives `Ш[2] = 0` and `C_d(ℚ)/2 = Sel₂`; RK9 then gives a non-torsion point
    with abscissa in `βℚ*²`.

  This matches pc-audit §2.2/RK1/RK3/RK9 and rv-route-k §4.3.
- **The rest of the proof: CORRECT, rederived by hand.** This covers (θ1)–(θ4), Step 0, Lemmas 1–3,
  slot existence, and steps 1–6. The checks include the `E2` sums in Lemma 2, the use of
  reciprocity for later slots, Jacobi reciprocity in step 5, and the sign bookkeeping
  `u_{r_ℓ} = λ_ℓ(s + x + 1)`.

## Computations (all exact, own code)

- **Proposition 0 against an independent point-based descent:** 30 random `d`, all classes mod 8.
  The Selmer subspace and the `π₁` membership of every signed divisor agree in 30/30. PARI `ellrank`
  agrees on `dim Sel₂` in 10/10.
- **Own implementation of the construction on 30 admissible inputs:**
  - the inputs are `B₁`, `B₂`, `B₃`, the second core-6 input, the 6 greedy-stall inputs, 5 new
    core-3/core-4 instances and 15 random inputs; 16 runs have `β < 0` and 14 have `β > 0`;
  - both `C_n` and `C_{nθ}` are certified (`dim Sel₂ = 3`, `β ∈ π₁`) in **30/30**;
  - the slot count is always `ω(β) + ω(θ)` (5–12) and `|n| ≡ 5 (mod 8)`.
- **Negative control** (`x = s` instead of `s + 1`): on the 16 inputs whose `θ` has a prime
  `≡ 3 (mod 4)`, the second curve loses `β` from `π₁` in 16/16, exactly as step 6 predicts.
- **Small realizations, `ellrank`:** 10 curves, all `[r₁, r₂, s] = [1, 1, 0]`. The 4 points found all
  have abscissa class `β`·torsion.

## Findings (severity)

1. **F1 (minor).** The place-2 rows in descent-alt are justified by sampled points, and only the
   `d ≡ 5` classes are printed. Rows `c = 1, 3, 7` have no written proof. Repair: the `x = 1/4`
   table of report §1.4.
2. **F2 (minor).** slot-k §2.1 states only one half of the reduction to `ℚ(S ∪ {2}, 2)²`. Add the
   good-reduction half: at `p ∤ 2d` the local image is the unramified subgroup.
3. **F3 (minor).** Cite Kriz Theorem 10.13 alone, not 10.17(2), and record the `f₀ ≥ 4` check.
   Cassels suffices for the alternating pairing.
4. **F4 (cosmetic).** Symbol clashes (`x`, `ω`, `K`).
5. **F5 (cosmetic).** "Within one of the lower bound of Proposition B" holds only when `β` has one
   prime outside the core. In general the gap is ≤ 4.

## Suggestions

- From the 2-descent side, the proof can be accepted for the switch to `x + ℓ` once the other two
  referees concur; F1–F3 can be folded into the rewrite of manuscript §5.
- For the Lean hypothesis CR₃: Proposition 0 holds in all four classes, so the unrestricted form is
  justified. Restricting to `d ≡ 5 (mod 8)` would need only the `c = 5` row.
- Not examined here: rv-route-k §4.2 (points ⇒ `Φ_C(B)`) and descent-alt Propositions A–C. The
  proof of DL does not use Propositions A–C.

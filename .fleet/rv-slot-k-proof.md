# rv-slot-k-proof: referee report on the proof of DL (slot-k §2)

Deliverable: `docs/research/rv-slot-k-proof.md`. Scripts and outputs: `scratch/rv-slot-k-proof/`
(independent code; nothing is imported from `scratch/slot-k/` or `scratch/descent-alt/`). Log:
`scratch/rv-slot-k-proof/log.md`.

## Verdict

**DL is proved as written.** I redid every step of `slot-k.md` §2 by hand and found no mathematical
gap. That covers the place-2 row for `c = 5` and the odd and real places of Proposition 0, Lemmas 1–3,
the slot conditions, steps 0–6 and the count. All three points the note flags check out:

- the cancellation in Lemma 2 step 3;
- the two uses of (θ4) in step 5;
- the sign bookkeeping in step 6.

The residue conditions on the auxiliary primes are always simultaneously satisfiable. Each one is
a condition on the new prime modulo an already fixed odd prime, with pairwise distinct moduli, so
CRT and Dirichlet apply directly and reciprocity imposes nothing extra. This holds for every
eligible multiplier, for `θ = 1`, and when `β` or `θ` has only primes `≡ 3 (mod 4)`.

DL as proved gives what Route K uses. Through the corank lemma, Kriz's Theorem 10.13 and RK9, the
certificates yield points on `C_n` and `C_{nθ}` with abscissa in `βℚ*²`, where `β` is signed and
the same `m` defines `β` and `θ`. Rescaling these points gives a zero of the `x + ℓ` pole polynomial
for every `B` satisfying the hypotheses of `ZInQ.PoleCompleteness`. I rederived this rescaling
directly from `polePoly`. The deep input itself (Kriz) is outside this review.

## Findings (all minor; none affects DL)

1. **Unused slot condition / inaccurate commentary.** `[q₀/ℓ] = 0` (`ℓ ∈ T`) is never used, because
   symbols inside the glued set `T ∪ {q₀}` drop out of Lemma 2. The note says they are dictated by
   the transfer; they are free. Exhaustive test: dropping the condition changes nothing.
2. **Overstatement.** "Within one of the lower bound of Proposition B" holds only when
   `ω(β) = k + 1`. In the core setting the first curve uses between `k + 1` and `k + 4` auxiliary
   primes, and in general there is no relation.
3. **Wording.** §2.1 states only the easy direction of "Selmer classes are supported on −1, 2 and
   the primes of d". Both directions are standard (Silverman X.1.4).
4. **Citation.** Cite Kriz Theorem 10.13, not 10.17(2) (as pc-audit RK1 advises). State that Kriz's
   hypothesis `f₀ ≥ 4` holds, since the odd part of `|d|` is `d ≥ 21`.
5. **Presentation.** The torsion certificate in §1.2 is loosely phrased. It is never used.

## Computations (independent implementations)

- Own exact 2-descent (`sel2.py`, no use of Proposition 0) vs PARI `ell2cover`: 30 curves, 0
  mismatches.
- Own Selmer system (`system.py`) vs own exact descent: 30 curves, dimension and every signed odd
  divisor as a first coordinate, 0 mismatches (all four classes mod 8).
- The theorem on abstract data satisfying only (θ1)–(θ4):
  - exhaustive for `|P|, |T| ≤ 3` (541,748 cases) and 1,000 random cases with `|P|, |T| ≤ 10`;
    0 failures;
  - negative control `x = s`: fails exactly when `θ` has a prime `≡ 3 (mod 4)`.
- End to end with actual primes for 30 runs `(B, m)` of admissible `B`, certified by the own exact
  descent. Families: random; `θ = 1` with both signs of `β`; `β` with only primes `≡ 3 (mod 4)`;
  prescribed `θ` with primes `≡ 3 (mod 4)` and both signs of `β`. Both curves certified in all 30 runs (`ω(β)` 1–8, `ω(θ)` 0–6, 16 runs with `β < 0`, 20 with a prime `≡ 3 (mod 4)` in `θ`, 22 distinct multipliers); slot count always `ω(β) + ω(θ)`.

## Suggestions

- Make the five editorial changes listed in §9 of the deliverable. Dropping `[q₀/ℓ] = 0` also
  shortens lemma L3 of a Lean formalization.
- In Lean (L5), write step 5 prime by prime: `Σ_ℓ[p/ℓ] = [θ/p] + λ_pλ_θ`. This needs no Jacobi
  symbols.
- From the proof side, nothing blocks switching the Lean construction to `x + ℓ`. What remains is
  the status of the deep input (Kriz, or TYZ via RK6), which this review did not cover.

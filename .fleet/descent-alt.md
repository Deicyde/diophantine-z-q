# descent-alt: the free multiplier and the free witness in the descent lemma of Route K

Deliverable: `docs/research/descent-alt.md`. Scripts and outputs: `scratch/descent-alt/` (they import
the exact 2-Selmer code `scratch/rv-route-k/sel2cong.py`).

## Verdict

The freedom the construction already offers does **not** replace auxiliary primes, and no bounded
number of auxiliary primes suffices. Both statements are proved at the level of certificates
(`dim Sel₂ = 3` plus the class `β`, the form in which Kriz's theorem is used). Neither affects
Route K: the auxiliary primes enter only the free witness `e`, so nothing in `Q_pole`, the multiplication
template or the Lean proof changes. The slot construction (task pole-descent-k) is unavoidable. The
note gives it an exact algebraic language and two hard constraints.

## Results

1. **Proposition 0** (VERIFIED). For odd `d`, `Sel₂(C_d)` is the kernel of an explicit `𝔽₂`-linear
   system in the Legendre symbols of the primes of `d`.
   - Odd places: `A u + D_λ v = a₀λ + a₁μ`, `D_μ u + (A + D_λ)v = b₀λ + b₁μ`.
   - Real place and 2: three linear rows, depending on `d` mod 8.
   - Agrees with the exact descent on 600 random curves (dimension and first coordinates).
   - The descent lemma is thus a finite combinatorial statement plus Dirichlet's theorem.
2. **Proposition A** (`n = β`; VERIFIED).
   - (i) `β` is always in the abscissa (2-isogeny) Selmer group of `C_{βθ}`, so the obstruction is
     global.
   - (ii) Because `(β/ℓ) = 1` on `θ` and `(θ/p) = 1` on `β`, the Monsky matrix of `βθ` splits into
     those of `β` and `θ`, coupled only off the diagonal. `β ∈ π₁(Sel₂)` iff `A v = r_β` is solvable
     with `v` supported on the primes `≡ 1 (mod 4)`. Checked on 400 pairs.
   - (iii) If all primes of `θ` are `≡ 1 (4)`, then `(1, θ) ∈ Sel₂(C_{βθ})` and `n = β` is never
     certified.
3. **The multiplier alone fails** (VERIFIED, computation).
   - Random inputs: 92 of 1,920 multiplier evaluations certified (4.8%); 2 of 30 inputs have no
     certifying multiplier.
   - `β` with six primes `≡ 3 (4)`: 3 of 10 inputs have none.
   - Three explicit admissible `B` with no certifying multiplier are listed in §4.3.
4. **Proposition B** (VERIFIED: proof, exhaustive checks for cores of size 2 and 3, actual curves for
   size 6). Suppose the primes of `β` outside `S₀` are `k` primes `≡ 1 (mod 21840)` that are pairwise
   residues. Then for every multiplier:
   - every certificate with `n' ≠ 1` needs at least `k` auxiliary primes, whatever `q` is;
   - `n' = 1` needs `ω(θ) ≥ k`.

   So no bounded form of the descent lemma is true for PC as stated. The bound is sharp up to one in
   the exhaustive tests.
5. **Proposition C** (VERIFIED). If all auxiliary primes are `≡ 1 (4)`, `(n'/p) = 1` on `β` and
   `(β/q) = 1` on `n'`, then `(1, n') ∈ Sel₂(C_{βn'})` and no certificate is possible. Some slot must
   break the symmetry at a prime `≡ 3 (4)`. This is the manuscript's slot `q₀` of type `(1, 1)`.
6. **The free witness `q`** (VERIFIED: it moves only `θ`, through one fixed rational function).
   SPECULATIVE: controlling the Legendre symbols of all primes of `θ(q)` is out of reach of current
   methods, so `q` cannot be used in a proof.
7. **Call sites** (VERIFIED by reading Lean).
   - Slope site: `β`'s primes outside `S_b` are at most six good slope primes (`≡ ±1 mod 8`). Under
     22P₂ they are exactly the six pattern primes.
   - Test site: `β ≡ mηF(n)` for the tested integer `n`, unbounded and not under the prover's
     control.
   - The slope and shift choices cannot change `β`. The number of auxiliary primes is invisible to
     the completeness argument.
8. **Experiments with auxiliary primes** (VERIFIED, computation).
   - A single auxiliary prime can certify `C_{βq}` only when `s(β)` is small.
   - Greedy one-prime descent on a Selmer potential stalls on 7 of 30 inputs at `(1, 1)`. Random
     search then solves all 7 with 2 or 3 primes, so all 30 inputs admit a certificate.

## Ranking

| Rank | Route | Chance |
| --- | --- | --- |
| 1 | Slot construction written in the language of Proposition 0 (≥ `k(β)` slots, one symmetry-breaking slot `≡ 3 (4)`, free slot symbols at the primes of `θ`) | medium |
| 2 | Same, plus one bordered determinant per curve (TYZ, published) | medium-low |
| 3 | Reachability proof (Swinnerton-Dyer/Kane Markov chain) for pairs of twists with a class condition | low-medium |
| 4 | Bounded slots at the slope site only | irrelevant (the test site needs the general form) |
| 5 | Multiplier only; free witness `q` | refuted / very low |

## Open questions

- A written proof of the descent lemma (the slot construction). Propositions B and C fix its
  minimal shape but do not prove it.
- Does the test site actually produce `β` with large isotropic cores? This needs values `F(n)` whose
  other primes are residues modulo the core. It is plausible, and PC as stated certainly contains
  such inputs.
- Is a two-prime step always enough to lower the potential of §4.7, from every state?
- At the slope site, is a lemma with at most `6 + O(1)` slots true and easier?

## Suggested follow-up tasks

1. **slot-construction-K**: implement the slot choice as an algorithm on symbol matrices
   (`scratch/descent-alt/auxsym.py` gives symbolic primes; `symsel.py` gives the Selmer system), and
   prove it. Validate on the core instances (`e10_core_instance.py`, `e11_core_check.py`), the
   smooth-`θ` family of rv-route-k and 30 random inputs.
2. **two-step reachability**: exhaustive two-prime search from the plateau states of
   `e8_greedy.py`. A positive answer gives an inductive proof strategy (Route R5).
3. Merge with pole-descent-k: check its construction against Propositions B and C. It needs at least
   `k(β)` slots, and a slot or symbol pattern that breaks `(1, n')`.

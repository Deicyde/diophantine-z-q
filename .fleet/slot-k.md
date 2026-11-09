# slot-k: a proof of the descent lemma of Route K

Deliverable: `docs/research/slot-k.md`. Scripts and outputs: `scratch/slot-k/` (they import the exact
2-Selmer code `scratch/rv-route-k/sel2cong.py` and descent-alt's `symsel.py`). Running log:
`scratch/slot-k/notes.md`.

## Verdict

**DL is true, with a complete written proof** (note §2). For every admissible `B`, choose `m` with `β`
odd and `|β| ≡ 7 (mod 8)`. Then `n = β · q₀ · Π r_p · Π r_ℓ` works, with `ω(β) + ω(θ)` auxiliary primes.
Both `C_n` and `C_{nθ}` have `dim Sel₂ = 3` and `β ∈ π₁`. The proof uses only explicit 2-descent
(descent-alt Proposition 0), quadratic reciprocity for Legendre and Jacobi symbols, CRT and Dirichlet.
It uses nothing about `θ` beyond the four properties (θ1)–(θ4), and it never uses the witness `q`.

## The construction

- `q₀ ≡ 3 (mod 8)`: the symmetry-breaking slot that Proposition C demands. Its symbols at the primes
  of `β` are fixed by a lifting condition, and it is a square mod every prime of `θ`.
- `r_p ≡ 1 (mod 8)` for each prime `p ≠ p₀` of `β`: non-residue mod exactly `p` and `p₀`. They glue
  the primes of `β` into one virtual prime of class 7.
- `r_ℓ ≡ 1 (mod 8)` for each prime `ℓ` of `θ`: non-residue mod exactly `ℓ` and `q₀`. They glue the
  primes of `θ` onto `q₀`, so that `C_{nθ}` inherits the Selmer group of `C_n`.
- The symbol `x = [q₀/|β|]` is set to `s + 1`, where `s` is the sign bit of `β`. This makes the class
  `β` survive the second gluing.

## The proof

- **Two gluing lemmas** (exact isomorphisms of the Proposition 0 system):
  - a partner prime `r ≡ 1 (mod 8)` with one non-residue symbol, at `y`, copies `y`;
  - glue primes `r_ℓ` (non-residue at `ℓ` and at an anchor `g`) merge `G ∪ {g}` into one virtual
    prime whose symbols are Jacobi sums.
- Both curves reduce to the base configuration `{p* ≡ 7, q₀ ≡ 3 (mod 8)}`. Its system has
  dimension 3 and contains the class `p*`, proved by hand (Lemma 3).
- The class `β` is lifted explicitly through each isomorphism. The second curve uses (θ3), (θ4) and
  Jacobi reciprocity.
- The proof relies on Proposition 0 only for the odd and real places (proved in descent-alt), the
  structure of the place-2 rows and the explicit rows for `d ≡ 5 (mod 8)`. The last two are
  rechecked by hand in the note, from the 2-adic image of `C_5`.

## Validation (exact descent `sel2cong.py`, independent of the proof)

- 62 inputs, 216 runs (input × multiplier with `|β| ≡ 7`). Both curves were certified in all 216.
- The inputs cover 30 random admissible inputs, the three inputs with no certifying multiplier
  (`B₁, B₂, B₃`), the core-6 instances of `e11`, new core-3 and core-6 instances, the six
  greedy-stall inputs, ten smooth-`θ` inputs and five inputs with all multipliers.
- The slot count was `ω(β) + ω(θ)` in every run: 3 to 17 slots, of up to 89 digits.
- The theorem itself was checked on 3,300 random abstract configurations (`ω ≤ 12`).
- A negative control (wrong sign choice) fails exactly where the proof says it must.
- PARI `ellrank` on small realizations gives rank bound 1 on all 20 curves. Where it finds a point
  (6 curves), the abscissa has class `β`.

## Completeness and open points

- **Complete as written.** An automated adversarial review of note §§1–2 found no error. It
  re-derived every step and ran its own brute-force checks; its only remark, writing out the
  `v`-analogue of (2.1), has been applied. Still subject to the human independent review which Jack requires before the Lean
  construction switches to `x + ℓ`. The places most worth checking are listed in note §5.1:
  - step 3 of Lemma 2;
  - steps 5–6 of the theorem;
  - the place-2 rows used.
- **Deep input unchanged.** Points come from Kriz 10.13 (unrefereed) plus Poonen–Stoll (A019).
  - Bonus: the construction automatically satisfies the K-TYZ-β rule of pc-audit §4.2
    (`|n| ≡ 5 (mod 8)`, `|β| ≡ 3 (mod 4)`).
  - So if pc-audit's RK6 claim about TYZ row 5b holds, published TYZ plus Gross–Zagier suffice, with
    no change to the descent.
- **Lean.** Keep only CR₃: "if the explicit system of `C_d` has 8 solutions and one with first
  coordinate `a`, then `C_d` has a point with `x ∈ aℚ*²`". It may be restricted to `d ≡ 5`,
  `|a| ≡ 7 (mod 8)`. Prove the rest in Lean:
  - the multiplier;
  - (θ1)–(θ4);
  - the slots (Mathlib has Dirichlet `Nat.forall_exists_prime_gt_and_zmodEq`, CRT, Jacobi
    reciprocity);
  - the system and the gluing bijections;
  - the realization of the symbols;
  - the algebra from points to `PoleSoluble`.

  The hardest pieces are the gluing bijection over changing index sets and the symbol bookkeeping
  (note §4.3).
- **Open.**
  - Are `ω(β) + O(1)` slots enough, i.e. can the `θ`-slots be avoided? Searches typically need only
    2–4 slots.
  - Bases for `|β| ≡ 1, 5 (mod 8)` need two auxiliary primes.

## Suggested follow-up tasks

1. **Independent review** of note §2 (Lemmas 1–3 and the theorem), by someone who has not read this
   note's derivation. This is Jack's gate for switching to `x + ℓ`.
2. **Check pc-audit RK6** (TYZ row 5b depends only on `β`'s 2-adic class). With this construction it
   would let Route K rest on published theorems only.
3. **Lean skeleton.** State CR₃ and the `x + ℓ` `PoleCompleteness_C` in Lean. Prove Lemma 3 by
   `decide` and the gluing lemma for abstract `Fintype` configurations. Check that
   `slope_complete`/`test_complete` close from CR₃ plus the descent, as `sorry`-free targets in
   stages.
4. **Manuscript rewrite** of Section 5's descent (lines 1019–1121) for `C_ℓ` along note §2.
5. *(Optional)* Find the minimal slot count, or a `θ`-free variant.

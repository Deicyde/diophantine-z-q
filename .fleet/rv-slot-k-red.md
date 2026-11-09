# rv-slot-k-red: adversarial review of the slot construction for DL

Deliverable: `docs/research/rv-slot-k-red.md`. Scripts and outputs: `scratch/rv-slot-k-red/`. They
are written from the text of slot-k §2 and descent-alt, and import no code from `scratch/slot-k/`,
`scratch/descent-alt/` or `scratch/rv-route-k/`. Running log: `scratch/rv-slot-k-red/log.md`.

## Verdict

**DL is proved as written** (slot-k §2).

- No GAP: every step was rechecked by hand and is CORRECT. This covers Step 0, (θ1)–(θ4),
  Proposition 0 at the odd and real places and at place 2 for `d ≡ 5 (mod 8)`, Lemmas 1–3, the
  existence of the slots, and steps 1–6 of the theorem.
- No input exists on which a prescribed choice is impossible. Every slot condition is a residue or
  non-residue condition modulo a distinct prime, plus a class mod 8.
- No produced curve failed the certificate. 363 runs over 16 adversarial families of admissible
  inputs gave 363 certified runs, with both curves checked by an independent exact 2-Selmer
  computation. The families cover:
  - `θ = 1`, `ω(β) = 1`, and `β` with all primes `≡ 3 (mod 4)` or mostly `≡ 1 (mod 4)`;
  - `P ⊆ {3, 5, 7, 13}`, and primes of `β` and `θ` in every class mod 8;
  - isotropic cores of size 3–6, every eligible multiplier (both signs), and every choice of `p₀`;
  - slots as small as `q₀ = 3`;
  - the slope site (six good slope primes) and the test site (`β = sqf(mηF(n))`, `ω(β)` up to 14);
  - up to 18 slots.
- On abstract data the theorem holds exhaustively for `|P| + |T| ≤ 5` except `(5, 0)` (117,076
  cases), and on 6,000 random larger configurations.

## Findings (severity)

- **F1 (minor).** The condition `[q₀/ℓ] = 0` for `ℓ ∈ T` is superfluous, and slot-k's stated
  reason for it ("dictated by the transfer to the second curve") is wrong.
  - The symbols between `q₀` and `T` are internal to the glued set in Lemma 2 and drop out.
  - Randomizing them leaves every check certified: 30/30 on actual primes, 1,000/1,000 random and
    2,048/2,048 exhaustive on abstract data.
  - Harmless. Dropping it shortens the Lean lemma L3.
- **F2 (minor).** "Within one of the bound" (slot-k §2.6) holds only when `ω(β) = k(β) + 1`. In
  general the gap to Proposition B's bound `k(β)` is `ω(β) − k(β)`, which is unbounded.
- **F3 (remark).** Every other prescribed condition is load-bearing. Randomizing any single other
  family of symbols breaks the conclusion in 34–100% of trials.
  - The sign rule `x = s + 1` fails, when replaced by `x = s`, exactly when `θ` has a prime
    `≡ 3 (mod 4)` (470/470). This confirms slot-k's negative control.
- **F4 (remark).** Slots may be small or divide 2730 (`q₀ = 3` works). Whether the downstream
  witness `e` tolerates this is UNCHECKED; if not, excluding these primes costs nothing.
- **F5 (remark).** (θ1)'s proof also gives `(θ/p) = 1` for `p ∈ {3, 5, 7, 13}`. It is unused, but
  generators of inputs with a prescribed `θ` must respect it.

## Other checks

- Proposition 0 agrees with the definition-based descent as subspaces, in all four classes mod 8,
  on 600 curves.
- The definition-based descent agrees with PARI `ellrank` on 27 small `d`.
- slot-k §2.3 (base configurations) is confirmed exhaustively.
- `±β` lie in `π₁` simultaneously, since `(−1, −d)` is in the Selmer group. The sign of `β` enters
  only through the prescribed symbol `[q₀/p*] = s + 1`.

## Suggestions

1. Fix the wording of F1 and F2 in slot-k (§2.4/§2.5 and §2.6). Optionally drop `[q₀/ℓ] = 0`.
2. The switch to `x + ℓ` can proceed as far as this review's focus is concerned. The deep input
   (Kriz plus Poonen–Stoll, or TYZ) and the passage from points to `PoleSoluble` were outside its
   scope.
3. CR₃ can be stated for `d ≡ 5 (mod 8)` only, the only class the construction produces.

## Limits

- One run of the `large` family was abandoned at the slot-search budget (`10⁷` candidates). This
  is a limit of the implementation, not a failure of the construction.
- One batch (the test site, seed 13) was stopped by a time limit after 17 runs, all certified. It
  was completed by 13 further runs.
- No Lean process was run.

# rv-route-k: adversarial check of Route K for pole completeness

Deliverable: `docs/research/rv-route-k.md`. Scripts and outputs: `scratch/rv-route-k/`.

## Verdict

**Route K holds with repairs.** No counterexample was found. The one gap is an elementary but
unproved descent lemma.

## What was checked

1. **Soundness** (VERIFIED). Lemma 5.1 holds verbatim for `x + ℓ` with the same `S₀`. The
   factor 3 entered only through the cubic step (`v(x + 3ℓ) = 0` needs `p ≠ 3`). With `x + ℓ`
   that step holds at every prime, and `S₀` is needed only because of the multipliers 2730.
   - `ℓ ≡ 11 (mod 12)` and `j = 35152/9` are used only in RC and its descent.
   - Lean: copy upstream's `curve_rhs_nonzero_and_valuation` and
     `poleSystem_no_negative_odd_valuation` with `3·l → l`.
   - Lean consumers: `pole_obstruction` and `poleSoluble_no_negative_odd`, used at
     `CommonGroup.lean:114` and `TestDivisibility.lean:231`.
2. **Reformulation** (VERIFIED, exact rational arithmetic).
   - For `C_ℓ`: `ℓ(τ) = β(β − τ²)/(β + τ²)`, so `Φ_C(B)` holds iff
     `θ(β² − τ₁⁴)(β² − τ₂⁴) ∈ ±ℚ*²` for some `m, τ₁, τ₂`.
   - 40 explicit zeros of `Q_pole^C` were built and checked.
   - "Only the abscissa class matters" is correct. Classes `β ≡ ±1` need a non-torsion point,
     because `(0, 0)` has abscissa 0.
   - The source note's `θ = 1` witness is wrong: `z = c` should be `z = Bc`, and
     `w = (AHBc)⁻¹`.
3. **Kriz** (arXiv:2002.04767v5, read in the text).
   - Theorems 1.1, 9.23, 10.13 and 10.17(2) apply to every `y² = x³ − d²x`. The only extra
     condition, `f₀ ≥ 4`, is handled in his proof by LMFDB tables.
   - That LMFDB step is never needed in Route K: the only curves with `f₀ ≤ 3` are
     `d ∈ {±1, ±2, ±3, ±6}`, and `C_6` has the point `(−3, 9)`.
   - **Unrefereed**: no journal reference on arXiv, and I found no publication.
4. **Tian–Yuan–Zhang** (Asian J. Math. 21(4), 2017, published), in Smith's determinant form
   (arXiv:1603.08479).
   - My transcription matches Monsky's coranks (60/60) and Smith's asymptotic densities, and
     always implies `dim Sel₂ = 3`.
   - **Route K with TYZ instead of Kriz succeeds on 60 of 60 inputs** (30 random, 30
     adversarial; `out_tyz_*.txt`, `out_brute_tyz_manybeta*.txt`). The deep input could then be
     a published theorem plus Gross–Zagier–Kolyvagin. This variant also no longer needs
     Poonen–Stoll.
5. **Descent** (own exact 2-Selmer code, cross-checked with PARI `ell2cover` 30/30 and with
   actual generators 22/22).
   - Fresh random inputs: 30/30.
   - Adversarial families, many-prime `β`, minimal `S₀` valuations, extreme `B`: 10/10 each, all
     multipliers allowed.
   - Fixed multiplier, trivial `n'` forbidden: 109/120 at once; 8 of the 11 failures were
     retried and solved with 3–6 auxiliary primes up to `10⁶`.
   - Hardest case: a fixed multiplier `m = 1` with `θ` built to have 4–9 small primes.
     Structured searches (beam, two-phase, annealing) failed there. Plain random sampling of
     2–10 primes up to `10⁶` solved every case examined (SMOOTH_FLEET), usually with two
     auxiliary primes after 10–15,000 trials. Suitable `n'` are rare (about `2^{−ω(θ)}`) but
     exist.
   - No invariant obstruction was found: quartic residue symbols, `θ mod 16` and the `n' = 1`
     case were tested.
6. **Other changes** (VERIFIED by grep).
   - Lean: `polePoly`, `poleT1`, `poleT2` and their docstrings, the valuation copy, two parity
     lemmas.
   - Unchanged: `poleTemplate_maj` (coefficients shrink), degree 75, 11 witnesses, and
     therefore exactly 292,890,231,905 variables.
   - Outside Lean: the construction JS.
   - Manuscript: Section 5 rewritten.
   - Sections 7–9 and Appendices E–G (nothing outside cites a result proved there) and 39
     RC-only audit records become unnecessary.

## Ranking

1. **K-Kriz**: Route K with a proved descent lemma; the deep input is Kriz's preprint.
   Chance: medium–high.
2. **K-TYZ**: the same lemma plus one bordered-determinant condition per curve; the deep inputs
   are published (TYZ, Gross–Zagier–Kolyvagin). Chance: medium.
3. **K-L**: a narrow Lean hypothesis ("Selmer-minimal, resp. TYZ-certified, congruent curve has
   a point with each Selmer first coordinate"), with the descent formalized in Lean. Chance:
   medium, given 1 or 2.
4. **Status quo** (`E_ℓ` and RC).

**Single next step:** write the descent lemma for `C_d` with the multiplier fixed by the 2-adic
class of `β`, transposing the manuscript's slot construction (lines 1035–1061) to the linear
system in §4.4 of the note.
- Success: a proof whose algorithm reproduces solutions on the smooth-`θ` family, each passing
  `sel2cong.py`.
- Chance: medium–high.

## Open questions

- The uniform descent lemma, especially for a fixed multiplier and `θ` with many primes. There
  the suitable auxiliary symbol patterns are a small fraction (about `2^{−ω(θ)}`), so the proof
  must choose them by Dirichlet rather than count on them.
- Can the proof use the 64 multipliers? Heuristically they make the problem easy (29 of 30
  random inputs need no auxiliary prime), but a proof cannot rely on probability.
- The publication status of Kriz's preprint and of Smith's 2016 reformulation. For the TYZ
  variant, Smith's Theorem 2.2 (an F₂ identity) could be re-proved or checked independently.

## Suggested follow-up tasks

1. **cong-descent-proof.** Prove the descent lemma for `C_d` via Monsky matrices (Heath-Brown
   appendix; Smith §2), transposing the manuscript's slot construction (lines 1035–1061).
   Validate with `sel2cong.py` on the smooth-`θ` family (`descent_search.py`, generator
   `smooththeta`): the proof's algorithm must produce solutions there.
2. **tyz-descent.** The same lemma with Smith's bordered determinants as an extra condition, so
   that only published inputs remain. Audit TYZ Theorem 1.2 in the published AJM version and
   Smith's Theorem 2.2.
3. **kriz-audit.** Audit-style record for Kriz Theorems 1.1, 9.23, 10.13 and 10.17(2).
4. **pole-curve-switch (Lean).** Change `polePoly`, `poleT1` and `poleT2`, add the `x + l`
   valuation lemma, and re-check `poleTemplate_maj` and the parity lemmas. One Lean process.

# rv-lit: review of the two literature reductions

**Verdict: adopt the variants as drafted, with the two listed changes** (FunctionalEquation5 on
`0 < Re s < 2`; GrossZagier renamed, with supplier BFH 1990 / Waldspurger / Friedberg–Hoffstein
1995). No further Lean repair is needed. lit-adopt (`9367dfa6`) made exactly these changes. Its
three variants compile here, each with only the axioms `propext`, `Classical.choice` and
`Quot.sound`. Full note: `docs/research/rv-lit.md`.

**Checks:**
- **Junk values.** The drafted FunctionalEquation5 is false (VERIFIED): Mathlib's `Γ(0) = 0` and
  `L(C_d, 2) ≠ 0`. On the strip it is true. The LSeries `tsum`, `analyticOrderAt` and the
  `Nat.card` junk in `localPolynomial` are never reached, because the half-plane is `Re s > 3/2`,
  `F` is entire, and residue fields are finite. `∀F` versus `∃F` is harmless because the
  continuation is unique and exists.
- **Mathlib L-series = standard L(E, s)** (VERIFIED by reading for all reduction types, including
  the split criterion in characteristics 2 and 3). The transcribed recipe matches PARI `ellan` up
  to `n = 300` on 29 curves: the `C_d`, and split and nonsplit multiplicative reduction at 2 and
  3. (`an_check.py`)
- **Conductor and root number.** For 30 values of `d ≡ 5 (mod 8)`, the conductor is `32d²` and the
  root number is `−1`. The functional equation holds numerically. (`fe_check.py`)
- **TYZRow5b.** It is the contrapositive of Proposition N's `T_5b` half (weaker: `ord ≤ 1`), plus
  Hecke's continuation. Independent sample, 30 values of `d` including the rank-3 cases 26565 and
  33117: 0 violations. (`tyz_sample.py`)
- **JHeightBound.** `J(u)` is N5's `j` (L510, L949). Its constant follows exactly from F2 + F3 + E4
  and `X ≥ 1`, so the J-form variants assume only steps A1-F3. `twelve_mul_ratHeight_le` is a Lean
  theorem, true for every `u` (sample: 30 values, `f4_check.py`).

**Note repairs (do not block adoption):**
- **N1.** wk-cr3 §3 calls the drafted FunctionalEquation5 true and cites Murty–Murty.
- **N2.** wk-cr3 §1.3's claim "only TYZ among refereed theorems" depends on the publication status
  of Kriz's 2-converse (arXiv:2002.04767), which is unknown.
- **N3.** wk-h §1 classes A9, C3 and C9 as W, but each contains a passage new in N5. Roughly 12
  steps are W, not 15. The verdict is unchanged.

Not checked: the journal texts (TYZ, GZ, BFH, Birch–Stephens), and wk-h's Tier-2 fake model
(SPECULATIVE).

# rv-h-b1: adversarial review of route B1 (h-b1.md)

Deliverable: `docs/research/rv-h-b1.md`. Scripts: `scratch/rv-h-b1/rv_checks.py` (R1-R7) and
`b1_checks_rerun.py` (the h-b1 script, rerun with byte-identical output). Log:
`scratch/rv-h-b1/log.md`.

**Verdicts.**
- Counterexample F1: **holds**. It is a twist by `p` of a cover that has good reduction. It
  also shows that unramified branch fibres alone do not rule out vertical ramification, so NV's
  `W`-step is essential.
- Prop. TS: **holds as stated** (cosmetic: excellence/finiteness, flatness).
- Lemma NV: **holds as stated**. Every step was checked. Step 3 needs a fuller sentence. Step 2
  needs only conductor prime to `p`: a complete enumeration (VERIFIED, R2) shows every elliptic
  CM order in `O` is maximal (disc −3, −4, −24), with `W`-images `w₂, w₃, w₆`. The step is also
  robust to the branch labelling.
- M3 `|Γ'| = 144 = 2⁴3²` and maximality of `O`: VERIFIED.
- Lemma PR(i) and (ii): **hold**. (ii) is valid at `v | 2`, since `ℓ = 3` differs from the
  residue characteristic.
- Replacement table: **holds after repairs**.
  - The conjugate good-reduction line is N5 L557-558, not L563-566.
  - The downstream uses L753 and L781 are missing.
  - L814 never used b11: confirmed.
- Independent support (VERIFIED, R7): Elkies' constants `−1, 3` give `X₆ → P¹_j` no vertical
  ramification at `p ≥ 5`. Prop. TS matches real biquadratic fibre fields in 30/30 samples.
- **B1 removes b11 from H's justification: yes.** It rests on published theorems plus the
  reviewed Prop. TS and Lemma NV. The locators are still unread (no network).

**Most serious issue (a citation, not a gap).** NV (canonical model, reciprocity), PR(ii)
(moduli `K`-points) and N5 (Baba–Granath's `j`) must use one `ℚ`-structure on `Y₃ = Sh_{K₃}`.
Before B1 this sat in b11's sentence N5 L476-477. After B1 it needs explicit STANDARD
citations: Shimura 1967 / Deligne for canonical model = moduli; Rotger for uniqueness of the
`μ`-principal polarization; the automatic Weil-pairing compatibility; level-3 rigidity.

**Single next step.** Apply repairs 1-6 of rv-h-b1.md §8 to h-b1.md and merge it into H's trust
statement. Then read the actual texts of the four citations in §7, together with SGA 1 XIII 5.3
(Abhyankar), to fix the locators.

# loc-adopt results log

Input: docs/research/locators.md (AI locator audit, 2026-11-12). Base commit 6988c7fe.

## Findings
- VERIFIED (counted in ~/tyz-src/Period7.tex, L244-259: all theorem-like environments, including
  `definition` (L252), share the per-section `thm` counter): §2 = Thm 2.1 (L554), Thm 2.2 `LQ`
  (L571), Prop 2.3 `odd` (L580), Thm 2.4 (L613), Lemma 2.5 (L646), Thm 2.6 `thm2.3` (L809),
  **Definition 2.7** `def primitive` (L842), **Lemma 2.8** `lem2.6` (L1009, symmetry),
  **Lemma 2.9** (L1062, convolution). The earlier notes skipped Definition 2.7. §1: Thm 1.1 `lg`,
  Thm 1.2 `lg'` (L389), Remark 1.3, Cor 1.4. §3 numbering in the notes (Prop 3.4, Thm 3.5,
  Lemmas 3.16, 3.18, 3.21) agrees with the counter (21 environments, L1219-2504).
- Journal facts (Theorem 1.2 = journal Theorem 1.4, restriction kept; Lemma 2.9 in the journal):
  from the audit only, not re-read.
- Side finding (not in the audit, not changed): rv-tyz-inputs.md calls `multiples1` "Lemma 3.9";
  by the §3 counter `multiples1` (L1919) is Lemma 3.15 and 3.9 is Corollary `integral5` (L1586).

## Edits
- Step 1: h-decomposition.md §0 (list items 1-3, 5-22, dated audit paragraph, TYZ paragraph),
  §1 route K (K1-K4 audit bullet, count 19), §2 R1-R22 (R2 restated, R3 locator Example 29, R5
  count corrected, audit notes on R1, R6-R22), T27 (Chia-Fu Yu 2013 Thm 1.1, "indefinite"),
  §2.3 route K count, §6 R1 and R2 updates. No count of leaves changed.

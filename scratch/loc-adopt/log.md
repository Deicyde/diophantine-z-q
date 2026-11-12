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
- Step 3: TYZ renumbering (convolution Lemma 2.8 -> 2.9, symmetry Lemma 2.7 -> 2.8; arXiv Thm 1.2 =
  journal Thm 1.4, per the audit) with a dated note in nt-tyz, cr3-trust, rv-tyz-inputs,
  pn-design, rv-pn-encoding, rv-prop-n, rv-nt-tyz; nt-tyz numbering list gains Definition 2.7.
  Docstrings/comments of TYZInputs.lean and PropN.lean updated; `LemmaTwoEight` kept, docstring
  says it encodes Lemma 2.9.
- scratch/loc-adopt/check_code_unchanged.py (strips nested block comments, docstrings, `--`
  comments outside string/char literals; whitespace-normalized compare with 6988c7fe):
  IDENTICAL for both Lean files (45 and 1527 code lines). Negative control (temporary rename of
  `lemmaN1`) gave DIFFERENT, exit 1.
- Step 2: h-trust.md: header paragraph; dated notes in A2 (Lin–Yang Example 29, Baba–Granath
  locators, branch-data caveat), A5 (h-b1 M4 applies 4, 6, 2 to Y₃ → P¹_j: possibly a supplier
  change, SPECULATIVE; argument unchanged, separate review), A7, A10 (González–Rotger count with
  orientation factor; argument unchanged), C4, C7, C8 (Kato all levels), D2 (m = 3 boundary), D5
  (Carayol), E2, E3, E4, F1 (Example 29; Igusa signs UNVERIFIED), F3 (Pazuki +log π), §2.5.
- Finding (read, not re-derived): h-cm.md §5 (L193-233, L342-350) and rv-h-cm §3 already use
  `#CM(𝔬) = 2^b h(𝔬)`, b = #{p | 6 inert in K}; the wrong count `h(R)` was only in
  h-decomposition's leaf R5 (and h-trust gave no count). Recorded in R5 and A10.
- Finding (read): h-b1 M4 (table, L172) and Lemma NV step 2 (L232) use the indices 4, 6, 2 for
  `Y₃ → P¹_j` (cyclic inertia of order e_i). Not the degree-4 cover the audit corrects.
- Extra (VERIFIED by the §3 recount, not in the audit): rv-tyz-inputs.md called `char'` "Lemma 3.8"
  and `multiples1` "Lemma 3.9"; they are Lemma 3.14 (L1868) and Lemma 3.15 (L1919). Fixed in place
  with a dated line in its correction block. tyz-t1.md (not editable here) still says "Lemma 3.8"
  for `char'` (6 places).

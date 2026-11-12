# loc-adopt (2026-11-12)

**Result.** The locator audit (`docs/research/locators.md`, AI agents with web access) is applied
to h-decomposition.md, h-trust.md, the seven TYZ notes and the docstrings of `TYZInputs.lean` and
`PropN.lean`. Each file gets a dated note. The audit's UNVERIFIED marks are kept, and every note
says "read by the audit", not human-verified.
- **R2 restated.** `V → V/W` has index 2 at each branch value; `4, 6, 2` are orbifold orders.
- **R3.** The locator is Lin–Yang arXiv v1 **Example 29**, not 30. Baba–Granath Prop. 3.6 is an
  alternative supplier.
- **R5 corrected.** The count carries the orientation factor `2^{#{p | D(R)N(R)}}`.
- **Other leaves.** Locators and qualifications for R1, R6-R22, K1-K4 (Kisin 2009 Cor. 0.3 as a
  published alternative to Ribet; route K has 19 leaves if K4 is dropped) and T27 (Chia-Fu Yu
  2013 Thm 1.1, "indefinite" kept).
- **Arguments not changed.** In h-trust, A2/A5 (branch indices, via h-b1 M4) and A10 (the CM
  count) are flagged for the separate review. h-cm already uses the count `2^b h(𝔬)`.
- **TYZ.** The convolution is Lemma 2.9 and the symmetry lemma is Lemma 2.8. This is VERIFIED for
  arXiv v1 by recounting the counter in `Period7.tex`: the notes had skipped Definition 2.7.
  arXiv Theorem 1.2 is journal Theorem 1.4, with the restriction kept (from the audit).
  `LemmaTwoEight` keeps its name; its docstring says it encodes Lemma 2.9.
- **Extra finding** from the recount: `char'` and `multiples1` are Lemmas 3.14 and 3.15, not 3.8
  and 3.9 (fixed in rv-tyz-inputs; tyz-t1.md, outside this task's scope, still wrong).

**What compiles.** `lake build ZInQKernel` exits 0. `print_axioms`: all 91 lines are
`[propext, Classical.choice, Quot.sound]`. The comment-stripped code of both Lean files is
IDENTICAL to 6988c7fe (`scratch/loc-adopt/check_code_unchanged.py`, with a negative control).

**What remains.**
- The review of A5's and A10's use of the corrected R2 and R5 data.
- The `Leaves.lean` docstrings (R2, R3, R5, T27 indefinite, R14 Eisenstein case).
- Other notes that still say "Example 30" or "indices 4, 6, 2" (glue-repo, hdec-*, pkg-I1,
  h-b1, h-v14, wk-h, rv-leaves-a, tyz-t1).
- The unread originals listed in the audit.

Report: `docs/research/loc-adopt.md`; log: `scratch/loc-adopt/log.md`.

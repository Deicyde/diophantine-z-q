# up-map: fleet report

**Verdict.** The map is done: `docs/research/up-map.md`, with its log and scripts in
`scratch/up-map/`.
- **Coverage.** It covers N5 through V16, the October 11 manuscript and the 214-variable proposal.
  For each version it records the file, the date, the main theorems, the deep inputs and where
  the analogs of Thm 4.1, 5.2, 5.3 and Prop 6.2 sit, with line numbers.
- **Release records.** It summarizes the release records of research/version6–16 and upstream's
  theorem-application audit.
- **Nothing the fork relies on was removed or weakened (VERIFIED).** Every N5 statement the fork
  formalizes or assumes appears byte-identical in V16. That covers:
  - Theorem 1.1, the FrozenTarget polynomial, now numbered Theorem 1.3;
  - Theorem 4.1, H, now 4.2, with the same constants;
  - PC, with the same pole polynomial and template x + 3ℓ;
  - RC;
  - 22P;
  - the catalogue definition and bound;
  - the literal cutoff.
  §§9–12 of N5 (compiler, bridge, cutoff and size) are byte-identical in V16.
- **What changed is in the proofs**, in V10 (Issue 2) and V14:
  - **H:** the modularity step now goes through a published statement, Calegari ICM 2022 p. 624
    (proof source Pan), in a new Lemma 4.1. The integral model is now written out in the
    manuscript.
  - **22P:** the Green–Tao–Ziegler inverse theorem was replaced by upstream's own proof of GI.
  - **V16** changes no line of N5's §§1–13. Its three corrections sit in the GI Part, the
    simultaneous-primes appendix and the 222-family height section.
- **Upstream's new work does not use H, PC or 22P.** The quartics (down to 299 and 314
  variables), the 222-variable family (ineffective N₀, via Von Buhren) and the 214-variable
  proposal all run on different inputs:
  - a five-contact height estimate with a discriminant-210 Shimura curve;
  - a seven-variable pole lemma derived from RC;
  - Gaussian simultaneous primes;
  - GI.

**Most important finding.** For H, V16 §4 is V14 §4 with one supplement (b11) inlined; nothing
else in the section changed after V14.
- So the fork's `docs/research/h-v14.md` carries over to V16 line for line: +25 lines, and +24
  after V14 l.785.
- One upstream record does bear on the fork's H trust statement:
  `research/version14/proofs/a001-moduli-current-v1/ADVERSE-CASE.md`.
  - It records a defect in the proof of Baba–Granath (CJM 2008) Prop. 3.7, including a direct
    counterexample to one printed sentence.
  - Lin–Yang's eq. (2) Igusa formula is attributed to Baba–Granath Prop. 3.9, and 3.9 uses 3.7.
  - Upstream therefore routes around it with its own `ly-d6` and `igusa-theta` proofs. Both are
    still "pending review" upstream.
  - The fork's h-trust.md (l.89) cites Baba–Granath 2008 and Lin–Yang 2020 directly, in place of
    those supplements.

**Single next step (for up-h).** Leaf F1 of h-trust.md (l.688–696, `j` in theta constants)
already does cite Lin–Yang eqs. (2), (14) and (13). It also cites Igusa 1967 and
Lauter–Naehrig–Yang, and `igusa_check.py`.
- Decide whether F1 stands on Igusa 1967 together with the computation alone.
- If it does, drop Lin–Yang eq. (2) from F1's suppliers.
- If it does not, record the Baba–Granath Prop. 3.7 → 3.9 → Lin–Yang (2) ancestry as a
  qualification in h-trust.md.

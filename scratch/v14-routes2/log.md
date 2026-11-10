# v14-routes2 log

- 2026-11-10: fresh start (no earlier log). Copies of V13/V14 with CRs removed, the diff and the
  hunk list live in ~/gt-src/scratch-v14b/ (outside the worktree; never committed).
- `scripts`: scratch/v14-routes2/hunks.py lists the 72 unified-diff hunks with line ranges and the
  enclosing section (prints no manuscript text beyond headings and labels). Same 72 hunks as
  `git diff --no-index`; CR-stripped counts +2948 -688 (git counts +2953 -693: five lines differ
  only in line ends).
- First pass: hunks fall in §1 (H03-H04), §3 (H05), §4 height (H06-H14, large), §5 pole
  (H15-H18), §6 (H19-H21), §7 RC (H22-H26), §14 base compiler (H27-H35), §14/15 (H36-H37),
  §18 (H38-H39), App B, D, E, F (H40-H52), App H deleted (H53), simultaneous primes (H54-H55),
  V12 section (H56-H58), V13 394 section and new V14 section (H59-H72).
- H01-H05 read: title/date/abstract/intro version paragraph, a pointer to upstream's
  research/version14/SUPPORTING-NOTES.md, and the class-number sentence in prop:generator
  (Minkowski bound replaced by norm-Euclidean). Exposition.
- H06-H14 read (§4): thm:height statement and the H_6 constants unchanged; the PROOF is
  repaired: new lem:qm-modularity-descent (V14 L480-669) citing Calegari ICM 2022 p.624 for
  Pan's modularity; Berger and Conrad local algebraicity dropped; App H (lem:de-rham-descent)
  deleted, absorbed; Baba-Granath printed form is 6x the det-one form; integral model and its
  identification with the adelic curve (Deligne 1971 PEL) rewritten; Igusa normalization
  eq:qm-normalized-igusa derived from Lin-Yang Ex. 29-30; Hom-field/unramified proof expanded;
  conductor via r_ell for every ell (Carayol); complement via Milne Prop 12.1; theta via Igusa 1967.
- Calegari arXiv:2109.14145v1 source fetched to ~/gt-src/scratch-v14b/dl-calegari-src/: the cited
  "p.624" is a survey sentence (Survey.tex L630-633): Pan proves modularity up to twist of any
  geometric rho: G_Q -> GL2(Qbar_p), p >= 5, assuming distinct HT weights and odd. Not a
  numbered theorem.

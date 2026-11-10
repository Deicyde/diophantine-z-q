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
- H15-H26 read. §5: non-CM argument for E_ell made explicit (RC curves); Lemma 5.4 proof
  (maximal divisible subgroup; Poonen-Stoll Cor 4, 7, Thm 8); Lemma 5.5 proof (BCDT via Silverman
  C.13.6; Kolyvagin now cited from Proc. ICM Kyoto 1990 pp. 429-436, Thms 1-5 pp. 430-431,
  instead of MPIM preprint MPI/90-69; explicit J_1(N) -> A quotient). Statements identical.
  §6: Prop 6.2 statement identical; proof's GI(20) source changed from GTZ arXiv v5 + erratum to
  `local-gi`, a project supplement (quartic-local-gi-supplement.pdf, 8 Nov 2026). §7: RC proof
  (DD Crelle Thm 1.8 -> DD Annals 2010 Thm 1.4; Amir-Hong newform; Shimura quotient; native
  genus lattice paragraph; Cornut-Jetchev Thm 3.1 -> project conductor-one supplement).
- H27-H37: quartic route (H5 height proof: full-three model, PEL, the Calegari/Pan lemma now
  shared; V13 comment "UNAPPLIED CANDIDATE: ... published Pan match pending" removed; 41-form
  prime pattern now via local-gi). H38-H39: degree-four section, Kollar -> Colliot-Thelene-
  Salberger. H40-H43: App B/D records. H44-H52: App E/F RC repairs (Kato cochains; DD; Ribet
  1990; CJ -> project). H53: App H deleted. H54-H55: Gaussian prime appendix (Dodos-
  Kanellopoulos -> Green-Tao Prop 10.1 + local-gi; new majorant lemma). H56-H58: V12 layout.
  H59: sec:v14 inserted at V14 L22784-23739 (offset +22783 from the earlier addition.tex line
  numbers; only refs sec:v13, subsec:v12-inputs and own labels). H60-H72: bibliography.
- stmts.py: statements of prop:generator, thm:height, lem:pole, hyp:PC, hyp:RC, lem:corank,
  lem:forward-rank, prop:fixed-prime-pattern, lem:assembly identical V13 -> V14; proofs of
  thm:height, lem:corank, lem:forward-rank, prop:fixed-prime-pattern, prop:generator changed.
- Calegari definition of geometric (Survey.tex L124-128): irreducible, unramified outside finitely
  many primes, pst (equivalently de Rham) at p.
- Our notes: GoodPrimeDensity does not use GTZ (nt-22p L539). h-leaves I1 (Carayol) now cited
  in V14 (carayol1987, L1481); I2 (mu_sigma extends) still uncited (V14 L1459-1460).

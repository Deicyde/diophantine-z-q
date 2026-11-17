# htnew-print results log

Base: c0f3d085 (main; `git merge origin/main`: already up to date, 2026-11-16 22:50 PST).

## Inputs read
- ht-exists (7088f9ed): KatoHTExists (existence form, semisimple witness, geometric Frobenius, HT {0,k-1}),
  flag "pending reading" (3 reading points: filtration jumps / sign convention, Frobenius normalization,
  semisimplicity via Ribet). VERIFIED read (docs/research/ht-exists.md on the branch).
- ht-bypass (16db7d60): one consumer (G12Weight, l = 5, k >= 3). VERIFIED read.
- htnew-det: determinant route circular. VERIFIED read.
- newform-dict (e9683dac): IsNewform <-> Tau Ceti Newform, proved. VERIFIED read.
- On main: TateTwistInvariants and AxSenTate are PROVED (ZInQKernel/Contrib/OneProof/TateTwistInvariants.lean,
  AxSenTate.lean: ZInQ.Contrib.CloudB3W11.tateTwistInvariants_proof, axSenTate_proof). VERIFIED (read).
- CONTRIBUTING.md l.38-41: a new printed leaf counts published (flag unread); a leaf whose print may say
  something weaker is flagged pending reading and counts GLUE. VERIFIED read.

## Plan
New leaf robust to every ht-exists reading point: (i) normalization disjunction (arith Frob & HT {0,1-k}) or
(geom Frob & HT {0,k-1}); (ii) no semisimplicity (semisimplification preserves HT weights: proved in Lean);
(iii) trace-only Frobenius clause; (iv) printed newform (Tau Ceti Newform, via newform-dict).
- EigenformHTPrinted.lean §1-§6a (HTDual copy; diagonal reps semisimple, invariant line, conjGR, diagGR) compiles (lake env lean, 17 s). VERIFIED.
- §6b sum_finrank_Ysp_le, finrank_Ysp_le_diag (dim Y_i(rho) <= dim Y_i(diag) for upper triangular rho) compile. VERIFIED.
- §6c ht_diag, exists_ss (semisimplification of a 2-dim HT rep is HT with the same weights, same traces, unramified where rho is) compile. VERIFIED.
- §7 ModularHTPrinted (leaf), eigenformHTNew_of_printed (discharge, with LEAF field eigenformCoeffFieldFinite), printed_of_eigenformHTNew (converse over dsThm965Printed, eigenformCoeffFieldFinite, dsThm966Printed), printed_iff compile; axioms standard (scratch/htnew-print/axioms.txt). VERIFIED.
- Contribution ZInQKernel/Contrib/OneProof/EigenformHTPrinted.lean = scratch copy; no #eval/run_cmd/notation/macro/axiom/sorry (grep). VERIFIED.
- lake build +Main +Discharges +EigenformHTPrinted: success (14229 jobs, 15 min). VERIFIED.
- #discharges: DISCHARGES [OpenResearchLeaves31.eigenformHTNew] by EigenformHTPrinted.eigenformHTNew_of_printed,
  still assumes [ModularHTPrinted, DSCoeffExt.EigenformCoeffFieldFinite], standard axioms; 35 open, 9933 checked,
  37 discharge one (Discharges-output.txt). VERIFIED.
- autofold --dry-run: strict 11/18 on 29 -> 12/17 on 29; strictest 11/18 -> 12/17; FoldDryRun.lean compiles,
  sixContactMin_of_open49 standard axioms. VERIFIED.
- Leaf rating: published, flag unread (printed existence form; survey locators Taylor 2004 / Gee 2022 UNVERIFIED);
  alternative rating consequence (of Kato's V_{F_lambda}(f) statement) -> count neutral. SPECULATIVE judgement.

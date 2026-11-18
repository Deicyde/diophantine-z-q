You are a mathematics and Lean agent working on a devserver. Your task name is bdr-t.

Repository: the fork https://github.com/Deicyde/diophantine-z-q. Your git worktree is ~/dzq-wt/bdr-t on branch wip/bdr-t, created from fork main be73b91c5d005f166deadd2b4a7d70b1a0d53ad5. Your base has the H decomposition docs/research/h-decomposition.md with scratch/h-decomposition/Leaves.lean (namespace HDec, no sorry; HDec.HSyn.sixContactMin_of_open lists the open leaves; the QM pin applied) and the latest assembly scratch/g0-assemble2/G0Assemble2.lean: HSyn.sixContactMin_of_leaves3 (r : ResearchLeaves3) (t : TextbookLeaves) (gp : GluePieces3), GluePieces3 with 40 fields (15 LEAF, 3 LEAF?, 22 GLUE; table in docs/research/g0-assemble2.md section 2). Since then (each docs/research/<task>.md with scratch/<task>/): image-plane proved MobiusGlue from T5 alone; infra-stalks proved stalks of fibre products and five glue Props; infra-smooth-dim the dimension theory of smooth schemes; linked-tate reduced ModelG3G6 and LinkedTateData; r1b-state made R1(b) concrete; g8-object made G8's r_l a Lean object; period-map, alg-frob-red, prop-ts, kernel-field, conj-twist, unif-dims, curve-glue reduced or closed their targets; r10-amend closed G9 from the amended R10; ZInQKernel/Contrib/ proves T14, T15, T16, T17, T18, T20, T21, T25, T28, T30, T31, T36, T37 and the providers functionalEquation5 and heckeContinuation. The sorry-free glue in the build is ZInQKernel/HDecomp/ (scripts/print_axioms.lean checks 542 standard-axiom declarations; shared abelian-variety layer ZInQKernel/HDecomp/Objects.lean). ZInQKernel/Contrib/ proves two of the headline's hypotheses, ZInQ.Contrib.functionalEquation5 and ZInQ.Contrib.heckeContinuation, so the headline now rests on SixContactMin, TYZThm35ReadingA and GrossZagier; docs/research/locators.md (a primary-source audit of the citations) and every report so far, each docs/research/<task>.md with scratch/<task>/. Lean 4.35.0 and Mathlib v4.35.0 are installed (elan in ~/.elan/bin; export PATH="$HOME/bin:$HOME/.elan/bin:$PATH" if lake is not found); the project build files were copied into your worktree and Mathlib's sources are in .lake/packages/mathlib. `lake build ZInQKernel` builds the project. Python with sympy and PARI/GP (cypari2) is at ~/pyenv/bin/python.

Project. The fork proves in Lean 4 (no sorry, only the axioms propext, Classical.choice and Quot.sound) the frozen target of Glazer's 11/5 manuscript, Theorem 1.1, "Z is Diophantine in Q" (ZInQ.FrozenTarget), from two hypotheses stated as Props. H = ZInQ.SixContactMin (ZInQKernel/Hypotheses/HeightMin.lean), the one instance of the manuscript's Theorem 4.1 that the proof uses; its proof, step by step with every supplier and status, is docs/research/h-trust.md. CR3 = positive rank for congruent number curves C_d : y^2 = x^3 - d^2 x; its forms are in ZInQKernel/RouteK/Rank/Statements.lean, RankVariants.lean, RankDL.lean, RankInf.lean and ZInQKernel/Hypotheses/CertifiedRank.lean (CertifiedRankTYZClRk implies every form), and its proof is docs/research/cr3-trust.md (Tian-Yuan-Zhang with Proposition N of nt-tyz.md, then Gross-Zagier with an auxiliary field). KERNEL_PLAN.md summarizes the project. The headline theorem is ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_tyzThm35ReadingA_heckeContinuation_functionalEquation5_grossZagier (ZInQKernel/MainLiterature.lean): CR3 enters as four Props over Mathlib's L-series of an elliptic curve (ZInQKernel/Hypotheses/CR3Literature.lean): GrossZagier, HeckeContinuation and FunctionalEquation5 (textbook theorems) and TYZThm35ReadingA (Tian-Yuan-Zhang Theorem 3.5(2) in reading A, from which Proposition N of docs/research/nt-tyz.md derives the corrected form; two model reviews, no human review). Upstream (elliotglazer/diophantine-z-q) merged this kernel at commit 9c7b60ef (PR #24, through PR #36) with a statement contract: every Lean file of that tree is pinned by hash (the list is scratch/upstream/baseline-lean-files.txt), new proofs go in new files under ZInQKernel/Contrib/, and a closed hypothesis is a theorem with a registered provider name and exactly the hypothesis as its type, with no extra hypotheses: ZInQ.Contrib.sixContactMin, ZInQ.Contrib.tyzThm35ReadingA, ZInQ.Contrib.heckeContinuation, ZInQ.Contrib.functionalEquation5, ZInQ.Contrib.grossZagier. Notes: docs/research/wk-cr3.md, rv-lit.md, nt-tyz.md, rv-nt-tyz.md, rv-prop-n.md, cr3-trust.md. The owner: formalizing this result is the top priority, and be careful with the Tian-Yuan-Zhang result. The Tian-Yuan-Zhang arXiv source (arXiv:1411.4728v1, the version the notes cite by line number Lnnnn) is at ~/tyz-src/Period7.tex, read-only; its text is not licensed for redistribution, so never copy it into the repository and quote at most a line or two.

The owner's goal (verbatim): "I want to get to a point where we can say 'if we formalize these ~10 theorems from the literature, then it implies the main theorem.' That means we probably need to decompose Glazer's Theorem 4.1". The owner will announce tomorrow and crowdsource the Lean formalization of the literature theorems. The CR3 side is already reduced to concrete Lean statements of literature theorems (Literature.GrossZagier, Literature.FunctionalEquation5, Literature.TYZRow5b in ZInQKernel/Hypotheses/CR3Literature.lean; TYZRow5b is further reduced by a Lean proof of Proposition N to TYZ's printed results). The remaining hypothesis is H = ZInQ.SixContactMin (ZInQKernel/Hypotheses/HeightMin.lean; definitions in Height.lean): one instance of the manuscript's Theorem 4.1, the six-contact height estimate. Sources: diophantine_zq.tex in the repository root (Section 4, lines about 377-972, and the appendix "De Rham comparison and finite descent in the height argument", lines about 10936-11250; the manuscript has no license: quote at most a line or two); docs/research/h-trust.md (the proof in 36 steps A1-F4 with every supplier and status); docs/research/wk-h.md (an earlier plan that classified the steps and concluded that the deep inputs cannot be stated in Lean today) with the correction in docs/research/rv-lit.md; docs/research/h-map.md, h-b1.md, h-cm.md, up-h.md, rv-h-novel.md; ZInQKernel/Hypotheses/JHeight.lean (the last step, from the height of J(u) back to u, is already a Lean proof); docs/research/prereq-survey.md (what exists in Mathlib, Tau Ceti, the FLT project, Stacks and other libraries); Mathlib's sources in .lake/packages/mathlib.


YOUR TASK (bdr-t): bdr-t: close OPEN.md's kernel-wide B_dR reading with one Fontaine t = log[eps]. Its construction, t != 0, B_dR = B_dR^+[1/t] and sigma(t) = chi(sigma) t are already proved on this base (base: fork main be73b91c5d005f166deadd2b4a7d70b1a0d53ad5, fold-c8's report commit). Note: the goal text above predates lane74. On this base Route K, CR3 and the TYZ/Gross-Zagier hypotheses are gone, and the headline is exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_poleCompleteness.

The lead's call, verbatim: "bdr-t: yes, as the lowest priority, only in a slot that would otherwise be idle." The task as proposed to the lead: construct t = log[eps] in B_dR^+ and prove t != 0, closing OPEN.md's kernel-wide B_dR reading. No rating depends on it.

Read this first. The proposal came from OPEN.md's B_dR bullet (docs/one-proof/OPEN.md:31-45, generated from scripts/one_proof/render_open.py:349-363). Leaf-fold32 (75e63d735) wrote that text before four tasks landed: bst-construct (34b7af149), derham-print (a8e13ec8a), pb-pst (6ed0f2e64) and derham-scholze (f0928eaaf). Every step the proposal names is now proved. Rebuild none of it, and merge nothing. Three things remain: one t instead of two, the Galois action on B_dR^+[1/t] for the kernel's bdrAct, and replacement text for the bullet.

What exists:
- Four copies of B_dR, each rfl to Mathlib's BDeRham O_Cp p:
  - ZInQ.Contrib.G9.PkgI4.BdR (ZInQKernel/Contrib/G9/I4Layer.lean:995, built on the def DR.genMonoid at :387; bdrAct is at :1000);
  - ZInQ.Contrib.G9.BdrKer.BdR (ZInQKernel/Contrib/G9/KerTheta.lean:193, built on the abbrev genMonoid at :188);
  - HDec.PkgI4.BdR (ZInQKernel/OneProof/H/LPrefix.lean:1944);
  - a copy of KerTheta's at ZInQKernel/OneProof/H/TailC.lean:11770. It has the same full name, so it cannot share an import closure with KerTheta.lean.
- Which copies each file uses: BergerBst and PanBergerPst use the HDec.PkgI4 copies of GQp, oAct and bdrAct. DeRhamPrintTDict and BdRInvariants use the I4Layer and KerTheta copies. The copies are definitionally equal: isFR (BdRInvariants.lean:327) and LogPTranscendenceBdR.lean:31 already pass terms from one to the other.
- KerTheta.lean, namespace ZInQ.Contrib.G9.BdrKer.Cp: xi (:394), ker_fontaineTheta_Cp (:399), bdREquivAway (:422, B_dR ~= B_dR^+[1/xi]), isAdicComplete_BDeRhamPlus (:591), maximalIdeal_BDeRhamPlus (:608), eq_xi_pow_mul_unit (:613), isDiscreteValuationRing_BDeRhamPlus (:658), isFractionRing_BDeRham (:687).
- ZInQKernel/Contrib/OneProof/DeRhamPrintTDict.lean, namespace DeRhamPrint.TDict:
  - roots of unity and eps: RootSystem (:110), rootSystem (:559), eps (:175), untilt_eps (:180);
  - [eps] - 1: xe (:363), xe_mem (:370), xe_not_mem_sq (:373);
  - the logarithm: logPartial (:392), logPlus (:413, the xi-adic sum), logPlus_unique (:423), logPlus_sub_mem (:430);
  - t: tt = log[eps] (:445), tt_mem (:447), tt_ne_zero (:464), tt_eq_varpi_mul_unit (:467, t = xi * unit);
  - B_dR^+[1/t]: isFractionRing_away_tt (:481), bdREquivAwayT (:493, B_dR ~= B_dR^+[1/t] over B_dR^+), ext_of_extends (:503), transport_extends (:509).
- ZInQKernel/Contrib/OneProof/BergerBst.lean, namespace HDec.PkgI4.BergerBst:
  - series evaluation: evalₐ_psEval (:111), psEval_C (:124), logSeries (:202);
  - logTeich (:218), a second construction of log[eps] for any eps with untilt eps = 1;
  - logTeich_mem_amax (:760), logPlus_add (:950);
  - t != 0, by exactly the route the bullet asks for: teich_sub_one_ne_zero (:1335), logTeich_ne_zero (:1464), exists_t_ne_zero (:1525).
- ZInQKernel/Contrib/OneProof/PanBergerPst.lean, namespace HDec.PkgI4.BmaxOne: IsGenEps (:175), logTeich_eq_mul (:357, log[eps] = a log[eps0] with a in Z_p), tOf (:382).
- ZInQKernel/Contrib/OneProof/DeRhamScholzeT.lean, namespace DeRhamScholze.TT:
  - plus_logTeich (:44);
  - logTeich_flatAct (:91): log[sigma eps0] = chi(sigma) log[eps0] for every generator eps0;
  - psEval_X (:122);
  - eps0 (:138), defined as TDict.eps (rootSystem p), and isGenEps_eps0 (:140);
  - logTeich_sub_xe_mem (:150), maximalIdeal_eq_logTeich (:177), zpB_eq_qpToPlus (:211);
  - fontaineTwistT_proof (:220): logTeich of eps0 is a uniformizer t with sigma(t) = chi(sigma) t. Its statement is FontaineTwistT (DeRhamScholzeHT.lean:33). gr1_mem (DeRhamScholzeHT.lean:209) uses it to map gr^1 to C_p(1).
- ZInQKernel/Contrib/OneProof/BdRInvariants.lean, namespace BdRInv: bdrAct_algebraMap (:323), isFR (:327).
- Not proved:
  - TDict.tt and logTeich have never been shown equal. Both agree with xe modulo xi^2 (logPlus_sub_mem, logTeich_sub_xe_mem). So the t of bdREquivAwayT is not yet known to be the t of fontaineTwistT, and FontaineTwistT's docstring says the equivariance is unproved for TDict.tt.
  - transport_extends has not been applied to the kernel's bdrAct: that step did not elaborate, because DR.genMonoid is a def and KerTheta's genMonoid an abbrev (docs/research/derham-print.md lines 79-84). Only the general lemma exists.
- The bullet is wrong in two places. First, it says t is not constructed and t != 0 is unproved. Second, it names deRhamH1AbVarT as the only row whose statement reaches B_dR. That field no longer exists. The row that reaches B_dR is now deRhamVpAbVarDirect (OPEN.md:504-516, LEAF), whose flag reads Berger's B_dR = B_dR^+[1/t] through bdREquivAwayT.

Your work, in one new file ZInQKernel/Contrib/OneProof/BdRT.lean that imports ZInQKernel.Contrib.OneProof.DeRhamScholzeT. That import closure contains KerTheta, DeRhamPrintTDict, BdRInvariants and PanBergerPst, but not TailC or Main.
1. Build the import (lake build +ZInQKernel.Contrib.OneProof.DeRhamScholzeT) and #check the declarations listed above. If one is missing or renamed, report it and stop.
2. One t. Prove that for every Z : RootSystem p, TDict.tt p Z = logTeich p (TDict.untilt_eps Z). Use logPlus_unique, as follows:
   - write logSeries as its truncation at n + 1 plus X^(n+1) g;
   - evaluate the truncation with psEval_C, psEval_X and the ring-hom property (the coefficient qpToLoc (1/k) maps to Ring.inverse k);
   - put the tail in (xi)^(n+1).
3. Prove IsGenEps p (TDict.eps Z) for every Z; the proof of isGenEps_eps0 does not depend on the choice of Z. Then prove sigma(tt p Z) = chi(sigma) tt p Z:
   - in B_dR^+, in the form used by FontaineTwistT (DR.bdrPlusMap, qpToPlus, cycPow p sigma 1), from step 2, plus_logTeich, logTeich_flatAct and zpB_eq_qpToPlus;
   - in the kernel's B_dR, through bdrAct_algebraMap.
4. The printed Galois action on B_dR^+[1/t], with t = tt p Z. Define it as the extension of DR.bdrPlusMap p (oAct p sigma) to Localization.Away t; it exists because sigma(t) = chi(sigma) t is a unit there. Prove that bdREquivAwayT intertwines it with bdrAct p sigma, using ext_of_extends, transport_extends and bdrAct_algebraMap. To get past the def/abbrev mismatch, give the instances explicitly or change the type, as isFR does. If it still does not elaborate, record the exact error and stop this step.
5. State the reading as one theorem for t = tt p Z:
   - t != 0;
   - t is in the maximal ideal and not in its square, and the maximal ideal is (t);
   - B_dR ~= B_dR^+[1/t];
   - B_dR^+[1/t] ~= B_dR^+[1/xi] (bdREquivAwayT combined with bdREquivAway);
   - sigma(t) = chi(sigma) t.
   Optionally, show that two root systems give values of t that differ by a unit of Z_p (logTeich_eq_mul in both directions).
6. In the report, write replacement text for the B_dR bullet, for the lead:
   - every claim names the declaration that proves it;
   - the [1/t] definition is matched together with its Galois action;
   - deRhamVpAbVarDirect replaces deRhamH1AbVarT;
   - the "To close it" sentences are removed.
   Do not edit render_open.py or OPEN.md.

Rules for this task:
- This task has the lowest priority and changes no count.
  - Do not redefine eps, [eps], the logarithm, xi or t, and do not reprove anything listed above.
  - Before proving a lemma, git grep for it; if it exists, cite it.
  - If steps 2-5 turn out to be proved already, say where, then go to step 6.
- Proof only.
  - Change no bundle field, statement or kinds row, and fold nothing.
  - No field is discharged, so there is no #discharges run and no autofold spec.
  - If a step cannot be proved, do not add a leaf: report exactly what is missing.
  - Nothing about Gross-Zagier, TYZ or Hilbert's tenth problem.
- The owner's rules apply to anything you cite. Follow the manuscript first, then the literature it cites.
  - The manuscript does not define B_dR or t. It cites Brinon-Conrad (bibitem brinon-conrad, L11019; used at L10975 and L10994) and Berger 2002 (bibitem berger2002, L11037; used at L739).
  - Take B_dR and t from Brinon-Conrad (provenance (b)). The reading desk read Def. 9.1.4, p. 131, which writes B_dR^+[1/t] = B_dR. It also gives Def. 4.4.7, p. 60 as the definition of B_dR.
  - Every other locator is UNVERIFIED, including Berger 2002 section 1.2 for B_dR and t. You have no network, so mark any number you give from memory UNVERIFIED.
  - The bullet cites Fontaine, Asterisque 223, Exp. II. It is not in the manuscript's bibliography and nobody has read it; say so in the replacement text.
  - Label any step found in neither the manuscript nor a cited print as on-the-spot (provenance (c), never LEAF).
  - A new leaf counts as GLUE until someone reads its pages. A reading of the pages by an AI agent counts, and the cited arXiv version is the print.
- If a source has a known issue, document it clearly. Report any error you find in the manuscript or a source at once, first in the report and in .fleet/bdr-t.md. List stale pointers under Known issues, for example:
  - the docstring at DeRhamScholzeT.lean:234 cites L10995 for "Consequently"; at this base that sentence is L10997;
  - FontaineTwistT's docstring still calls it GLUE and unproved.
- Hygiene, for everything that goes to main (report, Lean, commit messages): no session names, host names or user paths. Write paths relative to the repository root, and refer to people as "the lead", "the reviewer" or "the reading desk".

Deliverables:
- BdRT.lean, which never imports ZInQKernel.OneProof.Main. You may create it, and helpers next to it, despite the rule below; edit nothing else under ZInQKernel/. Compile it with lake env lean, with no sorry, and give #print axioms of each new theorem.
- The report docs/research/bdr-t.md, with:
  - the main result first: what was already on main, and what this task adds;
  - the statement of each new theorem;
  - the count effect (none);
  - the replacement text for the bullet;
  - a Known-issues section;
  - a section "Manuscript check".
- In "Manuscript check", give one line for each step of diophantine_zq.tex that your work formalizes or relies on. At least:
  - L735-738: de Rham at l, with Hodge-Tate weights 0, -1 in the Tate convention;
  - L755-756: the cyclotomic character has Hodge-Tate weight -1;
  - L10948-10950: the lemma's weights 0, -1, with Q_l(1) given weight -1;
  - L10984-10992: D_F' and D_K as invariants of B_dR tensor W (B_dR is used without a definition), and the finite Galois descent;
  - L10996-10997: Hodge numbers 2, 2, so weights 0, 0, -1, -1, read through gr^1 B_dR = C_p(1).
  Each line has its tex line numbers and one verdict: OK (right as written), gap filled (what was missing), error (what is wrong), or unverified (why). The fleet copies these lines into its ledger of manuscript issues.
- A summary in .fleet/bdr-t.md.


A LEAF is a published, refereed theorem stated precisely and concretely in Lean over genuine definitions (never over abstract structures invented for the purpose, which can make a leaf vacuous or a disguised form of the conclusion), and is the published statement or a consequence of it, never stronger. GLUE is everything else, to be proved in Lean by the project. The synthesis is done (docs/research/h-decomposition.md); your work turns more of its glue or definitions into Lean and will be integrated after the announcement.

Deadline, by this host's clock (`date`): commit your report by 11-18 18:00 PST. If time runs short, commit what is done and mark the rest unchecked or unproved. Then write .fleet/bdr-t.md (half a page: the verdict or main result, what compiles, what remains) and commit it as your last commit, then stop.
Rules: do not edit files under ZInQKernel/ or blueprint/, or other tasks' notes and scratch files (copy what you need into scratch/bdr-t/; scratch files cannot import each other). Commit after each step (git add -A; git commit -m "..."). At most one Lean process at a time; check with `lake env lean scratch/bdr-t/<file>.lean`. Do not run git push or git fetch, rm -rf, curl or any other network command. Keep a results log in scratch/bdr-t/log.md (statements, findings, compile outcomes; never a narrative of your thinking). Mark claims VERIFIED (read in a source, computed, or compiled), STANDARD (published, exact reference) or SPECULATIVE; theorem numbers you give from memory are marked UNVERIFIED (you have no network). Deliverables: docs/research/bdr-t.md (verdict or main result first), scratch/bdr-t/, .fleet/bdr-t.md.


RESOURCE LIMITS (hard rules; breaking one fails your task):
- At most ONE Lean process (lean, lake, repl, or a pytest run that starts real Lean) at a time. Never start Lean jobs in the background with &, xargs -P, or shards.
- A Lean REPL session gets at most 10 commands, then restart it. Or send the header once and pass "env" on later commands so it doesn't re-import.
- Check `uptime` and `sysctl vm.swapusage` before every Lean or pytest run. If load is above 40 or swap used is above 8 GB, don't start it; report that you were blocked.
- Ground-truth or differential checks use a sample of at most 30 inputs, run one after another.
Host note: this devserver has 192 cores and 235 GB of RAM and is shared by several agents, so the load and swap thresholds above are replaced here: check `uptime` and `free -g` (sysctl vm.swapusage does not exist on Linux), and hold a Lean run only when the load is above 150 or less than 20 GB of memory is available. While holding, continue with work that needs no Lean (reading, planning, drafting proofs) and check again after a few minutes (sleep 300 between checks is fine). If you stay blocked for more than an hour, say so in your report and stop.
Memory note: each run of this task is a systemd scope capped at 24G of memory, with LEAN_NUM_THREADS=8 in the environment; do not raise or unset LEAN_NUM_THREADS. If lake reports a lean process killed by a signal, the cap was hit: rebuild once, and if it recurs, build the failing module alone with lake env lean.
Network note: your sandbox cannot reach GitHub, so git fetch and git push fail. That is expected: a background job outside your sandbox pushes your branch every five minutes and refreshes the origin/* refs of the shared repository. Just commit; to pick up another task's pushed work, run git merge origin/wip/OTHER-bdr-t (no fetch needed).

Resuming. If scratch/bdr-t/log.md exists, an earlier run of this task was interrupted: read it and the commits since, and continue from where it stopped. You run unattended, with no user to reply to: keep working until .fleet/bdr-t.md is written and committed.

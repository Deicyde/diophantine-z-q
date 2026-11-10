# cr5b-lean log

- Start: plan files Rank5b/{Bordered,Matrices,Kernel,Row5b}.lean + root Rank5b.lean.
- Lemma 4.2 proof plan: no adjugate; direct kernel argument (v·k=0 → (k,0) in kernel; v·k=1 → trivial kernel).
- Bordered.lean (Lemma 4.2), Matrices.lean, Kernel.lean (Lemma 4.1 config level), Row5b.lean
  (Lemma 4.1 for Sel2, Thm 4.3, Cor 4.4, CertifiedRank5b, derivation), root Rank5b.lean (variant):
  all compile; `lake build ZInQKernel` OK (5m11s wall, full from partially built tree).
- Check.lean: det M5b 21 = 1, det M5b 5 = 0 by kernel (reindex to primeCfg, explicit entries,
  det_succ_row_zero + decide); ~9s. Incremental `lake build ZInQKernel` OK (26s).
- #print axioms: propext, Classical.choice, Quot.sound only; check_target.py OK.
- Report .fleet/cr5b-lean.md written. Done.

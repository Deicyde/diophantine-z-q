# rv-cr3-dl log

Review of feb18a7b (cr3-dl, RouteK/RankDL.lean) and 350f7798 (rv-cr3-rank follow-up).

- Started lake build ZInQKernel (output in scratch/rv-cr3-dl/build.out, not committed).
- Read RankDL.lean, Assembly/DL.lean, Assembly/PoleCompleteness.lean, Assembly/Data.lean (Inputs),
  Slots/Construction.lean (Slots, exists_slots, exists_multiplier_and_slots), RankVariants.lean,
  MainGreenTao.lean, Rank/Statements.lean, Hypotheses/CertifiedRank.lean, Covering.lean docstring,
  KERNEL_PLAN.md lines 120-170, manuscript lemma lem:corank (line 1072), tyz-5b.md §1, §4.
- Findings so far:
  * curves match: PC_of_CR applies CR3 at n.natAbs, (n*θ).natAbs with n = D.d₁ (descent_lemma);
    DLRk at D.d₁ and D.d₁ * θ.natAbs (= (D.d₁*θ).natAbs). D existential, PC proof uses it.
  * main variant: same assembly_AP chain as _sixContactMin_certifiedRank (unfolded by hand).
  * KERNEL_PLAN "…_certifiedRankRk assumes the least" contradicted by DLRk (Rk → DLRk is
    provable in a few lines; to check in scratch).
  * DLRk docstring: "or Kriz's 2-converse" does not follow from TYZRk → DLRk; needs Rk → DLRk.
- lake build ZInQKernel: success (9913 jobs), exit 0 (build-tail.txt).
- print_axioms: 45/45 entries [propext, Classical.choice, Quot.sound] (axioms.txt).
- Probe (deleted; text in report §5): Inputs (-7) 1 7, Nonempty (Slots (-7) 1 7),
  CertifiedRankRk → CertifiedRankDLRk all elaborate, standard axioms (probe.txt).
  Fixes during probe: Squarefree not decidable (used Prime.squarefree, squarefree_one);
  legBit 7 1 via simp [IsSquare.one].
- Report docs/research/rv-cr3-dl.md written: Lean no blocker; doc blocker B1 KERNEL_PLAN.md:152–155
  ("assumes the least"); remarks R1–R4.

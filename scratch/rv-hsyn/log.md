# rv-hsyn results log

- lake build ZInQKernel.Hypotheses.JHeight: success (build.out). VERIFIED.
- lake env lean scratch/h-decomposition/Leaves.lean: exit 0, no errors (leaves.out). VERIFIED.
- #print axioms (Leaves.lean, 20 printed theorems): only propext, Classical.choice, Quot.sound,
  except HSyn.sixContactMin_of_leaves (+sorryAx). VERIFIED.
- LeavesCheck.lean (copy + 20 more #print axioms + 1 example): exit 0 (check.out). 15 more cited
  theorems are axiom-clean; sorryAx exactly in glueOutputs_of_leaves, goodReduction_of_QM_rational3,
  artinConductor_le_of_upper, sq_principalUnits. `example : ResearchLeaves → TextbookLeaves →
  ZInQ.SixContactMin` compiles. VERIFIED.
- opaque placeholders (L9075-9178): R01 R02 R03 R05 R08 R16-R22 T09-T12 T23 T29 T32 = 19; matches
  note §0/§2.3. VERIFIED.
- Stated Props: 11 research (10 leaves), 28 textbook (25 leaves); all `def`s with content. VERIFIED.
- Finding: b3_degree_le_QM hypotheses are LeafHasse, LeafLocalTwo, LeafSqrtCrit, LeafUnramified;
  LeafHasse/LeafLocalTwo are not bundled in TextbookLeaves and not derived from PkgI6 forms. VERIFIED.
- Finding: §3 "GK1, GK2 NEW and unreviewed" contradicts §0, §1, §6 R3. VERIFIED (read).
- Finding: "weakened to 𝓛(n)=0" wrong direction; nt-tyz L275-278 F6. VERIFIED (read).
- Finding: G0-G20 = 21 rows incl. composition G0. VERIFIED.
- Finding: Bourbaki/SGA sources (R1, R14, R21, R6, R8, T1, T2) refereed status. SPECULATIVE.

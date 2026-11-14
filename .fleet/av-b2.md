# av-b2 (2026-11-13)

**Main result.** In group B of leaf-fold3, T9 and Serre's lemma are now glue, and two leaves are replaced by smaller
ones. `HDec.HSyn.sixContactMin_of_openB2 : ZInQ.SixContactMin` follows from **66** named Props (leaf-fold3 had 68,
of which 62 leaves; now 60 leaves). No `sorry`; axioms `propext, Classical.choice, Quot.sound` only.
Report: `docs/research/av-b2.md`.

**Declarations proved** (scratch/av-b2/olean/AVB2Main.lean, on leaf-fold3's chain, namespace `HDec`):
- `AVB2.t9_of_leaves3 : WeilPairing.T09_SymmIsogenyExists → WeilPairing.IsogenyQuasiInverse →
  LeafPush.T09_WeilPairing.{0}`. Field `t9` follows from two fields already in the list.
- `AVB2.serreRigidity3_of_T35 : ZInQ.LeafPush2.UniformizationExists → HomUnify.HomLatticeCorr →
  HeckeRest.SerreRigidity3`. Both inputs are fields already. The proof also uses the proved `MulIsogeny` for the
  descent `A(ℂ)[3] = A(ℚ̄)[3]`, plus Serre's lemma on the lattice.
- `AVB2.divisiblePoints_of_posChar : AVB2.MulIsogenyPosChar → WeilPairing.DivisiblePoints`. The new leaf says
  `[n]` is an isogeny in positive characteristic; characteristic 0 is the proved `MulIsogeny`.
- `AVB2.t11b_of_exists : AVB2.T11bExists → ZInQ.LeafPush2.T11b_Rigidity`. Uniqueness is proved
  (`baseChange_map_injective`); the new leaf is the existence half.
- `ZInQKernel/Contrib/AVB2/SerreLemma.lean` (Mathlib only): `eq_one_of_pow_eq_one`, `eq_zero_of_smul_mem` and
  `lattice_serre`, which is Serre's lemma for a matrix `≡ 1 (mod 3)` of finite order.

**What compiles.**
- The olean chain (scratch/av-b2/chain.sh) and `AVB2Main.lean`: 0 errors.
- `lake build ZInQKernel.Contrib.AVB2.SerreLemma`: OK.
- The flat single-file check `scratch/av-b2/AVB2Flat.lean` (built by `assemble.sh`; leaf-fold3's `Leaves3.lean`
  verbatim plus this task's part, checked by `verbatim_check.sh`): exit 0 in 1037 s, no `sorry`. All 293
  `#print axioms` lines are standard.

**What remains.**
- `t09SymmIsogenyExists`, `isogenyQuasiInverse`, `t10` (pro-étale `H¹`) and `t4` (Serre–Tate reduction of torsion)
  are confirmed as published statements, never stronger. References are in the report (§2.4–2.7; locators
  UNVERIFIED).
- The new leaves `MulIsogenyPosChar` and `T11bExists` stay open.
- `divisiblePoints` can be dropped altogether with t5-torsion's rewiring, which would make the count 65.

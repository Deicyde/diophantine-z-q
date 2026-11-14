# av-b2 results log

Task av-b2 (2026-11-13). Base: 8ec80711 + origin/wip/leaf-fold3 (f7951690) merged (55904cbb).
Targets (group B of docs/research/leaf-fold3.md §3, minus t5, t26, t27, t35, homLatticeCorr, t6, t7, t8):
`t4`, `t9`, `t10`, `t11b`, `t09SymmIsogenyExists`, `isogenyQuasiInverse`, `divisiblePoints`, `serreRigidity3`.

## Setup
- `lake build ZInQKernel.Hypotheses.JHeight` needed first (builds the upstream `lean/` package `ZInQ.*`); OK.
- Olean chain: leaf-fold3's `olean/*.lean` sources copied to `scratch/av-b2/olean/`; `scratch/av-b2/chain.sh`
  (copy of leaf-fold3's) compiles them with `scratch/av-b2/ctail.sh` (oleans written to scratch/av-b2/olean, gitignored).

## Statements read (VERIFIED, scratch/leaf-fold3/Leaves3.lean)
- `t9 : LeafPush.T09_WeilPairing.{0}` (l.11905). weil-pairing's `WeilPairing.oldT9_of_symmIsogeny`
  (l.49811) proves `OldT9.T09_WeilPairing` (verbatim copy with `Type u` → `Type`) from
  `T09_SymmIsogenyExists` and `IsogenyQuasiInverse`, both already fields of `OpenAddedLeaves3`.
- `divisiblePoints : WeilPairing.DivisiblePoints` (l.50148): all fields `K`, all `n > 0`, `[n]` onto on `A(K̄)`.
  `G0FibreSimple.MulIsogeny` (proved, `HSyn.mulIsogeny_proved`) gives `[n]` finite + surjective in char 0.
- `serreRigidity3 : HeckeRest.SerreRigidity3` (l.98709): over `Qbar = AlgebraicClosure ℚ`.
- `t10 : T10Etale.T10_TateDuality` (l.27887): over Mathlib's pro-étale `Scheme.EllAdicCohomology`
  (Mathlib/AlgebraicGeometry/Sites/ElladicCohomology.lean:76), a genuine definition; no comparison theorem
  for pro-étale cohomology of abelian varieties exists in Mathlib.
- `t11b : ZInQ.LeafPush2.T11b_Rigidity` (l.21477).
- `t4 : PkgI2.ReductionTorsionBijective.{0}` (l.1593).

## Plan (drafted, compile pending)
- `ZInQKernel/Contrib/AVB2/SerreLemma.lean` (Mathlib only): `eq_one_of_pow_eq_one` (ring form of Serre's lemma
  at 3), `eq_zero_of_smul_mem` (discreteness), `lattice_serre` (lattice form).
- `scratch/av-b2/olean/AVB2Main.lean` (imports TailI): `t9_of_leaves3`, `MulIsogenyPosChar` (new leaf),
  `divisiblePoints_of_posChar`, `cpt_torsion_descends`, `hom_ext_of_pts`, `serreRigidity3_of_T35`,
  bundles `OpenTextbookLeavesB2`/`OpenAddedLeavesB2`, `sixContactMin_of_openB2` (66 Props).

## Compile outcomes (VERIFIED)
- Olean chain (scratch/av-b2/chain.sh, 18:11-18:33): LPrefix 595 s, TailA 108, TailB 106, TailC 192, TailD 16,
  LF2* 6-12, TailE 59, TailF 46, TailG 69, TailH 75, TailI 5; all exit 0, 0 errors, no sorry.
- `lake build ZInQKernel.Contrib.AVB2.SerreLemma`: first run 2 errors (`Submodule.coe_smul` vs nsmul;
  induction without generalizing), fixed (`Submodule.coe_smul_of_tower`, `Nat.cast_smul_eq_nsmul`); then OK.
- `scratch/av-b2/ctail.sh AVB2Main.lean`: after 4 fix rounds (pullback type ascriptions, `simp` closing
  goals early in `sC`), exit 0, 0 errors, no sorry, 6 s. `#print axioms`:
  - `HDec.AVB2.t9_of_leaves3`: [propext, Classical.choice, Quot.sound]
  - `HDec.AVB2.divisiblePoints_of_posChar`: [propext, Classical.choice, Quot.sound]
  - `HDec.AVB2.serreRigidity3_of_T35`: [propext, Classical.choice, Quot.sound]
  - `HDec.HSyn.sixContactMin_of_openB2`: [propext, Classical.choice, Quot.sound]

## Findings
- t9 (T9, consequence form) is glue: `t9_of_leaves3 : T09_SymmIsogenyExists → IsogenyQuasiInverse →
  LeafPush.T09_WeilPairing.{0}` is weil-pairing's `oldT9_of_symmIsogeny`; Lean accepts it at the field's type, so
  `OldT9.T09_WeilPairing` and `LeafPush.T09_WeilPairing.{0}` are definitionally equal (VERIFIED).
- serreRigidity3 is glue from T35 and HomLatticeCorr (both bundle fields) plus the proved `MulIsogeny` (finiteness
  of `[3]` for the torsion descent `A(ℂ)[3] = A(ℚ̄)[3]`) and Mathlib (VERIFIED).
- divisiblePoints follows from the new leaf `AVB2.MulIsogenyPosChar` ([n] finite + surjective, n ≠ 0, positive
  characteristic); characteristic 0 is the proved `MulIsogeny` (VERIFIED).
- Net: 68 → 66 Props (`sixContactMin_of_openB2`); leaves 62 → 60 (t9, serreRigidity3 removed; divisiblePoints
  replaced by MulIsogenyPosChar).
- T11(b): `baseChange_map_injective` (uniqueness, any char, any L, k alg. closed) and
  `t11b_of_exists : T11bExists → T11b_Rigidity` compile (2 fix rounds: `Category.assoc` rewrites failed on
  Scheme compositions, replaced by term proofs). Fold: field `t11b` → `t11bExists`.
- Flat single-file check `AVB2Flat.lean` (111 230 lines, md5 71e9e3ab…): `lake env lean` exit 0 in 1037 s,
  0 errors, no sorry; 293 `#print axioms`, all `[propext, Classical.choice, Quot.sound]` (script count).
  A first flat run (before the T11b part) was killed by PID to rerun with the final text.
- `verbatim_check.sh`: flat prefix = Leaves3.lean byte for byte (110 826 lines); tail = AVB2Main body.
- Leaves confirmed, not reduced: t09SymmIsogenyExists, isogenyQuasiInverse, t10 (pro-étale H¹, no Mathlib
  theory), t4 (Serre–Tate reduction of prime-to-p torsion).

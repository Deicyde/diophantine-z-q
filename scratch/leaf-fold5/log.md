# leaf-fold5 results log

## 2026-11-13 23:30 start
- Base ee7582da (wip/integrate-w52). No earlier run (no log.md).
- Kernel not built in this worktree: `lake build` of the 51 kernel modules the chain and the new parts import
  (kernel_targets.txt) started 23:40.
- Chain plan: leaf-fold4's committed sources scratch/leaf-fold4/olean/{LPrefix,...,TailK}.lean compiled unchanged
  into scratch/leaf-fold5/olean (chain.sh), then TailL (vert-witness + model-glue port, mk_e10.py), TailM (av-b2,
  av-b1, curves-g, neron-c), TailN (bundles, sixContactMin_of_open5).
- mk_e10.py: vert-witness VertMain.lean.part + model-glue ModelGlue{,2..6}.lean.part, hdec edits; no declaration of
  them is already in the chain (0 dropped); `smoothFibreReduced'` now the kernel's `ZInQ.SmoothFibre.smoothFibreReduced`.

## 23:50 kernel built; chain started
- `lake build` of kernel_targets.txt: success (11003 jobs, 23:40-23:49). ZInQKernel.Contrib.AVB2.SerreLemma (av-b2's
  kernel file, imported by part e20) built separately.
- mk_e10.py edits for (c): `smoothFibreReduced'` := the kernel's `ZInQ.SmoothFibre.smoothFibreReduced`;
  `isReduced_of_etale_of_isDomain'` := the kernel's `ZInQ.SmoothFibre.isReduced_of_etale_of_isDomain` (model-glue had
  verbatim copies of both).
- Parts drafted: e20 (av-b2 AVB2Main, verbatim), e30 (t6/t7/t8/t34/t38/t3/t41 from the kernel's AVB1/CurvesG/NeronC
  theorems via toAbVarK4/ofAbVarK4), e90 (OpenTextbookLeaves5 21, OpenAddedLeaves5 21, OpenGlue5 2;
  sixContactMin_of_open5 through leaf-fold4's bundles).
- 23:50 `./chain.sh LPrefix` (LPrefix ... TailK from leaf-fold4's sources, then TailL, TailM, TailN).

## 00:10-00:14 chain, VERIFIED
- LPrefix 551 s, TailA 66, TailB 93, TailC 172, TailD 10, LF2* 6-8, LF3Cot 12, TailE 55, TailF 40, TailG 71, TailH 76,
  TailI 6, LF4T5 12, TailJ 30, TailK 13 s: leaf-fold4's sources, 0 errors each.
- TailL first run: 5 errors, all name resolution: model-glue uses the kernel's `curveFacts` and `smoothStalkDimOne`
  (over the kernel's `ToP1`), which `open LeafQM.AV.Pin` inside `namespace HDec` does not reach. Fixed in mk_e10.py:
  `HSyn.curveFacts5` := `curveFacts_of_leaves smoothStalkDimOne_proved constOrOntoAlgClosed_proved
  ratFactorAlgClosed_proved` (the chain's own curve facts, the term leaf-fold3's `mobiusGlue_of_t5'` uses; those
  three are the kernel's theorems through `toP1K`). TailL second run: 11 s, 0 errors.
- TailM first run: 3 errors. T38 and T34: the chain's `IsCurve` is a copy of the kernel's class (rebuilt field by
  field); T41: the chain's `NeronModelExists` is over `ZInQ.DefFaltings.AbVar` (h5-neron's copy), so the kernel's
  abelian variety is `⟨A.X⟩`. The AVB1 transports (T6, T7, T8) and T3 were accepted at once. Second run: 29 s, 0 errors.
- TailN: 5 s, 0 errors; all 15 `#print axioms` lines `[propext, Classical.choice, Quot.sound]`, including
  `HDec.HSyn.sixContactMin_of_open5`. Counts 26 + 21 + 21 + 2 = 70.

## 00:15-00:25 Check5 and (c), VERIFIED
- olean/Check5.lean (25 s): `example : ∀ r t l g, _root_.ZInQ.SixContactMin := HDec.HSyn.sixContactMin_of_open5`
  compiles; closure 184 142 constants; contains the kernel's SmoothFibre, AVB1, CurvesG, NeronC, AVB2.lattice_serre
  theorems, model-glue's and vert-witness's composites; not sorryAx, not av-b2's divisiblePoints/MulIsogenyPosChar;
  output (no host paths) in check5_result.txt, with the head constant of every field type.
- Probe (olean/Probe6.lean): none of the 23 chain field Props with a kernel namesake is definitionally equal to it at
  default transparency (all quantify over copied structures/classes).
- Part e40: the chain's Prop from the kernel's for T5, T4, R6, R7a, R7b (with `hasGoodReduction_iffK5`: the class
  IsAbelianScheme inside HasGoodReduction is a copy), R8, R9a (needs 8M heartbeats: about 80 s of defeq on galRep),
  R9b, T27, T35, T33. Bundles: OpenResearchLeaves5 (r6, r7a, r7b, r8, r9a, r9b over the kernel's Props) and
  OpenTextbookLeaves5 (t4, t5, t27, t33, t35 too). TailM 110 s, TailN 5 s, 0 errors, all 28 axiom lines standard.
- Not restated (their Props involve copied structures beyond AbVar: QML3/QMPair/QMStr (r1rec, r3, r5, r5count),
  Faltings heights over copied GroupModel (r19-r22, h5fin), modular-curve/Galois-rep structures (r16, r17, r18)).

## 00:27-00:47 flat file, VERIFIED
- Leaves5.lean (121728 lines, md5 35a709b10b2b…): `lake env lean` exit 0 in 1194 s, max RSS 16.4 GB, 0 errors, no sorry,
  343 `#print axioms` reports (joined over wrapped lines), all `[propext, Classical.choice, Quot.sound]`, including
  `HDec.HSyn.sixContactMin_of_open5`.
- Report docs/research/leaf-fold5.md written (00:30-00:45).

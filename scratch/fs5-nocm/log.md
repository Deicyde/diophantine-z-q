# fs5-nocm results log

- 05:22 base 2dd83306; merged origin/wip/qm-pin, origin/wip/mobius-glue (g0-fibresimple already in base).
- FS5 source: scratch/g0-fibresimple/FibreSimple.lean L20190-20206 (`HSyn.G0Split.FibreComTrivial`).
  Its names resolve to kernel copies: `R1fpProps`, `R2fpProps`, `QML3`, `M3`, `com`, `Qbar` (LeafQM.AV,
  ZInQKernel/HDecomp/QM/*), `contactSet` (ZInQ, Hypotheses/Height.lean), `Jmap` (ZInQ.JHeight).
- Repaired R1 text: scratch/qm-pin/QM-Leaves-full.patch L63-70 (R1fpProps := old 4 clauses ∧ R1famProps ∧ R1univProps).
- lake build ZInQKernel.HDecomp.QM.Leaves, Repo.PRArith, Hypotheses.JHeight: OK (VERIFIED).
- 05:50 FS5NoCM.lean §A (qm-pin copy) + §B statements + §C named Props + §D arithmetic
  (two_not_prime_of_sqrt_neg_one, finrank_adjoin_sqrt_neg_one, adjoin_pair_eq, elkies_sq): compiles, 0 errors (VERIFIED).
- 05:47 FS5NoCM.lean complete: `fibreComTrivialFull_of (hL : R1R2fpFull) (hM : MobiusGlue) (hA : ComIntOrQuadOrder)
  (hB : CMConductorCoprime6) (hK : X6KummerFibre) (hC : R5fpCount) : FibreComTrivialFull`, via
  `fibreComTrivialOwn_of` (FS5 on the leaf's own witnesses) and `fibreComTrivialFull_of_own` (qm-pin transfer).
  `lake env lean` exit 0, 7.6 s; all #print axioms [propext, Classical.choice, Quot.sound] (run1.txt). VERIFIED.
- FS5Curves.lean = mobius-glue/MobiusGlue.lean L1-1439 (+2 imports) + qm-pin `cm_objects_of_R1R2fp` + parts B, D, E, E2:
  `fibreComTrivialFull_of_curves` (MobiusGlue replaced by CurveRatFactor, CurveSurj, T5): exit 0, 11.8 s, standard axioms (run2.txt). VERIFIED.
- Verbatim checks (python string comparison, VERIFIED): FibreComTrivial = g0-fibresimple text; FibreComTrivialFull = it with
  R1fpProps→R1fpPropsFull; R1fpPropsFull body = patched R1fpProps of qm-pin QM-Leaves-full.patch; qm-pin block = QMPin.lean
  L34-95 + L507-619; kernel defs used (R1fpProps, R2fpProps, X6Props, R2X6Props, CMExists, X6Surj, R5ptProps, R5fpCount,
  com, residueImage, inertCount6, conductor, QML3, QMPair, ToP1, ...) identical to the copies in FibreSimple.lean.
- 05:46 §G (partG.lean): N1a split. Proved `com_int_of_end0_quat` (End⁰ ≅ B ⇒ com ⊆ ℤ, from T6 = PkgI3.HomFreeFinite),
  `B6_central_eq` (centre of ℍ[ℚ,2,-3] is ℚ), `tmul_one_injective`; named N1a-CM `ComOfMatrixEnd0`; proved
  `comIntOrQuadOrder_of (t27) (t6) (hCM) : ComIntOrQuadOrder` and `fibreComTrivialFull_of_leaves`.
  Tail.lean L40-116 (B6_isUnit … qm_embeds_end0) copied verbatim (VERIFIED by string inclusion).
  FS5NoCM.lean: exit 0, 11.4 s, 11 axioms lines standard (run1.txt). FS5Curves.lean: exit 0, 14.4 s,
  `fibreComTrivialFull_of_curves_leaves` standard (run2.txt). VERIFIED.

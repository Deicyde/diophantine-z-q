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
- 06:05 §H (partH.lean): N1a-CM `ComOfMatrixEnd0` PROVED from T6 (`comOfMatrixEnd0_of_homFree`):
  `commute_quat_scalar` (a matrix commuting with I, J, I²=2, J²=−3, JI=−IJ in M₂(K) is scalar; basis 1,I,J,IJ),
  `adjRoot_numberField` (ℚ[X]/(X²−d), d<0, is a totally complex quadratic number field), `root_lin_indep(_int)`,
  ψ : End_𝒪(A) → ℚ(√d) injective ring map, image integral (T6 finite) and of rank 2 in 𝒪_k (contains 1, s√d via FS4's
  localization step) ⇒ finite index (`Submodule.finiteQuotientOfFreeOfRankEq`).
  Hence N1a = `comIntOrQuadOrder_of_leaves (t27) (t6)`; final `fibreComTrivialFull_of_leaves'` and
  `fibreComTrivialFull_of_curves_leaves` need only: bundle, R5fpCount, T27, T6, N1b (+T5) and MobiusGlue (or
  CurveRatFactor, CurveSurj), N2.
  FS5NoCM.lean (1168 lines): exit 0, 54 s (load 24), 16 axioms lines standard (run1.txt).
  FS5Curves.lean (2456 lines): exit 0, 31 s, standard (run2.txt). VERIFIED.
- Note (Lean pitfall): with `letI : Fact (Irreducible f)` in context, AdjoinRoot's Field-derived and CommRing-derived
  instances do not unify at reducible transparency: `ring`/`linear_combination`/`rw [map_intCast]` fail; state helper
  lemmas without the Fact (root_lin_indep) and pass through `exact`/`rfl`.
- 06:10 Re-ran scratch/rv-nocm/nocm_check.py (~/pyenv/bin/python -I): output identical to rv-nocm's
  nocm_check.output.txt; Part B: the Kummer-model fibre field Q(√−t, √3(t−1)) agrees with González–Rotger Thm 5.12 on
  all 24 rational CM rows (VERIFIED, reproduced) — evidence for N2's constants.
- 06:17 §I (partI.lean): N1b `CMConductorCoprime6` PROVED from the new leaf N1b′ `CMOptimalEmbedding`
  (Shimura/Jordan/González–Rotger: End_𝒪(A) ≅ φ⁻¹(𝒪) for an embedding φ : k → B), `cmConductorCoprime6_of`:
  `check2`, `check3` (decide: Q(n) ≡ 0 mod p² ⇒ p | n, p = 2, 3; N5's 𝒪 is the integral elements of B_p),
  `nrd_ofInt`, `dvd_of_sq_dvd_Qf`, `not_dvd_conductor_of_optimal` (Cauchy in 𝒪_k/R, minpoly of φ(y) = minpoly of y
  has integer coefficients, nrd(φ(py)) ∈ p²ℤ ⇒ φ(y) ∈ 𝒪 ⇒ y ∈ R). Final: `fibreComTrivialFull_of_leaves''`,
  `fibreComTrivialFull_of_curves_leaves'`.
  FS5NoCM.lean (1390 lines): exit 0, 24 s, 20 axioms lines standard (run1.txt). FS5Curves.lean (2684 lines): exit 0,
  25 s, 3 axioms lines standard (run2.txt). VERIFIED.
- 06:25 Docstrings of ComIntOrQuadOrder, CMConductorCoprime6, ComOfMatrixEnd0 updated to "proved" (text only).
  Final compile: FS5NoCM.lean exit 0, 20/20 axioms lines standard, 0 errors; FS5Curves.lean exit 0, 3/3 standard,
  0 errors (run1.txt, run2.txt). Verbatim checks re-run on final files (VERIFIED).

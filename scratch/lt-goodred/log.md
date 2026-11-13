# lt-goodred results log

## 2026-11-13
- Setup: `lake build ZInQKernel.Hypotheses.JHeight ZInQKernel.Compiler.Precision.HeightConstant` (ok, 9066 jobs).
  `build_prefix.sh`: olean of lines 1-14993 of scratch/linked-tate/Leaves.lean (byte-identical copy of the pin-applied
  scratch/h-decomposition/Leaves.lean) + 4 closers (`end AV`, `end LeafQM`, `end`, `end LeafQMSec`). VERIFIED exit 0 in 202 s.
  `ctail.sh`: olean/Tail.lean = `import LGPrefix` + parts/*.lean. `assemble.sh`: flat file GoodRed.lean = same prefix + parts.
- Declarations kept from linked-tate (verbatim): Leaves.lean L1-14993 (PkgI1, PkgI2, PkgI3 incl. the leaves
  NeronOggShafarevich, HomFreeFinite, QMDichotomyYu, EndDivision; PkgI4; ObjBridge; LeafQM through `LeafQM.AV.Qbar`);
  parts/10_dim.lean L1-208, L227-233 (G0Dim, `pkgI3_dim_baseChange`) -> parts/05_dim.lean;
  parts/70_galois.lean `G0Galois.resQ`, `qEmbRing`, `resQ_spec`; parts/75_modfield.lean `G0ModField.IF`, `incAlg`,
  `numberField_of_fd`; parts/96_unramtate.lean `UnramTate.sK`, `specMap_comp_sK`, `ptMapIso`, `homEquiv_mul`, `bcPt`,
  `bcPt_galAct`, `trHom`, `trHom_left`, `trHom_symm_comp`, `trHom_comp_symm`, `trPt`, `trPt_galAct` -> parts/10_copies.lean;
  parts/98_g3tate.lean `GoodRedTorsion` -> parts/20_goodred.lean; parts/95_linked.lean §1 (`endBC`, `specMap_flat`,
  `specMap_surjective`, `endBC_injective`) and `QMEndRank` -> parts/30_qmendrank.lean.
  From scratch/neron-lg/NeronLG.lean (Mathlib only, namespace renamed `LTGoodRed.NLG`): `dvrAt` + instance,
  `ringOfIntegers_mem`, `toO`, `toO_coe`, `center'`, `dvrAt_center'`, `isDiscreteValuationRing_of_ne_top`.
- `LTGoodRed.goodRedTorsion : HSyn.LinkedTate.GoodRedTorsion` PROVED. Tail runs: 1 (open Pointwise; universe of
  `PkgI2.IsInertia` needs `Type`), 2 (`isUnit_of_mul_eq_one` unknown; `Field.absoluteGaloisGroup` is not coerced to
  a function: restated as `s' : Ω ≃ₐ[L'] Ω`), 3 (`rw [resQ_spec]` fails through `PkgI4.GQ`: used `have` + `rw at`),
  4 (bcPt implicit fields), 5 (timeout at whnf: `set_option maxHeartbeats 1000000 in` on this one theorem; the default
  200000 is not enough, VERIFIED by a run without it). Run 6: VERIFIED exit 0 in 50 s, 0 errors,
  `'LTGoodRed.goodRedTorsion' depends on axioms: [propext, Classical.choice, Quot.sound]`.
  Helper lemmas proved (Mathlib only): `mem_nonunits_comap`, `natCast_notMem_nonunits` (an integer prime to `p` is a
  unit of a valuation ring with `p` in its maximal ideal), `inv_mem_of_notMem_nonunits`, `of_mem_inertia` and
  `isInertia_of` (Mathlib's inertia subgroup <-> "preserves the ring, trivial mod the maximal ideal").
- parts/40_qmrank.lean: `LTGoodRed.QM.qmEndRank_of (hM1 : PkgI3.HomFreeFinite) (hT27 : PkgI3.QMDichotomyYu)
  (hS : QMSplitCaseRank) : HSyn.LinkedTate.QMEndRank` PROVED. Pieces proved: `ofInt_injective`, `ofIntHom` (𝒪 ≅ ℤ⁴),
  `four_le_finrank` (rank End ≥ 4 from an injective ring map 𝒪 → End, I3.M1), `finrank_le_baseChange` (endBC injective),
  `finrank_end0` (rank_ℤ End = dim_ℚ End⁰, `Module.finrank_baseChange`), `mod3_step`, `pow3_dvd`, `norm6_int`, `norm6_rat`
  (x₀²−2x₁²+3x₂²−6x₃² anisotropic over ℚ, 3-adic descent), `quatB6_isUnit` (B=(2,−3) division: T27's hypothesis),
  `oI'`, `oJ'` and their relations, `quatEmbed` (B →ₐ[ℚ] End⁰(A) from 𝒪 →+* End(A), `QuaternionAlgebra.Basis.liftHom`).
  New glue Prop `LTGoodRed.QM.QMSplitCaseRank` (T27's second case: End⁰(A_Ω) ≅ M₂(ℚ(√d)), with ι, dim 2 and EndDivision
  ⇒ rank End(A) ≤ 4). Tail runs: 1 (ℤ division in linear_combination; `re 2` simp lemmas; `mul_one` ambiguous with
  MonObj; Nonempty destructuring; explicit args of `finrank_eq_four`), 2: VERIFIED exit 0 in 64 s, 0 errors, standard
  axioms for goodRedTorsion, quatB6_isUnit, quatEmbed, four_le_finrank, qmEndRank_of.
- parts/50_split.lean: `LTGoodRed.QM.qmSplitCaseRank (hM1 : PkgI3.HomFreeFinite) : QMSplitCaseRank` PROVED, hence
  `LTGoodRed.QM.qmEndRank_of_leaves (hM1 : PkgI3.HomFreeFinite) (hT27 : PkgI3.QMDichotomyYu) : HSyn.LinkedTate.QMEndRank`.
  Pieces proved: `eq_zero_of_mul_self_eq_zero` (EndDivision + dim 2 ⇒ no nonzero square-zero endomorphism: the zero
  endomorphism `toUnit ≫ η` factors through Spec k; surjectivity would make A.X.left subsingleton, dim ≤ 0),
  `intCast_smul_one_tmul`, `exists_smul_eq_tmul` (n·x = 1 ⊗ m in ℚ ⊗ M), `one_tmul_injective` (M free ⇒ flat),
  `eight_le_finrank` (B ↪ R and dim R > 4 ⇒ dim R ≥ 8: (b, b') ↦ θb + θb'·s injective), and in `qmSplitCaseRank`:
  dim_ℚ M₂(ℚ(√d)) = 8 (`AdjoinRoot.powerBasis`, `Module.finrank_matrix`), End⁰(A) ↪ End⁰(A_Ω) (`IsLocalization.flat`,
  `Module.Flat.lTensor_preserves_injective_linearMap`), preimage of E₁₂.
  Tail runs: 1 (Nontrivial via finrank; `mul_assoc` ambiguous; Module.Finite of AdjoinRoot), 2 (one extra tactic),
  3: VERIFIED exit 0 in 43 s, 0 errors; standard axioms for eq_zero_of_mul_self_eq_zero, eight_le_finrank,
  qmSplitCaseRank, qmEndRank_of_leaves (and the earlier ones).
- Flat file `scratch/lt-goodred/GoodRed.lean` (16417 lines = Leaves.lean L1-14993 + closers + parts 05, 10, 20, 30, 40, 50),
  `lake env lean`: VERIFIED exit 0 in 160 s, 0 errors, no `sorry`, 9 axiom reports, all [propext, Classical.choice, Quot.sound]
  (goodRedTorsion, quatB6_isUnit, quatEmbed, four_le_finrank, qmEndRank_of, eq_zero_of_mul_self_eq_zero, eight_le_finrank,
  qmSplitCaseRank, qmEndRank_of_leaves).

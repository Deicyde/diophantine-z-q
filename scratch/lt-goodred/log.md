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

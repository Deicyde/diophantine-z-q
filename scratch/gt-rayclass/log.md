# gt-rayclass results log

## Step 0 (11-15 02:45): base c2ad4181; merged origin/wip/shimura-cft (already in) and origin/wip/rayclass-cft.

## Step 1 (03:20): contribution file assembled and compiled (VERIFIED)
- `scratch/gt-rayclass/mk.py` writes `ZInQKernel/Contrib/OneProof/RayClassShimura.lean` (145 KB, 3053 lines) from
  shimura-cft (Part A2, B, C2, D), rayclass-cft (RayProof1-5, RayGlueO/I/A/B), `s6_sq` (RayDefs; the chain's
  TailZ21 copy of x6-glue was trimmed of it), and the new `NewCNO.lean`, `NewFinal.lean`.
  Dropped as chain duplicates: R1UnivRigid core (TailZ16), `ShimuraFamilyAb` (TailZ17), RayDefs (TailZ21),
  t5-glue's `T5Glue.*` (ZInQKernel/Contrib/OneProof/RingClassLattice.lean), `exists_ringEquiv_extend`.
  Dropped as unneeded: c-to-printed `CToPrinted.Shimura`, `dcRel_one_iff`, rigidity variants, `RayClassCM` theorems.
- `lake env lean ZInQKernel/Contrib/OneProof/RayClassShimura.lean`: 0 errors, 0 warnings, 1 min 01 s, 14.8 GB.
- New theorems: `RayClassCFT.classNumberOneB_proof : ClassNumberOneB` (from the chain's
  `HDec.QMSplit.CNO.principal_of_lattice`, plus `exists_den`, `padic_div`, `exists_int_approx`, `exists_den_B`);
  `rayClassCMAb_of (hL : ShimuraMainThmIDeligneY3AbU) (hHL : HomLinearLift) : RayClassCMAb` (no rigidity);
  `rayClassCMAb_of_leaves hL (hUL : UniformizationLeafAll) (hG : GAGAMorphism)`; `shimuraFamilyAb_of_U hL`.
- Pitfall: `lean/.lake` missing in the fresh worktree ("unknown module prefix 'ZInQ'"): reflink-copied from
  ~/dzq-wt/gt-grcount (identical lean/ZInQ).
- Pitfall: `Algebra (𝓞 ℚ) (v.adicCompletion ℚ)`: Mathlib's lemmas use `instAlgebraAdicCompletion`; a bare
  `algebraMap` elaborates another instance (not defeq for `mul_mem`): `attribute [local instance 2000]
  instAlgebraAdicCompletion` (as in TailZ12).

## Step 2 (03:35): autofold spec and dry run (VERIFIED, no Lean)
- `scratch/gt-rayclass/autofold-spec.json`: discharges `rayClassCMAb` (by `rayClassCMAb_of_leaves
  {n}.shimuraMainThmIDeligneY3AbU {t}.uniformizationLeafAll {t}.gagaMorphism`) and `shimuraFamilyAb` (by
  `shimuraFamilyAb_of_U {n}.shimuraMainThmIDeligneY3AbU`); adds one leaf `shimuraMainThmIDeligneY3AbU`, kind
  `composite` (the shimura-cft review's rating of the underlying Deligne leaf; see report §3).
- `python3 scripts/one_proof/autofold.py scratch/gt-rayclass/autofold-spec.json --dry-run`:
  `strict count: 45/13 on 58 -> 45/12 on 57; strictest 44/14 -> 44/13` (no file changed).
  Generated module saved (line 1 stripped) as `scratch/gt-rayclass/FoldCheck.lean`.

## Step 3 (03:55): build, #discharges, fold check (VERIFIED)
- `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.RayClassShimura`:
  success, 12980 jobs, 8 min 19 s; frozenTarget standard axioms.
- `lake env lean scratch/gt-rayclass/Discharges.lean`: DISCHARGES rayClassCMAb by rayClassCMAb_of_leaves (still
  assumes ShimuraMainThmIDeligneY3AbU, UniformizationLeafAll, GAGAMorphism) and by rayClassCMAb_of; DISCHARGES
  shimuraFamilyAb by shimuraFamilyAb_of_U (still assumes ShimuraMainThmIDeligneY3AbU); all axioms standard;
  "#discharges: 65 open hypotheses, 1499 theorems checked, 7 discharge one" (3 of the 7 are earlier contributions).
- `lake env lean scratch/gt-rayclass/FoldCheck.lean`: sixContactMin_of_open27 standard axioms, 6 s.

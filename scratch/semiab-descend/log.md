# semiab-descend results log

Base: wip/height-fix 49e6d97d + origin/main (merge 530ef0e7) + origin/wip/leaf-fold32b (merge de506e7e).

## Target
`ZInQ.HeightFix.SemiAbelianDescendsPerfect` (ZInQKernel/Contrib/OneProof/PrintedStableHeight.lean:611).

## Consumers (VERIFIED, grep)
- only `isSemistableRes_of_geom` (PrintedStableHeight.lean:630) applies it, at `k = 𝔭.ResidueField` for a maximal
  ideal `𝔭` of `𝓞_L` (finite field, `perfectField_residueField`). Everything else takes it as a hypothesis
  (`isPrintedStableHeight_of`, `bostLowerBound_of_printed`, `gaudronRemondThm14_of_printed`, javanpeykar/pazuki).

## Plan (decomposition)
- LEAF `ChevalleyPerfect` (Chevalley's structure theorem over a perfect field, existence + uniqueness;
  Conrad 2002 Thm 1.1, UNVERIFIED locator), kernels as scheme-theoretic kernels (pullback along the unit).
- GLUE to prove: identity component over a field (open subgroup); open subgroups over k̄ closed (Jacobson);
  `U'_{k̄}` = base change of `G⁰`; kernel `ker π'` ≅ `Spec k̄[x₁^{±1},…,x_r^{±1}]` (Yoneda on affine points);
  `U'` smooth (shear iso + flat descent of smoothness, Mathlib `DescendsAlong @Smooth`); `G⁰` smooth (descent along
  `Spec k̄ → Spec k`); kernel of `π_{k̄}` smooth connected affine; uniqueness ⇒ kernels agree; transport.

## Findings / compile outcomes
- A.lean §1-§4 COMPILED (VERIFIED): isIso_of_bijective_affine (Yoneda on affine points over any S), exists_algPtMap, exists_iso_algPt, isSmoothConnAffineKer_of_torus (functor-of-points split torus kernel ≅ Spec K[x^±1], hence smooth/affine/connected).
- A.lean §5 COMPILED (VERIFIED): isPullback_shear, smooth_of_smoothKer (faithfully flat qc hom with smooth kernel onto smooth group => smooth source; Mathlib DescendsAlong @Smooth).
- A.lean §6 COMPILED (VERIFIED): isClosed_range_openSubgroup (open subgroup scheme of lft group over alg. closed field is closed; Jacobson + K-points + translations).
- A.lean §7 COMPILED (VERIFIED): identity component over a field: isOpen_idCompSet, isClosed_idCompSet, isSubgroupOpen_W0 (from 04KV, proved), connectedSpace_W0.
- A.lean §8-§9 COMPILED (VERIFIED, 11-16 ~16:40): semiAbelianDescendsPerfect_of_chevalley : ChevalleyPerfect → ZInQ.HeightFix.SemiAbelianDescendsPerfect; #print axioms = [propext, Classical.choice, Quot.sound]. Only new hypothesis: the leaf ChevalleyPerfect. Covers every perfect field (the full Prop).
- autofold dry run (combined spec autofold.json) on this base: 'strict count: 16/21 on 37 -> 19/19 on 38; strictest 16/21 -> 19/19' (-2 GLUE), exit 0 without --allow-rise. autofold-after-height-fix.json refused on this base (field semiAbelianDescendsPerfect exists only after the height-fix fold), as expected.
- Build `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.SemiAbelianDescendsPerfect` OK.
- #discharges (discharges.txt, VERIFIED): bostLowerBound, gaudronRemondThm14, javanpeykarBound, pazukiCor13Upper discharged by the *_of_printed_chevalley theorems; still assumes [printed leaf, UniformizationLeafAll, MumfordTorsionAlgClosed, ChevalleyPerfect]; standard axioms. "45 open hypotheses, 6883 theorems checked, 27 discharge one".
- Statements.lean: verbatim copies of SemiAbelianDescendsPerfect, HasSemiAbelianIdCompTorus, HasSemiAbelianIdentityComponent equal the originals by rfl (VERIFIED, compiles silently).
- Finding: on this base uniformizationLeafAll is no longer a textbook field (proved: `_root_.uniformizationLeafAll_proof`, Contrib/OneProof/UniformizationLeafAll.lean). height-fix's spec `{t}.uniformizationLeafAll` fails to compile here; autofold.json uses the proof instead and imports that module.
- Dry run (updated spec): exit 0 without --allow-rise, 16/21 on 37 -> 19/19 on 38 (strict and strictest): -2 GLUE. FoldDryRunCheck.lean (output minus line 1 + #print axioms) compiles; sixContactMin_of_open39 standard axioms (VERIFIED).

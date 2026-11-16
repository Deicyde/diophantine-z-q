# poincare-proof results log

Base: origin/main 0caafe66 (wip/poincare-proof). Field: `poincareComplement : ZInQ.Contrib.AVB1.PoincareComplement`
(OpenTextbookLeaves12, ZInQKernel/OneProof/H/TailZ42.lean; statement in ZInQKernel/Contrib/AVB1/Poincare.lean:42).

## Findings (VERIFIED by reading the tree)
- Consumer: only T8 (`PkgI3.PoincareReducibility`) via `AVGlue.poincareReducibility_of_published'` (TailX:218),
  used at step E1 in TailD (`t.t8 L.K ...`, L.K a number field). Full statement is needed only over number fields,
  but the plan below proves the full statement (any char-0 field).
- Inputs available as open fields of the current bundles (no new leaf):
  `{l}.picRepresentableAbVar`, `{l}.picZeroAbVar`, `{l}.phiAmpleIsogeny` (OpenAddedLeaves17, T09Pic in TailZ24),
  `{l}.milneIsogenyQuasiInverse` (AvSplit, TailQ:1207), `{t}.cartierSmooth` (AVGlue, TailP:305).
- Proved in the tree: `ZInQ.Contrib.AbVarBC.mulIsogeny` ([n] finite surjective, char 0), `AVGlue.imageFactorization_of_cartier`,
  `T09Pic.veryAmpleIsAmple`, `T09Pic.exists_isVeryAmple`, `T09Pic.mumfordBundle_restrict_zero`, `T09Pic.comp_classify`.

## Plan (proof of PoincareComplement)
B --i--> A closed immersion. L very ample on A, L' = i^*L very ample on B. psi : A -> B^ = Pic^0_B classifies (i x 1)^*Lambda(L)
on B x A; psi . i = lambda_{L'} (isogeny by L3). Milne quasi-inverse phi' with phi phi' = [d], phi' phi = [d].
f = [d] - i phi' psi : A -> A; C = image of f (Cartier), f = g . h. m = i + g : B x C -> A, m' = (phi' psi, h).
m' ; m = [d]_A (surjective), m ; m' = [d]_B x [d]_C (finite) so m finite (IsFinite.of_comp, m' separated).

## Compile log
- 13:05 PoincareComplement.lean §1-§2 (algebraic step) compiled except mul_one/one_mul ambiguity (fixed).
- 13:08 full file compiled (lake env lean), only linter warnings; copied to ZInQKernel/Contrib/OneProof/PoincareComplement.lean
- 13:08 `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.PoincareComplement`:
  success (13699 jobs; PoincareComplement built in 63 s). VERIFIED.
- 13:09 `#discharges` (scratch/poincare-proof/Discharges.lean; output discharges-output.txt): VERIFIED
  `DISCHARGES [OpenTextbookLeaves12.poincareComplement] by ZInQ.Contrib.OneProof.PoincareComplement.poincareComplement_of_open`
  still assumes [T09Pic.PicRepresentableAbVar, T09Pic.PicZeroAbVar, T09Pic.PhiAmpleIsogeny, AvSplit.MilneIsogenyQuasiInverse,
  AVGlue.CartierSmooth] (all five are fields of the current bundles); axioms [propext, Classical.choice, Quot.sound].
- 13:09 autofold --dry-run (autofold.json): strict 34/11 on 45 -> 33/11 on 44; strictest 34/11 -> 33/11. The generated
  module (FoldDryRun.lean, line 1 stripped) compiles; `sixContactMin_of_open36` standard axioms. VERIFIED.

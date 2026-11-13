# afr-absfrob results log

## Setup
- Merged origin/wip/alg-frob-red (b7acb2e6). Targets: `AlgFrobRedRed.AbsFrob` (part_red.lean L1368),
  `AlgFrobRedRed.FExtendGen` (part_red.lean L1299).

## Runs
1. AbsFrobDef.lean (powHom, natCast_sections, frobC, frobPSh, frob_stalkMap, fr, fr_base, fr_app):
   compiles, no errors (VERIFIED, `lake env lean`, ~80 s).
2. AbsFrobDef.lean + fr_naturality, natCast_Spec, natCast_of_hom, fr_Spec, verbatim copy of
   `AlgFrobRedRed.AbsFrob`, `frobenius_eq_powHom`, `absFrob : AbsFrob`: compiles;
   `#print axioms AlgFrobRedRed.absFrob` = [propext, Classical.choice, Quot.sound] (VERIFIED).
   Copy of the `AbsFrob` def+docstring is byte-identical to part_red.lean (VERIFIED, cmp, 12 lines).
3. part_fext.lean drafted (FExtendGen from I2-NMP); build.sh assembles AfrAbsFrob.lean =
   src_AlgFrobRed.lean (cmp-identical copy of scratch/alg-frob-red/AlgFrobRed.lean) + AbsFrobDef
   body (minus import and the duplicate `def AbsFrob`) + part_fext.lean.
   First run blocked: ZInQKernel.HDecomp.C10.Link olean missing -> `lake build ZInQKernel.HDecomp.C10.Link`.

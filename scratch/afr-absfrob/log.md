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
4. Built missing ZInQKernel oleans (`lake build` of AfrAbsFrob.lean's ZInQKernel imports; exit 0).
5. AfrAbsFrob.lean runs 1-3: rw-motive failures (hσ.1 through the `IsArithFrob` def; `G.left`
   codomain `ℬ.X.left` vs `pullback ..`; identities at `(𝟙_ _).left`) fixed by `generalize hσ.1 = hσ1`,
   a retyped `Gl`, `erw`.
6. AfrAbsFrob.lean run 4: exit 0, no errors; 91 axiom prints, all [propext, Classical.choice, Quot.sound];
   `AlgFrobRedRed.fExtendGen_of_nmp : PkgI2.NeronMappingAbelianScheme.{0} → FExtendGen` (VERIFIED).
7. Final AfrAbsFrob.lean (with algFrobRed_of_nmp, tateBridge35_of_nmp): exit 0, ~141 s, no errors,
   95 axiom prints, 0 non-standard; no `sorry` in part_fext.lean / AbsFrobDef.lean (VERIFIED).
   - absFrob, fExtendGen_of_nmp, fExtendCore_of_nmp, algFrobRed_of_nmp, tateBridge35_of_nmp,
     ringHom_eq_of_normal, hom_spec_eq_of_point: [propext, Classical.choice, Quot.sound].

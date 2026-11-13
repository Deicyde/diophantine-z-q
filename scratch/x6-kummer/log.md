# x6-kummer results log

- 06:37 start; base 322303a2. `lake build ZInQKernel.HDecomp.QM.Leaves` (2m17s), `...QM.Pin` OK.
- Statement copied verbatim from scratch/fs5-nocm/FS5NoCM.lean (lines 224-234, 250-265, 301-345):
  `R1fpPropsFull`, `R1R2fpFullProps`, `R1R2fpFull`, `CMConductorCoprime6`, `X6KummerFibre`.
  On this base the names `R1famProps`/`R1univProps` resolve to the kernel's (pin-apply integrated),
  so `R1fpPropsFull = LeafQM.AV.R1fpProps` (Iff.rfl, compiled). fs5-nocm's own copies of qm-pin's
  block clash with the kernel's (`Ambiguous term R1famProps`, VERIFIED by compile), so the kernel
  module `QM/Pin.lean` (phi_part, MobiusGlue, cm_objects_of_R1R2fp) is used instead.
- 06:48 X6Kummer.lean (part0 + partB) compiles, exit 0, no errors (VERIFIED):
  `intermediateField_eq_of_fix_iff`, `fix_adjoin_iff`, `spec_comp_eq_self_iff`,
  `galPt_eq_self_iff` (stabilizer of a Qbar-point = fixing group of its residue field),
  `galPt_mem_fibre`, `ne_neg_self'`, `fix_iff_of_sq_eq`,
  `x6KummerFibre_of_equiv : X6KummerEquiv → X6KummerFibre`.
- 06:50 partC (transport): `X6KummerModel` (leaf N2-L, existential), `PairBaseChangeUnique` (glue),
  `cm_objects_of_props`, `kummerFibreEquiv_transport`, `x6KummerEquiv_of_model`,
  `x6KummerFibre_of_model : MobiusGlue → PairBaseChangeUnique → X6KummerModel → X6KummerFibre`.
  Compiled first try, standard axioms (VERIFIED).
- 06:54 partR = scratch/mul-rigidity/Rigidity.lean lines 18-203 verbatim (rigidityHom); partD:
  `one_pt_left`, `pairBaseChangeUnique : PairBaseChangeUnique` (pullback uniqueness + rigidity),
  `x6KummerFibre_of_model' : MobiusGlue → X6KummerModel → X6KummerFibre`.
  `lake env lean scratch/x6-kummer/X6Kummer.lean`: exit 0, 0 errors, 33 s, load ~15; all 6
  `#print axioms` = [propext, Classical.choice, Quot.sound] (VERIFIED).
- 07:00 N1b.lean = part0 + partN (fs5-nocm partI verbatim minus its last theorem): exit 0, 9 s;
  `dvd_of_sq_dvd_Qf`, `not_dvd_conductor_of_optimal`, `cmConductorCoprime6_of :
  CMOptimalEmbedding → CMConductorCoprime6` re-verified on this base, standard axioms (VERIFIED).
- 07:08 partE (conic form): `ConicPt`, `conicGal`, `ConicModel`, `X6ConicModel` (leaf N2-L′),
  `conic_fibre_iff`, `kummerFibreEquiv_of_conic`, `x6KummerModel_of_conic`,
  `x6KummerFibre_of_conic : MobiusGlue → X6ConicModel → X6KummerFibre`.
  X6Kummer.lean (part0,B,C,R,D,E): exit 0, 0 errors, 33 s; 8 `#print axioms` lines, all
  [propext, Classical.choice, Quot.sound] (run1.txt) (VERIFIED).

# x6-kummer results log

- 06:37 start; base 322303a2. `lake build ZInQKernel.HDecomp.QM.Leaves` (2m17s), `...QM.Pin` OK.
- Statement copied verbatim from scratch/fs5-nocm/FS5NoCM.lean (lines 224-234, 250-265, 301-345):
  `R1fpPropsFull`, `R1R2fpFullProps`, `R1R2fpFull`, `CMConductorCoprime6`, `X6KummerFibre`.
  On this base the names `R1famProps`/`R1univProps` resolve to the kernel's (pin-apply integrated),
  so `R1fpPropsFull = LeafQM.AV.R1fpProps` (Iff.rfl, compiled). fs5-nocm's own copies of qm-pin's
  block clash with the kernel's (`Ambiguous term R1famProps`, VERIFIED by compile), so the kernel
  module `QM/Pin.lean` (phi_part, MobiusGlue, cm_objects_of_R1R2fp) is used instead.
- 07:40 X6Kummer.lean (part0 + partB) compiles, exit 0, no errors (VERIFIED):
  `intermediateField_eq_of_fix_iff`, `fix_adjoin_iff`, `spec_comp_eq_self_iff`,
  `galPt_eq_self_iff` (stabilizer of a Qbar-point = fixing group of its residue field),
  `galPt_mem_fibre`, `ne_neg_self'`, `fix_iff_of_sq_eq`,
  `x6KummerFibre_of_equiv : X6KummerEquiv → X6KummerFibre`.

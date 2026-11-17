import ZInQKernel.Contrib.OneProof.GrossZagierModuli.NonVacuous

/-! gz-moduli: axiom check of the main theorems. -/

#print axioms ZInQ.GZModuli.grossZagierFormulaCd_of_moduli
#print axioms ZInQ.GZModuli.grossZagierFormulaAt_of_moduli
#print axioms ZInQ.GZModuli.grossZagierFormula_of_moduli
#print axioms ZInQ.GZModuli.grossZagierModuliCd_of
#print axioms ZInQ.GZModuli.isHeegnerPointReps_of
#print axioms ZInQ.GZModuli.isModularParam_of
#print axioms ZInQ.GZModuli.modPt_eq
#print axioms ZInQ.GZModuli.exists_heegnerPointReps
#print axioms ZInQ.GZModuli.exists_modularParam_cd

/-- The discharge, with exactly the target's type. -/
example (h : ZInQ.GZModuli.GrossZagierModuliCd) : ZInQ.GZHL3.GrossZagierFormulaCd :=
  ZInQ.GZModuli.grossZagierFormulaCd_of_moduli h

/-! # twist-descent, part FINAL: consequences (kf-glue's reductions with `TwistDescent` discharged) -/

section TwistDescentFinal

namespace G0ModField.KernelField

/-- **`ConjIsogMaps` from `MulIsogeny` alone** (kf-glue's `conjIsogMaps_of_descent` with
`twistDescent`). -/
theorem conjIsogMaps_of_mulIsogeny (hMul : G0FibreSimple.MulIsogeny) : ConjIsogMaps :=
  conjIsogMaps_of_descent hMul twistDescent

/-- **`ConjIsogMaps` from mul-rigidity's leaf `KerUnitOpen` alone.** -/
theorem conjIsogMaps_of_kerUnitOpen' (hK : MulRigidity.KerUnitOpen) : ConjIsogMaps :=
  conjIsogMaps_of_kerUnitOpen hK twistDescent

/-- **`ConjIsogMaps` from mul-rigidity's two cotangent glue statements alone.** -/
theorem conjIsogMaps_of_cotangent' (h1 : MulRigidity.KerUnitOpenOfCotangentSurj)
    (h2 : MulRigidity.CotangentMulN) : ConjIsogMaps :=
  conjIsogMaps_of_cotangent h1 h2 twistDescent

/-- **`KernelFieldExists` without `TwistDescent`.** Leaves: T6, NOS, Raynaud, TorsionStructure,
T27, `KerUnitOpen`; glue: FS5 `FibreComTrivial`. -/
theorem kernelFieldExists_of_kerUnitOpen' (hHFF : PkgI3.HomFreeFinite)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (t27 : PkgI3.QMDichotomyYu)
    (h5 : G0FibreSimple.FibreComTrivial) (hK : MulRigidity.KerUnitOpen) :
    KernelFieldExists :=
  kernelFieldExists_of_kerUnitOpen hHFF hNOS hRay hTors t27 h5 hK twistDescent

/-- **`KernelFieldExists` without `TwistDescent`**, with `MulIsogeny`. -/
theorem kernelFieldExists_of_mulIsogeny (hHFF : PkgI3.HomFreeFinite)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (t27 : PkgI3.QMDichotomyYu)
    (h5 : G0FibreSimple.FibreComTrivial) (hMul : G0FibreSimple.MulIsogeny) :
    KernelFieldExists :=
  kernelFieldExists_of_descent hHFF hNOS hRay hTors t27 h5 hMul twistDescent

end G0ModField.KernelField

end TwistDescentFinal

#print axioms TwistDescentGD.exists_open_gal
#print axioms TwistDescentGD.descend
#print axioms TwistDescentXC.xc_mul
#print axioms TwistDescentXC.xc_one
#print axioms TwistDescentHFD.hfd
#print axioms G0ModField.KernelField.td_hom_inv
#print axioms G0ModField.KernelField.td_construct
#print axioms G0ModField.KernelField.twistDescent
#print axioms G0ModField.KernelField.conjIsogMaps_of_mulIsogeny
#print axioms G0ModField.KernelField.conjIsogMaps_of_kerUnitOpen'
#print axioms G0ModField.KernelField.conjIsogMaps_of_cotangent'
#print axioms G0ModField.KernelField.kernelFieldExists_of_kerUnitOpen'
#print axioms G0ModField.KernelField.kernelFieldExists_of_mulIsogeny

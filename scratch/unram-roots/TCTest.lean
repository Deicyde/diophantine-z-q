import ZInQKernel.HDecomp.Conductor.LadicCond
import ZInQKernel.Contrib.TauCeti.NumberTheory.LocalField.Unramified.Maximal
import ZInQKernel.Contrib.TauCeti.NumberTheory.LocalField.Unramified.Existence
import ZInQKernel.Contrib.TauCeti.NumberTheory.LocalField.FiniteExtension.IntermediateField
import ZInQKernel.Contrib.TauCeti.NumberTheory.LocalField.InertiaDegree
import ZInQKernel.Contrib.TauCeti.NumberTheory.LocalField.Padic

noncomputable section

namespace UnramRootsTask

open PkgI4 (GQp)
open LadicCond Polynomial TauCeti IntermediateField

variable {p : ℕ} [Fact p.Prime]

example (F : Fld p) [FiniteDimensional ℚ_[p] F] : True := by
  letI := finiteIntermediateFieldValuativeRel ℚ_[p] (Kbar p) F
  letI := finiteIntermediateFieldTopology ℚ_[p] (Kbar p) F
  haveI := finiteIntermediateField_isNonarchimedeanLocalField ℚ_[p] (Kbar p) F
  haveI := finiteIntermediateField_valuativeExtension ℚ_[p] (Kbar p) F
  have h1 : Module.finrank F (unramifiedExtension F (Kbar p) 3) = 3 :=
    finrank_unramifiedExtension (by norm_num)
  have h2 : Nat.card 𝓀[F] = Nat.card 𝓀[ℚ_[p]] ^ inertiaDegree ℚ_[p] F :=
    TauCeti.natCard_residueField
  have h3 := Padic.natCard_residueField p
  trivial

end UnramRootsTask

import ZInQKernel.Contrib.OneProof.RC.CMField2.Lattices
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.ClassFields.RingClass.Field

/-! The arithmetic membership statement, independent of the normalization. -/

noncomputable section

open NumberField TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields

namespace ZInQ.Manuscript.RC.CMField2

/-- Simultaneous membership of the singular moduli in the ring class field, in one
complex embedding extending the specified embedding of the quadratic field. -/
def SingularModulusMemRingClass : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (O : NumberFieldOrder K)
    (hk : Module.finrank ℚ K = 2) (hc : IsTotallyComplex K) (κ : K →+* ℂ),
    ∃ ι : ringClassField O →+* ℂ, ι.comp (algebraMap K (ringClassField O)) = κ ∧
      ∀ I : O.invertibleProperFractionalIdeals,
        singularModulus O hk hc κ I ∈ Set.range ι


end ZInQ.Manuscript.RC.CMField2

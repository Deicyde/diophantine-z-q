import ZInQKernel.Contrib.OneProof.EllAdic.PadicProEtSubShiftEpiV2
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace RC53.EllAdic

universe u

/-- The short complex formed with the original lifted p-adic coefficient
sheaf, actual residue reductions, and the difference on the same product. -/
noncomputable def padicCoefficientProductSequence (S : Scheme.{u}) (p : ℕ) [Fact p.Prime] :
    ShortComplex (Sheaf (Scheme.ProEt.topology S) Ab.{u+1}) :=
  ShortComplex.mk (padicCoefficientToResidueProduct S p) (finiteResidueProEtSubShift S p)
    (padicCoefficientToResidueProduct_comp_subShift S p)

/-- Exactness here follows from the actual compatible limit and the
objectwise surjectivity of the difference, before taking any cohomology. -/
theorem padicCoefficientProductSequence_shortExact (S : Scheme.{u}) (p : ℕ) [Fact p.Prime] :
    (padicCoefficientProductSequence S p).ShortExact := by
  let seq := padicCoefficientProductSequence S p
  have hk : Nonempty (IsLimit (KernelFork.ofι seq.f seq.zero)) :=
    ⟨padicCoefficientIsKernelOfSubShift S p⟩
  obtain ⟨he, hm⟩ := (seq.exact_and_mono_f_iff_f_is_kernel).2 hk
  exact ShortComplex.ShortExact.mk' he hm (finiteResidueProEtSubShift_epi S p)

end RC53.EllAdic

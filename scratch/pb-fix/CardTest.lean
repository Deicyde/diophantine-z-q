import ZInQKernel.Contrib.OneProof.PanBerger
open Cardinal
variable (p : ℕ) [Fact p.Prime]
example : #(PadicAlgCl p) ≤ max #ℚ_[p] ℵ₀ := by
  have : FaithfulSMul ℚ_[p] (PadicAlgCl p) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap ℚ_[p] (PadicAlgCl p)).injective
  have : Module.IsTorsionFree ℚ_[p] (PadicAlgCl p) :=
    Module.IsTorsionFree.trans_faithfulSMul ℚ_[p] (PadicAlgCl p) (PadicAlgCl p)
  exact Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[p] (PadicAlgCl p)
noncomputable example : HDec.PkgI4.Qbar →ₐ[ℚ] ℂ := IsAlgClosed.lift

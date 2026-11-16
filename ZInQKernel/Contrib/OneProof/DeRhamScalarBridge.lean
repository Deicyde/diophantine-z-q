import ZInQKernel.Contrib.CloudB3SC3DeRhamScalars.Basic

/-!
# Scalar structure of the existing de Rham spaces

These are supporting results for an arbitrary finite extension `F/ℚ_p`.
They prove fixed scalars and dimension divisibility, not the abelian-variety
comparison equality. Neither `hodgeTateDecompAbVar` nor `deRhamH1AbVarT` is
claimed discharged by this file.
-/

namespace ZInQ.Contrib.OneProof.DeRhamScalarBridge

open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4
open ZInQ.Contrib.HodgeSplit

variable (p : ℕ) [Fact p.Prime]
variable (F : Type*) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]

/-- Every finite `F/ℚ_p` has a scalar embedding into the existing `BdR`, fixed
by the exact `G_F` action used by the comparison contract. -/
theorem fixedScalarEmbedding :
    ∃ ι : F →ₐ[ℚ_[p]] BdR p,
      ∀ (σ : Field.absoluteGaloisGroup F) (x : F),
        bdrAct p (gfToGqp p F σ) (ι x) = ι x :=
  ⟨PadicDeRhamScalars.scalarEmbeddingOver p F,
    PadicDeRhamScalars.scalarEmbeddingOver_fixed p F⟩

variable {F}
variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]

/-- Scalar divisibility in the original Hom form. -/
theorem homDimensionDivisible
    (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V) :
    Module.finrank ℚ_[p] F ∣ Module.finrank ℚ_[p] (ddrSpaceOver p ρ) :=
  PadicDeRhamScalars.finrank_dvd_ddrSpaceOver p ρ

/-- Scalar divisibility in the original tensor-dual form. -/
theorem dualTensorDimensionDivisible [FiniteDimensional ℚ_[p] V]
    (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V) :
    Module.finrank ℚ_[p] F ∣ Module.finrank ℚ_[p] (ddrTensorOver p ρ.dual) :=
  PadicDeRhamScalars.finrank_dvd_ddrTensorOver_dual p ρ

end ZInQ.Contrib.OneProof.DeRhamScalarBridge

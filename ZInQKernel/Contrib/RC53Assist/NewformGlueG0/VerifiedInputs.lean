import ZInQKernel.Contrib.RC53Assist.NewformArithmetic.CoefficientField
import ZInQKernel.Contrib.RC53Assist.NewformArithmetic.MultiplicityOne
import ZInQKernel.Contrib.RC53Assist.NewformGlueG0.GaloisCompletion

/-!
# Vendored newform proofs in the existing G0 input types

The Shimura input retains precisely existence of an analytic normalized full
Hecke eigenform for each embedding. The number-field clause and Li's two
results are supplied by the verified arithmetic modules.
-/

namespace ZInQ.Contrib.RC53Assist.NewformGlueG0

/-- Li's bad-prime input, discharged on the original newforms. -/
theorem li1975BadPrimeWeightTwo_proved : Li1975BadPrimeWeightTwo :=
  NewformArithmetic.bad_prime_weight_two

/-- Li's strong multiplicity-one input, discharged on the original newforms. -/
theorem li1975StrongMultiplicityOneWeightTwo_proved : Li1975StrongMultiplicityOneWeightTwo :=
  NewformArithmetic.multiplicity_one_weight_two

end ZInQ.Contrib.RC53Assist.NewformGlueG0

namespace ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent

open UpperHalfPlane CongruenceSubgroup HeckeRing.GL2
open ZInQ.Contrib.RC53Assist.NewformPeriods (IsNormalizedFullEigenformGamma0)

/-- The unresolved clause of `Shimura1973ConjugateEigenforms`: for every
coefficient-field embedding, its image coefficients are realized by a
normalized full eigenform at the same level. The new proof supplies finite
dimensionality separately and does not replace this existence clause. -/
def Shimura1973EmbeddedEigenforms : Prop :=
  ∀ (M : ℕ) [NeZero M] (F : Newform M 2), F.χ = 1 →
    ∀ σ : coefficientField F →ₐ[ℚ] ℂ,
      ∃ g : CuspForm (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) 2,
        IsNormalizedFullEigenformGamma0 M g ∧
        ∀ n : ℕ, (qExpansion 1 g).coeff n = σ ⟨(qExpansion 1 F.toCuspForm).coeff n,
          coeff_mem F n⟩

/-- The finite-dimensionality clause uses the same coefficient field. -/
theorem Shimura1973ConjugateEigenforms.of_embedded (h : Shimura1973EmbeddedEigenforms) :
    Shimura1973ConjugateEigenforms := by
  intro M _ F hχ
  exact ⟨NewformArithmetic.finiteDimensional_adjoin_all_coeffs F, h M F hχ⟩

/-- The older package also supplies the unresolved clause. -/
theorem Shimura1973ConjugateEigenforms.embedded (h : Shimura1973ConjugateEigenforms) :
    Shimura1973EmbeddedEigenforms := by
  intro M _ F hχ
  exact (h M F hχ).2

end ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent

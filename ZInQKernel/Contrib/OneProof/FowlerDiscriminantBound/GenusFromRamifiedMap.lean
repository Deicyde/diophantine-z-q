import ZInQKernel.Contrib.OneProof.FowlerDiscriminantBound.GenusUnitSquareClasses
import ZInQKernel.Contrib.OneProof.FowlerDiscriminantBound.RamifiedGenusMap

/-! The integral generators give the square-class relations of the same quadratic field. -/

namespace HDec.CMBranch.FowlerArithmetic

open NumberField IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K] [IsTotallyComplex K]

/-- The genus divisibility from ramified ideal products representing each rational prime
factor of the actual field discriminant. -/
theorem genus_dvd_of_ramified_genus_map (hk : Module.finrank ℚ K = 2)
    (P : ↥(NumberField.discr K).natAbs.primeFactors → HeightOneSpectrum (𝓞 K))
    (hP : ∀ i, (P i).asIdeal ^ 2 = Ideal.span {(i.val : 𝓞 K)})
    (hinj : Function.Injective (genusInteger (Subtype.val :
      ↥(NumberField.discr K).natAbs.primeFactors → ℕ)))
    (hsq : ∀ a, Squarefree (genusInteger (Subtype.val :
      ↥(NumberField.discr K).natAbs.primeFactors → ℕ) a)) :
    2 ^ ((NumberField.discr K).natAbs.primeFactors.card - 1) ∣ classNumber K := by
  classical
  apply classNumber_genus_dvd_of_principal_unit_squares hk (genusClassMap P Subtype.val hP)
    (fun a => genusInteger Subtype.val a.1.toAdd)
  · intro a b hab
    exact Subtype.ext (hinj hab)
  · exact fun a => hsq a.1.toAdd
  · intro a
    obtain ⟨α, u, _, h⟩ := genusClassMap_ker_generator P Subtype.val hP a
    exact ⟨(α : K), u, by exact_mod_cast h⟩

end HDec.CMBranch.FowlerArithmetic

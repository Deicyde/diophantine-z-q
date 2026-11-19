import ZInQKernel.Contrib.OneProof.RC.WitnessSpec.Inert
import ZInQKernel.Contrib.OneProof.RC.WitnessSpec.Restriction

/-! Conductor-one residue descent at the selected place, using the same
restriction of the prime on both number fields. -/

noncomputable section

open NumberField IsDedekindDomain TauCeti TauCeti.ClassFieldTheory
open ZInQ.Contrib.ChebFD.C10 (Zbar Qbar GQ)
open ZInQ.Contrib.CloudB3RC53.CST
open scoped NumberField

namespace ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace

variable {g : GQ} {p : ℕ} (v : FrobeniusPlace g p)

section Tower

variable {K H : Type} [Field K] [NumberField K] [Field H] [NumberField H]
  [Algebra K H] [IsScalarTower ℚ K H] (e : H →ₐ[ℚ] Qbar)

/-- Contracting the same prime through a tower gives primes lying over one another. -/
theorem restrictPrime_liesOver :
    (v.restrictPrime e).LiesOver (v.restrictPrime (e.comp (IsScalarTower.toAlgHom ℚ K H))) := by
  constructor
  unfold restrictPrime
  rw [Ideal.under_def, Ideal.comap_comap]
  congr 1


end Tower

variable [Fact p.Prime] {K : Type} [Field K] [NumberField K]
  (e : ringClassField (conductorOrder K 1) →ₐ[ℚ] Qbar)

/-- The residue field of the datum at the selected prime has order p² when
the quadratic discriminant has negative Legendre sign. -/
theorem ringClassResidue_card (hK : Module.finrank ℚ K = 2)
    (hD : ¬ (p : ℤ) ∣ discr K) (hsign : legendreSym p (discr K) = -1) :
    Nat.card ((𝓞 (ringClassField (conductorOrder K 1))) ⧸ v.restrictPrime e) = p ^ 2 := by
  let e₀ := e.comp (IsScalarTower.toAlgHom ℚ K (ringClassField (conductorOrder K 1)))
  let u := v.restrictHeightOne e₀
  let U := v.restrictHeightOne e
  let : U.asIdeal.LiesOver u.asIdeal := v.restrictPrime_liesOver e
  obtain ⟨hu, hd⟩ := inertPrime_of_legendre hK u (v.rationalPrimeBelow_restrict e₀) hD hsign
  exact conductorOne_residue_card u hu (v.rationalPrimeBelow_restrict e₀) hd U


end ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace

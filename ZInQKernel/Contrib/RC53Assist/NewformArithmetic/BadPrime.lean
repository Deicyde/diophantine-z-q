import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Newforms.BadPrime.AtkinLehner
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Newforms.BadPrime.Vanishing

namespace ZInQ.Contrib.RC53Assist.NewformArithmetic

open UpperHalfPlane HeckeRing.GL2

/-- Li's two bad-prime cases, on the normalized weight-two newform with trivial
nebentypus. The two cases use the vendored Atkin–Lehner square and vanishing
results respectively. -/
theorem bad_prime_weight_two (M : ℕ) [NeZero M] (F : Newform M 2) (hχ : F.χ = 1)
    (p : ℕ) (hp : p.Prime) (hpM : p ∣ M) :
    (p ^ 2 ∣ M → (qExpansion 1 F.toCuspForm).coeff p = 0) ∧
    (¬p ^ 2 ∣ M → (qExpansion 1 F.toCuspForm).coeff p ^ 2 = 1) := by
  constructor
  · intro hsq
    apply F.qExpansion_coeff_prime_eq_zero_of_sq_dvd hp hsq
    have htriv : F.dirichletLift = 1 := by
      apply MulChar.ext
      intro u
      rw [F.dirichletLift_def, MulChar.ofUnitHom_coe, hχ]
      simp
    rw [htriv]
    exact ⟨Nat.div_dvd_of_dvd hpM, 1, (DirichletCharacter.changeLevel_one _).symm⟩
  · intro hs
    have h : TauCeti.Nat.IsExactDivisor p M := .of_not_sq_dvd hp hpM hs
    have hcomp : F.χ = (1 : (ZMod (M / p))ˣ →* ℂˣ).comp
        (ZMod.unitsMap (Nat.div_dvd_of_dvd h.dvd)) := by
      rw [hχ, MonoidHom.one_comp]
    simpa using F.qExpansion_coeff_prime_sq_of_isExactDivisor hp h hcomp

end ZInQ.Contrib.RC53Assist.NewformArithmetic

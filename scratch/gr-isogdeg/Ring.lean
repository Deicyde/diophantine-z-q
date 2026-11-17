import Mathlib

namespace ZInQ.GRIsogDeg

open TensorProduct

/-- Ring-level count: `S` finite over the domain `R`, `ψ₀ : R → Ω` injective into a field.
The ring maps `S → Ω` over `ψ₀` are finitely many, at most the rank of `S` at the zero prime. -/
theorem card_ringHom_le_rankAtStalk {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsDomain R] [Module.Finite R S] {Ω : Type*} [Field Ω]
    (ψ₀ : R →+* Ω) (hψ₀ : Function.Injective ψ₀) (p : PrimeSpectrum R) (hp : p.asIdeal = ⊥) :
    Finite {ψ : S →+* Ω // ψ.comp (algebraMap R S) = ψ₀} ∧
    Nat.card {ψ : S →+* Ω // ψ.comp (algebraMap R S) = ψ₀} ≤ Module.rankAtStalk S p := by
  obtain ⟨P, hP⟩ := p
  dsimp only at hp
  subst hp
  let Rp := Localization.AtPrime (⊥ : Ideal R)
  have : IsFractionRing R Rp := by
    simpa [Ideal.primeCompl_bot] using Localization.isLocalization (M := (⊥ : Ideal R).primeCompl)
  letI : Algebra R Ω := ψ₀.toAlgebra
  have hunit : ∀ y : (⊥ : Ideal R).primeCompl, IsUnit (ψ₀ y) := fun y => by
    have hy : (y : R) ≠ 0 := fun h => y.2 (by rw [h]; exact Ideal.zero_mem _)
    exact ((map_ne_zero_iff ψ₀ hψ₀).mpr hy).isUnit
  let ψp : Rp →+* Ω := IsLocalization.lift hunit
  letI : Algebra Rp Ω := ψp.toAlgebra
  haveI : IsScalarTower R Rp Ω := IsScalarTower.of_algebraMap_eq fun r => by
    change ψ₀ r = ψp (algebraMap R Rp r)
    exact (IsLocalization.lift_eq hunit r).symm
  haveI : Module.Free Rp (Rp ⊗[R] S) := by
    let _ : Field Rp := IsFractionRing.toField R
    exact Module.Free.of_divisionRing _ _
  let toA : {ψ : S →+* Ω // ψ.comp (algebraMap R S) = ψ₀} → (S →ₐ[R] Ω) := fun ψ =>
    AlgHom.mk ψ.1 (fun r => congrArg (fun g : R →+* Ω => g r) ψ.2)
  let e₁ : {ψ : S →+* Ω // ψ.comp (algebraMap R S) = ψ₀} ≃ (S →ₐ[R] Ω) :=
    { toFun := toA
      invFun := fun f => ⟨f.toRingHom, RingHom.ext fun r => f.commutes r⟩
      left_inv := fun ψ => rfl
      right_inv := fun f => rfl }
  let e := e₁.trans (AlgHom.liftEquiv R Rp S Ω)
  have hfin : Finite (Rp ⊗[R] S →ₐ[Rp] Ω) := inferInstance
  refine ⟨Finite.of_equiv _ e.symm, ?_⟩
  rw [Nat.card_congr e, Module.rankAtStalk_eq_finrank_tensorProduct]
  exact card_algHom_le_finrank Rp (Rp ⊗[R] S) Ω

end ZInQ.GRIsogDeg

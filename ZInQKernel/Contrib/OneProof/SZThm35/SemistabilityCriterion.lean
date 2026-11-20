import ZInQKernel.Contrib.OneProof.SZThm35.RationalTorsionInertia
import ZInQKernel.OneProof.H.TailZ7

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open ReductSplit ReductGlue
open HDec.CMSerreTate (galAct_one_apply)
open ZInQ.Contrib.AbVarBC

namespace SZRaynaud

section Torsion

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (A : PkgI3.AbVar K)

/-- A point in the image of the ground field is fixed by every geometric
automorphism over that field. -/
theorem galAct_extPt_of_base (σ : Ω ≃ₐ[K] Ω) (y : A.Pt K) :
    A.galAct σ (extPt A (Algebra.ofId K Ω) y) = extPt A (Algebra.ofId K Ω) y := by
  have he : ∀ x : K, (Algebra.ofId K Ω) ((1 : K ≃ₐ[K] K) x) =
      σ ((Algebra.ofId K Ω) x) := fun x => (σ.commutes x).symm
  rw [← extPt_galAct A (Algebra.ofId K Ω) 1 σ he y, galAct_one_apply]

/-- A prime-power divisor of a rational invertible torsion level supplies the
prime and the rational two-factor inertia condition. -/
theorem exists_levelTwo_of_rational_torsion_of_finite_index
    (O : ValuationSubring K) (w : ValuationSubring Ω)
    (E : IntermediateField K Ω) [FiniteDimensional K E]
    (m : ℕ) (hm : 3 ≤ m) (hu : IsUnit (m : O))
    (hrat : ∀ x : A.Pt Ω, x ^ m = 1 →
      ∃ y : A.Pt K, extPt A (Algebra.ofId K Ω) y = x)
    (hE : ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : O) →
      ∀ (σ : Ω ≃ₐ[E] Ω), PkgI2.IsInertia w σ →
      ∀ (τ : Ω ≃ₐ[E] Ω), PkgI2.IsInertia w τ →
      ∀ x : VΩ (A.baseChange E) Ω ℓ,
        galVΩ (A.baseChange E) ℓ τ (galVΩ (A.baseChange E) ℓ σ x - x) =
          galVΩ (A.baseChange E) ℓ σ x - x) :
    ∃ (ℓ : ℕ) (_ : Fact ℓ.Prime), IsUnit (ℓ : O) ∧
      ∀ (σ : Ω ≃ₐ[K] Ω), PkgI2.IsInertia w σ →
      ∀ (τ : Ω ≃ₐ[K] Ω), PkgI2.IsInertia w τ →
      ∀ x : VΩ A Ω ℓ, galVΩ A ℓ τ (galVΩ A ℓ σ x - x) = galVΩ A ℓ σ x - x := by
  obtain ⟨ℓ, k, hp, hk, hd⟩ := exists_prime_pow_dvd_of_three_le hm
  let : Fact ℓ.Prime := ⟨hp⟩
  have hk₀ : k ≠ 0 := by
    intro h
    rw [h, pow_zero] at hk
    omega
  have hℓm : ℓ ∣ m := (dvd_pow_self _ hk₀).trans hd
  have hℓO : IsUnit (ℓ : O) := isUnit_of_dvd_unit (Nat.cast_dvd_cast hℓm) hu
  refine ⟨ℓ, ‹Fact ℓ.Prime›, hℓO, ?_⟩
  apply levelTwo_of_fixed_primePower_torsion_of_finite_index A w E ℓ k hk _ (hE ℓ hℓO)
  intro σ _ x hx
  have hxm : x ^ m = 1 := by
    obtain ⟨r, hr⟩ := hd
    rw [hr, pow_mul, hx, one_pow]
  obtain ⟨y, rfl⟩ := hrat x hxm
  exact galAct_extPt_of_base A σ y

end Torsion

section Criterion

variable {K : Type} [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
  (w : ValuationSubring (AlgebraicClosure K)) (A : PkgI3.AbVar K)

set_option maxHeartbeats 1000000 in

/-- Theorem 3.3 and potential semistability give Raynaud's criterion for the
existence of a semistable model over the original DVR. -/
theorem hasSemistableReductionSZ_of_sz33_of_rational_torsion
    (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O)
    (hSZ : SilverbergZarhinThm33)
    (hPotential : HasSemistableReductionSZ A O ∨
      ∃ E : IntermediateField K (AlgebraicClosure K), FiniteDimensional K E ∧ Algebra.IsSeparable K E ∧
        IsDiscreteValuationRing (w.comap (algebraMap E (AlgebraicClosure K))) ∧
        HasSemistableReductionSZ (A.baseChange E) (w.comap (algebraMap E (AlgebraicClosure K))))
    (m : ℕ) (hm : 3 ≤ m) (hu : IsUnit (m : O))
    (hrat : ∀ x : A.Pt (AlgebraicClosure K), x ^ m = 1 →
      ∃ y : A.Pt K, extPt A (Algebra.ofId K (AlgebraicClosure K)) y = x) :
    HasSemistableReductionSZ A O := by
  rcases hPotential with h | ⟨E, hfin, hsep, hdvr, hs⟩
  · exact h
  let := hfin
  let := hdvr
  let : IsAlgClosure E (AlgebraicClosure K) :=
    ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := K) (L := E) (A := AlgebraicClosure K)⟩
  have hE (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : O)) :
      ∀ (σ : AlgebraicClosure K ≃ₐ[E] AlgebraicClosure K), PkgI2.IsInertia w σ →
      ∀ (τ : AlgebraicClosure K ≃ₐ[E] AlgebraicClosure K), PkgI2.IsInertia w τ →
      ∀ x : VΩ (A.baseChange E) (AlgebraicClosure K) ℓ,
        galVΩ (A.baseChange E) ℓ τ (galVΩ (A.baseChange E) ℓ σ x - x) =
          galVΩ (A.baseChange E) ℓ σ x - x := by
    have hℓE : IsUnit (ℓ : w.comap (algebraMap E (AlgebraicClosure K))) := by
      simpa only [map_natCast] using hℓ.map (toO' O w hw E)
    exact (hSZ E _ _ w rfl _ ℓ hℓE (Or.inl hs)).mp hs
  obtain ⟨ℓ, hℓ, hℓO, htwo⟩ :=
    exists_levelTwo_of_rational_torsion_of_finite_index A O w E m hm hu hrat hE
  let := hℓ
  exact (hSZ K O _ w hw A ℓ hℓO (Or.inr ⟨E, hfin, hsep, hdvr, hs⟩)).mpr htwo

end Criterion

end SZRaynaud

#print axioms SZRaynaud.exists_levelTwo_of_rational_torsion_of_finite_index
#print axioms SZRaynaud.hasSemistableReductionSZ_of_sz33_of_rational_torsion

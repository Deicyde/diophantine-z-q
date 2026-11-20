import ZInQKernel.Contrib.OneProof.WildPeriodCoprime
import Mathlib.RingTheory.Localization.BaseChange

namespace SZRaynaud

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI2 (IsInertia)
open ReductSplit (TΩ galTΩ unipSq_of_tate)
open scoped TensorProduct

noncomputable section

/-- The kernel's `PkgI3.AbVar.V`, with its Tate module taken over the chosen closure
`Ω` rather than the canonical `AlgebraicClosure K`. -/
abbrev VΩ {K : Type} [Field K] (A : PkgI3.AbVar K) (Ω : Type) [Field Ω] [Algebra K Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] : Type :=
  ℚ_[ℓ] ⊗[ℤ_[ℓ]] TΩ A Ω ℓ

/-- The action on `VΩ`, obtained by extending scalars in `galTΩ` just as in
`PkgI3.AbVar.galRep`. -/
def galVΩ {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (A : PkgI3.AbVar K)
    (ℓ : ℕ) [Fact ℓ.Prime] (σ : Ω ≃ₐ[K] Ω) : VΩ A Ω ℓ →ₗ[ℚ_[ℓ]] VΩ A Ω ℓ :=
  (galTΩ A ℓ σ).baseChange ℚ_[ℓ]

/-- A. Silverberg and Yu. G. Zarhin, *Semistable reduction and torsion subgroups of
abelian varieties*, Annales de l'Institut Fourier 45 (1995), 403–420, Theorem 3.3,
p. 405 (Galois criterion of semistable reduction, attributed to Grothendieck;
AI page read of 11-17; provenance (b), the paper cited at manuscript L816).

Both directions, for the print's Galois extension specialized to the separable
closure, as in the proofs of Lemma 5.5 (p. 411) and Proposition 6.1 (pp. 412–413).
For this infinite extension we read “semistable at w” as semistable at the
restriction of w to some finite separable subextension, allowing the base itself
(the left disjunct). This uses the discrete valuation notion of Definition 3.1
on that field, not on the infinite extension. We model the absolute group and
valuation using an algebraic closure `Ω`; restriction to its separable subfield
identifies the automorphism groups and inertia since purely inseparable
extensions have unique extensions of valuations and purely inseparable residue
extensions. The prime-to-residue-characteristic torsion is already separable.

For `W = V_ℓ(A)^I`, the condition that inertia act trivially on `V_ℓ(A)/W`
says that every difference `σ x - x` is in `W`, i.e. is fixed by every inertia
element `τ`. The equation below expresses this condition on the rational module. -/
def SilverbergZarhinThm33 : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (w : ValuationSubring Ω),
    w.comap (algebraMap K Ω) = O →
    ∀ (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : O) →
    (HasSemistableReductionSZ A O ∨
      ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧ Algebra.IsSeparable K E ∧
        IsDiscreteValuationRing (w.comap (algebraMap E Ω)) ∧
        HasSemistableReductionSZ (A.baseChange E) (w.comap (algebraMap E Ω))) →
    (HasSemistableReductionSZ A O ↔
      ∀ σ : Ω ≃ₐ[K] Ω, IsInertia w σ → ∀ τ : Ω ≃ₐ[K] Ω, IsInertia w τ →
        ∀ x : VΩ A Ω ℓ, galVΩ A ℓ τ (galVΩ A ℓ σ x - x) = galVΩ A ℓ σ x - x)

open PkgI3.Tate (T smulSeq smulSeq_congr)
open scoped nonZeroDivisors

/-- **ON THE SPOT (provenance (c)).** The transition maps recover coordinate `n`
from coordinate `n+k` after multiplying by `ℓ^k`. Any nonzero scalar in
`ℤ_ℓ` is a unit times such a power, so localization to `ℚ_ℓ` is injective. -/
private theorem tate_tmul_injective {ℓ : ℕ} [Fact ℓ.Prime] {M : Type} [AddCommGroup M] :
    Function.Injective (TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] (T ℓ M) 1) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro t ht
  obtain ⟨a, ha⟩ := (IsLocalizedModule.eq_zero_iff ℤ_[ℓ]⁰
    (TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] (T ℓ M) 1)).mp ht
  have ha0 : (a : ℤ_[ℓ]) ≠ 0 := nonZeroDivisors.ne_zero a.property
  rw [show a • t = (a : ℤ_[ℓ]) • t from rfl, PadicInt.unitCoeff_spec ha0, mul_smul] at ha
  have hpow : ((ℓ : ℤ_[ℓ]) ^ (a : ℤ_[ℓ]).valuation) • t = 0 := by
    have h := congrArg ((↑((PadicInt.unitCoeff ha0)⁻¹) : ℤ_[ℓ]) • ·) ha
    simpa only [smul_smul, Units.inv_mul_cancel_left, smul_zero] using h
  let k := (a : ℤ_[ℓ]).valuation
  have hshift (n j : ℕ) : (ℓ ^ j) • t.1 (n + j) = t.1 n := by
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, mul_smul, ← Nat.add_assoc, t.2.2, ih]
  apply Subtype.ext
  funext n
  change t.1 n = 0
  have h := congrArg (fun z : T ℓ M => z.1 (n + k)) hpow
  change smulSeq ((ℓ : ℤ_[ℓ]) ^ k) t.1 (n + k) = 0 at h
  rw [smulSeq_congr t.2 _ (c := ℓ ^ k) (by rw [map_pow, map_natCast, Nat.cast_pow]),
    hshift] at h
  exact h

/-- **ON THE SPOT (provenance (c)).** In the forward implication of Theorem 3.3
take `τ = σ`, then restrict to the Tate lattice. Each coordinate has square
zero for `σ - 1` and a prime-to-ℓ wild period, so it is fixed. -/
theorem elliot_of_sz33 (h : SilverbergZarhinThm33) : ElliotWildInertiaTrivial := by
  intro K _ _ O _ Ω _ _ _ w hw A hA ℓ _ hℓO σ hσ hwild t
  have hV := (h K O Ω w hw A ℓ hℓO (Or.inl hA)).mp hA σ hσ σ hσ
    ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] t)
  have hT : galTΩ A ℓ σ (galTΩ A ℓ σ t - t) = galTΩ A ℓ σ t - t := by
    apply tate_tmul_injective
    change ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] _) = (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] _
    simpa only [galVΩ, LinearMap.baseChange_tmul, ← TensorProduct.tmul_sub] using hV
  have hsquare : galTΩ A ℓ σ (galTΩ A ℓ σ t) - 2 • galTΩ A ℓ σ t + t = 0 := by
    calc
      _ = galTΩ A ℓ σ (galTΩ A ℓ σ t - t) - (galTΩ A ℓ σ t - t) := by
        rw [map_sub]
        abel
      _ = 0 := sub_eq_zero.mpr hT
  apply Subtype.ext
  funext n
  let x : A.Pt Ω := Additive.toMul (t.1 n)
  have ht : t.1 n = Additive.ofMul x := rfl
  have hx : x ^ (ℓ ^ n) = 1 := pow_smul_tate t n
  have hu := unipSq_of_tate A ℓ σ t n x ht hsquare
  obtain ⟨N, hcop, hit⟩ := wildPeriodCoprime_proof K O Ω w hw A ℓ hℓO σ hσ hwild n x hx
  have hfix : A.galAct σ x = x :=
    PkgI2.fixed_of_unipSq_of_iterate (ObjBridge.toGrp A) σ x ℓ n N 1 (by rwa [pow_one]) hx hu
      (by rwa [pow_one])
  exact congrArg Additive.ofMul hfix

#print axioms tate_tmul_injective
#print axioms elliot_of_sz33

end

end SZRaynaud

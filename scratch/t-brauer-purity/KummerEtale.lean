import Mathlib

/-!
# t-brauer-purity: a Kummer étaleness lemma (an ingredient of Abhyankar's lemma, leaf T2)

For a commutative ring `A`, `e ≥ 1` with `e` invertible in `A`, and a unit `u` of `A`,
`A[X]/(Xᵉ - u)` is étale over `A`.  In the standard proof of Abhyankar's lemma (SGA 1 X 3.6) this
is the step "adjoining an `e`-th root of a unit, `e` prime to the residue characteristic, is
unramified".  Proof: `(Xᵉ - u, 1)` is a standard étale pair, since
`(e⁻¹u⁻¹ X)·(Xᵉ - u)' + (-u⁻¹)·(Xᵉ - u) = 1`.
-/

open Polynomial

namespace TBrauerPurity

variable {A : Type*} [CommRing A]

/-- The standard étale pair `(Xᵉ - u, 1)`. -/
noncomputable def kummerPair (e : ℕ) (he : 0 < e) (heu : IsUnit (e : A)) (u : A)
    (hu : IsUnit u) : StandardEtalePair A where
  f := X ^ e - C u
  monic_f := monic_X_pow_sub_C u he.ne'
  g := 1
  cond := by
    refine ⟨C (((heu.unit⁻¹ : Aˣ) : A) * ((hu.unit⁻¹ : Aˣ) : A)) * X, -C ((hu.unit⁻¹ : Aˣ) : A), 1, ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
    have h1 : (((heu.unit⁻¹ : Aˣ) : A) : A) * ((k + 1 : ℕ) : A) = 1 := heu.val_inv_mul
    have h2 : (((hu.unit⁻¹ : Aˣ) : A) : A) * u = 1 := hu.val_inv_mul
    simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, pow_one]
    rw [show (C (↑(k + 1) : A) * X ^ (k + 1 - 1)) = C ((k + 1 : ℕ) : A) * X ^ k by
      simp]
    have e1 : C ((((heu.unit⁻¹ : Aˣ) : A) : A) * ((k + 1 : ℕ) : A)) = (1 : A[X]) := by rw [h1, C_1]
    have e2 : C ((((hu.unit⁻¹ : Aˣ) : A) : A) * u) = (1 : A[X]) := by rw [h2, C_1]
    simp only [C_mul] at e1 e2 ⊢
    linear_combination (X ^ (k + 1) * C (((hu.unit⁻¹ : Aˣ) : A) : A)) * e1 + e2

/-- **Kummer étaleness.** `A[X]/(Xᵉ - u)` is étale over `A` when `e ≥ 1` is invertible in `A`
and `u` is a unit. -/
theorem etale_adjoinRoot_X_pow_sub_C (e : ℕ) (he : 0 < e) (heu : IsUnit (e : A)) (u : A)
    (hu : IsUnit u) : Algebra.Etale A (AdjoinRoot (X ^ e - C u : A[X])) := by
  let P := kummerPair e he heu u hu
  have hx : P.HasMap (AdjoinRoot.root (X ^ e - C u : A[X])) := by
    refine ⟨?_, ?_⟩
    · change aeval _ (X ^ e - C u) = 0
      rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
    · change IsUnit (aeval _ (1 : A[X]))
      rw [map_one]; exact isUnit_one
  let φ : P.Ring →ₐ[A] AdjoinRoot (X ^ e - C u : A[X]) := P.lift _ hx
  let ψ : AdjoinRoot (X ^ e - C u : A[X]) →ₐ[A] P.Ring :=
    AdjoinRoot.liftAlgHom (X ^ e - C u : A[X]) (Algebra.ofId A P.Ring) P.X
      (by have h := P.hasMap_X.1; rw [aeval_def] at h; exact h)
  have hψ : ψ (AdjoinRoot.root _) = P.X := AdjoinRoot.liftAlgHom_root _ _ _ _
  let E : P.Ring ≃ₐ[A] AdjoinRoot (X ^ e - C u : A[X]) :=
    AlgEquiv.ofAlgHom φ ψ
      (AdjoinRoot.algHom_ext (by simp [φ, hψ, StandardEtalePair.lift_X]))
      (P.hom_ext (by simp [φ, hψ, StandardEtalePair.lift_X]))
  exact Algebra.Etale.of_equiv E

end TBrauerPurity

#print axioms TBrauerPurity.etale_adjoinRoot_X_pow_sub_C

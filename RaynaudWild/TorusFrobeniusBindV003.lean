import RaynaudWild.TorusFrobeniusV003

/-!
# The residue Frobenius power on torus points: coordinate form and group form

The torus data of a semistable special fibre are given in coordinates: for every algebra `R`
over the algebraic closure, a map `(Fin r → Rˣ) → X(R)`, natural in algebra maps
`t ↦ (Units.map f ∘ t)`, which is moreover a group homomorphism into the point group.

* `charOfFin`: the character of `ℤ^r` attached to a coordinate tuple; `charOfFin_basis`;
* `frob_pow_torus_point_fin`: for such a coordinate presentation there is `N ≥ 1` with
  `Spec(σ ^ N) ∘ e(t) = e(t ^ (q ^ N))` for every `t : Fin r → Ωˣ`;
* `frob_pow_torus_point_grp`: if `X` is a group scheme and `e_Ω` is multiplicative, the
  residue Frobenius power acts on torus points by `P ↦ P ^ (q ^ N)`;
* `frob_pow_torus_point_algClosure`: the hypothesis on `σ` is met by Mathlib's Frobenius
  automorphism of an algebraic closure of the finite residue field.
-/

open CategoryTheory AlgebraicGeometry MonObj

noncomputable section

namespace RaynaudWild.FrobDescent

variable {k Ω : Type} [Field k] [Finite k] [Field Ω] [Algebra k Ω]

/-- The character `v ↦ ∏ᵢ tᵢ ^ vᵢ` of `ℤ^r` attached to `t : Fin r → Rˣ`. -/
def charOfFin {R : Type} [CommRing R] {r : ℕ} (t : Fin r → Rˣ) :
    Multiplicative (Fin r → ℤ) →* Rˣ where
  toFun v := ∏ i, t i ^ (Multiplicative.toAdd v i)
  map_one' := by simp
  map_mul' v w := by
    simp only [toAdd_mul, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]

theorem charOfFin_basis {R : Type} [CommRing R] {r : ℕ} (t : Fin r → Rˣ) (i : Fin r) :
    charOfFin t (Multiplicative.ofAdd (Pi.single i (1 : ℤ))) = t i := by
  show ∏ j, t j ^ ((Pi.single i (1 : ℤ) : Fin r → ℤ) j : ℤ) = t i
  rw [Fintype.prod_eq_single i]
  · simp
  · intro j hj
    simp [Pi.single_apply, hj]

/-- The coordinates of a character in the standard basis. -/
def finOfChar {R : Type} [CommRing R] {r : ℕ} (χ : Multiplicative (Fin r → ℤ) →* Rˣ) :
    Fin r → Rˣ :=
  fun i => χ (Multiplicative.ofAdd (Pi.single i (1 : ℤ)))

variable (X : Over (Spec (CommRingCat.of k)))

/-- **Coordinate form.** -/
theorem frob_pow_torus_point_fin [Algebra.IsAlgebraic k Ω] (σ : Ω ≃ₐ[k] Ω)
    (hσ : ∀ x : Ω, σ x = x ^ Nat.card k) [LocallyOfFinitePresentation X.hom] (r : ℕ)
    (e : ∀ (R : Type) [CommRing R] [Algebra Ω R],
      (Fin r → Rˣ) → (kPt (k := k) (Ω := Ω) R ⟶ X))
    (he : ∀ (R S : Type) [CommRing R] [Algebra Ω R] [CommRing S] [Algebra Ω S]
      (f : R →ₐ[Ω] S) (t : Fin r → Rˣ),
      e S (fun i => Units.map (f : R →* S) (t i)) = kPtMap f ≫ e R t) :
    ∃ N : ℕ, 0 < N ∧ ∀ t : Fin r → Ωˣ,
      galK (σ ^ N) ≫ e Ω t = e Ω (fun i => t i ^ (Nat.card k ^ N)) := by
  obtain ⟨N, hN, h⟩ := frob_pow_torus_point (M := Multiplicative (Fin r → ℤ)) X σ hσ
    (fun R _ _ χ => e R (finOfChar χ))
    (fun R S _ _ _ _ f χ => by
      show e S (finOfChar ((Units.map (f : R →* S)).comp χ)) = kPtMap f ≫ e R (finOfChar χ)
      rw [← he]
      rfl)
  refine ⟨N, hN, fun t => ?_⟩
  have h1 := h (charOfFin t)
  have hb : finOfChar (charOfFin t) = t := funext fun i => charOfFin_basis t i
  have hp : finOfChar (charOfFin t ^ (Nat.card k ^ N)) = fun i => t i ^ (Nat.card k ^ N) := by
    funext i
    simp only [finOfChar, MonoidHom.pow_apply]
    rw [charOfFin_basis]
  simp only [hb, hp] at h1
  exact h1

/-- **Group form.** If `X` is a group scheme over `k` and `e_Ω` is multiplicative, the residue
Frobenius power acts on torus points by `P ↦ P ^ (q ^ N)`. -/
theorem frob_pow_torus_point_grp [Algebra.IsAlgebraic k Ω] (σ : Ω ≃ₐ[k] Ω)
    (hσ : ∀ x : Ω, σ x = x ^ Nat.card k) [LocallyOfFinitePresentation X.hom] [GrpObj X]
    (r : ℕ)
    (e : ∀ (R : Type) [CommRing R] [Algebra Ω R],
      (Fin r → Rˣ) → (kPt (k := k) (Ω := Ω) R ⟶ X))
    (he : ∀ (R S : Type) [CommRing R] [Algebra Ω R] [CommRing S] [Algebra Ω S]
      (f : R →ₐ[Ω] S) (t : Fin r → Rˣ),
      e S (fun i => Units.map (f : R →* S) (t i)) = kPtMap f ≫ e R t)
    (hmul : ∀ t s : Fin r → Ωˣ, e Ω (t * s) = e Ω t * e Ω s) :
    ∃ N : ℕ, 0 < N ∧ ∀ t : Fin r → Ωˣ,
      galK (σ ^ N) ≫ e Ω t = (e Ω t) ^ (Nat.card k ^ N) := by
  obtain ⟨N, hN, h⟩ := frob_pow_torus_point_fin X σ hσ r e he
  refine ⟨N, hN, fun t => ?_⟩
  have hsucc : ∀ m : ℕ, e Ω (t ^ (m + 1)) = (e Ω t) ^ (m + 1) := by
    intro m
    induction m with
    | zero => rw [zero_add, pow_one, pow_one]
    | succ m ih => rw [pow_succ t (m + 1), hmul, ih, ← pow_succ]
  have hq : 0 < Nat.card k ^ N := pow_pos Nat.card_pos N
  have hpow : (fun i => t i ^ (Nat.card k ^ N)) = t ^ (Nat.card k ^ N) := rfl
  rw [h, hpow, ← Nat.sub_add_cancel hq, hsucc]

/-- **Instantiation with Mathlib's Frobenius** of an algebraic closure of the residue field. -/
theorem frob_pow_torus_point_algClosure [Fintype k] [LocallyOfFinitePresentation X.hom] (r : ℕ)
    (e : ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R],
      (Fin r → Rˣ) → (kPt (k := k) (Ω := AlgebraicClosure k) R ⟶ X))
    (he : ∀ (R S : Type) [CommRing R] [Algebra (AlgebraicClosure k) R] [CommRing S]
      [Algebra (AlgebraicClosure k) S] (f : R →ₐ[AlgebraicClosure k] S) (t : Fin r → Rˣ),
      e S (fun i => Units.map (f : R →* S) (t i)) = kPtMap f ≫ e R t) :
    ∃ N : ℕ, 0 < N ∧ ∀ t : Fin r → (AlgebraicClosure k)ˣ,
      galK (FiniteField.frobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k) ^ N) ≫
          e (AlgebraicClosure k) t =
        e (AlgebraicClosure k) (fun i => t i ^ (Nat.card k ^ N)) :=
  frob_pow_torus_point_fin X (FiniteField.frobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k))
    (fun x => by
      rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic, Nat.card_eq_fintype_card]) r e he

end RaynaudWild.FrobDescent

#print axioms RaynaudWild.FrobDescent.exists_frob_invariant
#print axioms RaynaudWild.FrobDescent.frob_pow_torus_point
#print axioms RaynaudWild.FrobDescent.frob_pow_torus_point_fin
#print axioms RaynaudWild.FrobDescent.frob_pow_torus_point_grp
#print axioms RaynaudWild.FrobDescent.frob_pow_torus_point_algClosure

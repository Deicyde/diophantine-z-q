import ZInQKernel.Contrib.OneProof.FowlerBridges
import ZInQKernel.Contrib.OneProof.FowlerUniqueDiscriminant
import Mathlib.Algebra.QuadraticAlgebra.Int
import Mathlib.NumberTheory.FundamentalDiscriminant

/-! # Fowler's class number as a function of the order discriminant -/

namespace HDec.CMBranch.FowlerBridges

open NumberField Module TauCeti.GlobalNumberFields

private noncomputable def picEquiv {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) :
    CommRing.Pic A ≃ CommRing.Pic B where
  toFun := CommRing.Pic.mapRingHom e.toRingHom
  invFun := CommRing.Pic.mapRingHom e.symm.toRingHom
  left_inv I := by
    rw [CommRing.Pic.mapRingHom_mapRingHom]
    have h : e.symm.toRingHom.comp e.toRingHom = RingHom.id A := by ext x; exact e.symm_apply_apply x
    rw [h, CommRing.Pic.mapRingHom_id_apply]
  right_inv I := by
    rw [CommRing.Pic.mapRingHom_mapRingHom]
    have h : e.toRingHom.comp e.symm.toRingHom = RingHom.id B := by ext x; exact e.apply_symm_apply x
    rw [h, CommRing.Pic.mapRingHom_id_apply]

/-- The proper class number of a quadratic order is invariant under ring isomorphism. -/
theorem properClassNumber_ringEquiv {k l : Type} [Field k] [NumberField k]
    [Field l] [NumberField l] (hk : finrank ℚ k = 2) (hl : finrank ℚ l = 2)
    (O : NumberFieldOrder k) (P : NumberFieldOrder l)
    (e : O.toSubalgebra ≃+* P.toSubalgebra) : properClassNumber O = properClassNumber P := by
  let eO := (properIdealClassesEquivClassGroup O hk).trans
    (ClassGroup.equivPic O.toSubalgebra).toEquiv
  let eP := (properIdealClassesEquivClassGroup P hl).trans
    (ClassGroup.equivPic P.toSubalgebra).toEquiv
  exact Nat.card_congr (eO.trans ((picEquiv e).trans eP.symm))

/-- The proper class number agrees for quadratic orders of equal discriminant. -/
theorem properClassNumber_eq_of_discr_eq {k l : Type} [Field k] [NumberField k]
    [Field l] [NumberField l] (hk : finrank ℚ k = 2) (hl : finrank ℚ l = 2)
    (O : NumberFieldOrder k) (P : NumberFieldOrder l) (h : O.discr = P.discr) :
    properClassNumber O = properClassNumber P := by
  obtain ⟨e⟩ := orders_ringEquiv_of_discr_eq hk hl O P h
  exact properClassNumber_ringEquiv hk hl O P e

private abbrev Model (Δ : ℤ) :=
  QuadraticAlgebra ℚ ((Δ / 4 : ℤ) : ℚ) ((Δ % 4 : ℤ) : ℚ)

private theorem modelDiscr (Δ : ℤ) (hmod : Δ % 4 = 0 ∨ Δ % 4 = 1) :
    QuadraticAlgebra.discr ((Δ / 4 : ℤ) : ℚ) ((Δ % 4 : ℤ) : ℚ) = (Δ : ℚ) := by
  rw [QuadraticAlgebra.discr_intCast, QuadraticAlgebra.discr_ediv_emod hmod]

private theorem modelNonsquare (Δ : ℤ) (hneg : Δ < 0) (hmod : Δ % 4 = 0 ∨ Δ % 4 = 1) :
    Fact (¬ IsSquare (QuadraticAlgebra.discr ((Δ / 4 : ℤ) : ℚ) ((Δ % 4 : ℤ) : ℚ))) := by
  refine ⟨?_⟩
  rw [modelDiscr Δ hmod, isSquare_iff_exists_sq]
  rintro ⟨x, hx⟩
  have hnegQ : (Δ : ℚ) < 0 := by exact_mod_cast hneg
  nlinarith [sq_nonneg x]

private theorem modelIntNonsquare (Δ : ℤ) (hneg : Δ < 0) (hmod : Δ % 4 = 0 ∨ Δ % 4 = 1) :
    Fact (¬ IsSquare (QuadraticAlgebra.discr (Δ / 4 : ℤ) (Δ % 4))) := by
  refine ⟨?_⟩
  rw [QuadraticAlgebra.discr_ediv_emod hmod, isSquare_iff_exists_sq]
  rintro ⟨x, hx⟩
  nlinarith [sq_nonneg x]

private theorem modelNumberField (Δ : ℤ)
    [Fact (¬ IsSquare (QuadraticAlgebra.discr ((Δ / 4 : ℤ) : ℚ) ((Δ % 4 : ℤ) : ℚ)))] :
    NumberField (Model Δ) := ⟨⟩

attribute [local instance] modelNumberField

private theorem modelTotallyComplex (Δ : ℤ) (hneg : Δ < 0) (hmod : Δ % 4 = 0 ∨ Δ % 4 = 1)
    [Fact (¬ IsSquare (QuadraticAlgebra.discr ((Δ / 4 : ℤ) : ℚ) ((Δ % 4 : ℤ) : ℚ)))] :
    IsTotallyComplex (Model Δ) := by
  refine ⟨fun v => ?_⟩
  rw [InfinitePlace.isComplex_iff]
  intro hv
  have hs := QuadraticAlgebra.algebraMap_discr ((Δ / 4 : ℤ) : ℚ) ((Δ % 4 : ℤ) : ℚ)
  rw [modelDiscr Δ hmod] at hs
  have hr := congrArg hv.embedding hs
  have he : hv.embedding (algebraMap ℚ (Model Δ) (Δ : ℚ)) = (Δ : ℝ) := by simp
  rw [he, map_pow] at hr
  have hnegR : (Δ : ℝ) < 0 := by exact_mod_cast hneg
  rw [hr] at hnegR
  exact (not_lt_of_ge (sq_nonneg _)) hnegR

private noncomputable def canonicalOrder (Δ : ℤ) (hneg : Δ < 0)
    (hmod : Δ % 4 = 0 ∨ Δ % 4 = 1) :
    haveI := modelNonsquare Δ hneg hmod
    NumberFieldOrder (Model Δ) := by
  letI := modelNonsquare Δ hneg hmod
  letI := modelIntNonsquare Δ hneg hmod
  exact NumberFieldOrder.ofIsFractionRing (QuadraticAlgebra ℤ (Δ / 4) (Δ % 4)) (Model Δ)

private theorem canonicalOrder_discr (Δ : ℤ) (hneg : Δ < 0)
    (hmod : Δ % 4 = 0 ∨ Δ % 4 = 1) :
    haveI := modelNonsquare Δ hneg hmod
    (canonicalOrder Δ hneg hmod).discr = Δ := by
  let := modelNonsquare Δ hneg hmod
  let := modelIntNonsquare Δ hneg hmod
  let O := canonicalOrder Δ hneg hmod
  let b := QuadraticAlgebra.basis (Δ / 4) (Δ % 4)
  let e : QuadraticAlgebra ℤ (Δ / 4) (Δ % 4) ≃+* O.toSubalgebra :=
    NumberFieldOrder.ofIsFractionRingEquiv _ _
  calc
    O.discr = Algebra.discr ℤ (b.map e.toIntAlgEquiv.toLinearEquiv) :=
      (O.discr_eq_discr _).symm
    _ = Algebra.discr ℤ b := (Algebra.discr_eq_discr_of_algEquiv b e.toIntAlgEquiv).symm
    _ = Δ := (quadraticAlgebra_basis_discr _ _).trans (QuadraticAlgebra.discr_ediv_emod hmod)

/-- For a negative order discriminant `Δ`, the representative used here has integral
basis `(1, ω)` and relation `ω² = Δ / 4 + (Δ % 4) ω` (integer division and remainder).
Outside the domain of negative order discriminants the default class number is zero. -/
noncomputable def hDelta (Δ : ℤ) : ℕ := by
  classical
  exact if h : Δ < 0 ∧ (Δ % 4 = 0 ∨ Δ % 4 = 1) then
    haveI := modelNonsquare Δ h.1 h.2
    properClassNumber (canonicalOrder Δ h.1 h.2)
  else 0

/-- Every imaginary quadratic order of discriminant `Δ` has the class number
of the canonical representative. The comparison uses only the quadratic degree
and the two discriminant conditions. -/
theorem hDelta_eq_properClassNumber {k : Type} [Field k] [NumberField k] {Δ : ℤ}
    (hneg : Δ < 0) (hmod : Δ % 4 = 0 ∨ Δ % 4 = 1) (hk : finrank ℚ k = 2)
    (O : NumberFieldOrder k) (hO : O.discr = Δ) :
    hDelta Δ = properClassNumber O := by
  let := modelNonsquare Δ hneg hmod
  rw [hDelta, dite_eq_left ⟨hneg, hmod⟩]
  exact properClassNumber_eq_of_discr_eq (QuadraticAlgebra.finrank_eq_two _ _) hk _ O
    ((canonicalOrder_discr Δ hneg hmod).trans hO.symm)

/-- A quadratic order of discriminant `Δ < 0` has fraction field `ℚ(√Δ)`, written
as Mathlib's quadratic algebra with generator squaring to `Δ`. -/
theorem field_ringEquiv_sqrt_orderDiscr {k : Type*} [Field k] [NumberField k] {Δ : ℤ}
    (hneg : Δ < 0) (hmod : Δ % 4 = 0 ∨ Δ % 4 = 1) (hk : finrank ℚ k = 2)
    (O : NumberFieldOrder k) (hO : O.discr = Δ) :
    Nonempty (k ≃+* QuadraticAlgebra ℚ (Δ : ℚ) 0) := by
  let := modelNonsquare Δ hneg hmod
  obtain ⟨e⟩ := fields_ringEquiv_of_order_discr_eq hk (QuadraticAlgebra.finrank_eq_two _ _)
    O (canonicalOrder Δ hneg hmod) (hO.trans (canonicalOrder_discr Δ hneg hmod).symm)
  let : Invertible (2 : ℚ) := invertibleOfNonzero two_ne_zero
  have f := (QuadraticAlgebra.algEquivDiscrZero ((Δ / 4 : ℤ) : ℚ) ((Δ % 4 : ℤ) : ℚ)).toRingEquiv
  rw [modelDiscr Δ hmod] at f
  exact ⟨e.trans f⟩

private theorem fieldDiscrNeg {k : Type*} [Field k] [NumberField k] [IsTotallyComplex k]
    (hk : finrank ℚ k = 2) : NumberField.discr k < 0 := by
  have hdim := NumberField.IsTotallyComplex.finrank (K := k)
  have hc : InfinitePlace.nrComplexPlaces k = 1 := by rw [hk] at hdim; omega
  have hs := NumberField.sign_discr k
  rw [hc] at hs
  norm_num at hs
  exact hs

/-- An imaginary quadratic field is `ℚ(√d)` for its own field discriminant `d`. -/
theorem field_ringEquiv_sqrt_discr {k : Type*} [Field k] [NumberField k] [IsTotallyComplex k]
    (hk : finrank ℚ k = 2) :
    Nonempty (k ≃+* QuadraticAlgebra ℚ (NumberField.discr k : ℚ) 0) := by
  let O := maximalNumberFieldOrder k
  have hd : O.discr = NumberField.discr k := NumberFieldOrder.discr_maximal
  have hmod := order_discr_mod_four hk O
  rw [hd] at hmod
  exact field_ringEquiv_sqrt_orderDiscr (fieldDiscrNeg hk) hmod hk O hd

/-- The discriminant of an imaginary quadratic field is fundamental. If it were a
prime square times another discriminant, the order of that smaller discriminant
would lie in an isomorphic field, contradicting the maximal-order index formula. -/
theorem isFundamentalDiscr_field {k : Type*} [Field k] [NumberField k] [IsTotallyComplex k]
    (hk : finrank ℚ k = 2) : Int.IsFundamentalDiscr (NumberField.discr k) := by
  rw [Int.isFundamentalDiscr_iff_forall_prime]
  refine ⟨by simpa only [NumberFieldOrder.discr_maximal] using
    order_discr_mod_four hk (maximalNumberFieldOrder k), ?_⟩
  intro p hp
  rintro ⟨D, hD, hmod⟩
  have hneg := fieldDiscrNeg hk
  have hnegD : D < 0 := by
    by_contra! h
    have hn : 0 ≤ NumberField.discr k := by
      rw [hD]
      exact mul_nonneg (sq_nonneg (p : ℤ)) h
    exact (not_lt_of_ge hn) hneg
  let := modelNonsquare D hnegD hmod
  let O := canonicalOrder D hnegD hmod
  obtain ⟨e⟩ := field_ringEquiv_sqrt_discr hk
  obtain ⟨f⟩ := field_ringEquiv_sqrt_orderDiscr hnegD hmod
    (QuadraticAlgebra.finrank_eq_two _ _) O (canonicalOrder_discr D hnegD hmod)
  let : Invertible (2 : ℚ) := invertibleOfNonzero two_ne_zero
  obtain ⟨g⟩ := QuadraticAlgebra.nonempty_algEquiv_iff_of_invertible_two
    (a := (NumberField.discr k : ℚ)) (b := 0) (a' := (D : ℚ)) (b' := 0) |>.mpr
      ⟨Units.mk0 (p : ℚ) (by exact_mod_cast hp.ne_zero), by
        have hQ : (NumberField.discr k : ℚ) = (p : ℚ) ^ 2 * (D : ℚ) := by exact_mod_cast hD
        simp [QuadraticAlgebra.discr_def, hQ]
        ring⟩
  have hd := NumberField.discr_eq_discr_of_ringEquiv k (e.trans (g.toRingEquiv.trans f.symm))
  have hidx := O.discr_eq_index_sq_mul
  rw [canonicalOrder_discr, ← hd] at hidx
  have hp₂ : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  have hp_sq : (1 : ℤ) < (p : ℤ) ^ 2 := by nlinarith
  have hlt : NumberField.discr k < D := calc
    NumberField.discr k = (p : ℤ) ^ 2 * D := hD
    _ < 1 * D := mul_lt_mul_of_neg_right hp_sq hnegD
    _ = D := one_mul D
  have hidx_pos : (0 : ℤ) < O.index := by exact_mod_cast Nat.pos_of_ne_zero O.index_ne_zero
  have hidx_sq : (1 : ℤ) ≤ (O.index : ℤ) ^ 2 := by
    have := sq_pos_of_pos hidx_pos
    omega
  have hle : D ≤ NumberField.discr k := by
    conv_lhs => rw [hidx]
    simpa using mul_le_mul_of_nonpos_right hidx_sq hneg.le
  exact (not_lt_of_ge hle) hlt

/-- Fowler, Proposition 2·7, p. 615. The class number on p. 613 is `hDelta`,
whose value is independent of the representative by `hDelta_eq_properClassNumber`. -/
def FowlerProp27PrintCanonical : Prop :=
  ∀ (Δ : ℤ), Δ < 0 → (Δ % 4 = 0 ∨ Δ % 4 = 1) →
    ∀ n : ℕ, 0 < n → hDelta Δ ≤ n →
      Real.sqrt |(Δ : ℝ)| ≤ 2 * (n : ℝ) ^ 2 * Real.exp (21000 * (n : ℝ) ^ 2)

/-- Fowler's bound with a discriminant-indexed class number gives the existing
order-quantified formulation. -/
theorem fowlerProp27Print_of_canonical : FowlerProp27PrintCanonical → FowlerProp27Print := by
  intro h Δ hneg hmod k _ _ _ hk O hO n hn hcard
  exact h Δ hneg hmod n hn ((hDelta_eq_properClassNumber hneg hmod hk O hO).symm ▸ hcard)

/-- The existing order-quantified statement also implies the canonical one. -/
theorem fowlerProp27Print_iff_canonical :
    FowlerProp27Print ↔ FowlerProp27PrintCanonical := by
  refine ⟨?_, fowlerProp27Print_of_canonical⟩
  intro h Δ hneg hmod n hn hcard
  let := modelNonsquare Δ hneg hmod
  let := modelTotallyComplex Δ hneg hmod
  let O := canonicalOrder Δ hneg hmod
  have hk : finrank ℚ (Model Δ) = 2 := QuadraticAlgebra.finrank_eq_two _ _
  have hO := canonicalOrder_discr Δ hneg hmod
  exact h Δ hneg hmod (Model Δ) hk O hO n hn
    (hDelta_eq_properClassNumber hneg hmod hk O hO ▸ hcard)

/-- The canonical print-form statement is the only input needed for the live row. -/
theorem fowlerProp27_of_canonical : FowlerProp27PrintCanonical → FowlerProp27 :=
  fun h => fowlerProp27_of_print (fowlerProp27Print_of_canonical h)

end HDec.CMBranch.FowlerBridges

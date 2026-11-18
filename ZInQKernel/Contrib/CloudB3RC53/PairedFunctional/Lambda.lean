import Mathlib

/-!
# RC53 PairedFunctional: units of `Λ = ℤ₂[[t]]` at the primes used by the paired functional

Proposition `ex:arith-paired-functional` (`diophantine_zq.tex` L3704–3880) builds integral
contractions of the full local complexes at the active and moving primes. Their integrality rests
on a few facts about the Iwasawa algebra `Λ = ℤ₂[[t]]`, which this file proves:

* `LamPrimes`: `(2)`, `(t)` and `(t+2)` are pairwise distinct nonzero prime ideals of `Λ`
  (tex L3729, L3755–3760).
* `ActiveInertiaUnit`: at every height-one prime `𝔭 ≠ (2)`, `2` and `−2` are units of `Λ_𝔭`
  ("inertia minus one is `−2`, a unit at `𝔭 ≠ (2)`", tex L3755–3757; L5184–5185).
* `MovingInertiaUnit`: at every height-one prime `𝔭 ≠ (t)`, `t` is a unit of `Λ_𝔭`
  ("at the moving prime inertia minus one is invertible unless `𝔭 = (t)`", tex L3757–3758;
  L5185–5186).
* `QuadraticPrimesHeightOne`: non-vacuity — `(t)` and `(t+2)` have height exactly one and differ
  from `(2)`; at `(t+2)` both `2` and `t` are units ("`(t+2)` is treated by the inertia
  contraction", tex L3760; L5190–5191 "including both quadratic specializations").
* `CentralDeterminantUnit`: at `(t)`, an element (or matrix determinant) with nonzero constant
  coefficient is a unit of `Λ_(t)` ("at `(t)` the nonzero central Frobenius determinants give
  integral adjugate contractions", tex L3758–3760; L5186–5187 "nonzero and hence units in `R`").
* `ResidualFrobeniusNotInTwo`: for odd `a` and odd `q`, `(1+t)^a − q ∉ (2)`, and so the
  determinant `((1+t)^a − q)^n` of the scalar matrix `((1+t)^a − q) · 1ₙ` is not in `(2)` (tex
  L3730–3731: the residual active Frobenius is `(1+t)^a I` with `a` odd, so `A = Φ − 1` and
  `D = Φ − N_q(g)`, whose augmentation is `Φ − q`, are invertible over `𝒪[G]`).
  Turning "not in `(2)`" into "a unit of `𝒪 = (Λ_(2))^`" is the `𝒪`-model lemma
  `isUnit_algebraMap_of_not_mem_span_two` of the determinant lane, and invertibility over
  `𝒪[G]` is its augmentation criterion; neither is restated here.

All nodes are PROVED. No height-one prime is assumed principal: the argument only uses that
`(2)` and `(t)` are prime, via Mathlib's `Ideal.eq_span_singleton_of_height_eq_one`.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.PairedFunctional

open PowerSeries

/-- The Iwasawa algebra `Λ = ℤ₂[[t]]` (tex L2745–2748), with `t = X`. -/
abbrev Lam : Type := PowerSeries ℤ_[2]

/-- Coefficientwise reduction `Λ → 𝔽₂[[t]]`. -/
abbrev redTwo : Lam →+* PowerSeries (ZMod 2) := PowerSeries.map (PadicInt.toZMod (p := 2))

/-- `f ∈ (2)` iff every coefficient of `f` is divisible by `2`. PROVED. -/
theorem mem_span_two_iff (f : Lam) :
    f ∈ Ideal.span {(2 : Lam)} ↔ ∀ n, (2 : ℤ_[2]) ∣ coeff n f := by
  constructor
  · intro h n
    obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp h
    refine ⟨coeff n g, ?_⟩
    rw [show (2 : Lam) = C (2 : ℤ_[2]) from (map_ofNat C 2).symm, mul_comm, coeff_C_mul, mul_comm]
  · intro h
    choose d hd using h
    refine Ideal.mem_span_singleton'.mpr ⟨PowerSeries.mk d, ?_⟩
    ext n
    rw [show (2 : Lam) = C (2 : ℤ_[2]) from (map_ofNat C 2).symm, mul_comm, coeff_C_mul, coeff_mk, hd n]

/-- `(2)` is the kernel of the reduction `Λ → 𝔽₂[[t]]`. PROVED. -/
theorem span_two_eq_ker : Ideal.span {(2 : Lam)} = RingHom.ker redTwo := by
  ext f
  rw [mem_span_two_iff, RingHom.mem_ker]
  constructor
  · intro h
    ext n
    rw [coeff_map, map_zero, ← RingHom.mem_ker, PadicInt.ker_toZMod,
      PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton.mpr (by exact_mod_cast h n)
  · intro h n
    have := congrArg (coeff n) h
    rw [coeff_map, map_zero, ← RingHom.mem_ker, PadicInt.ker_toZMod,
      PadicInt.maximalIdeal_eq_span_p] at this
    exact_mod_cast Ideal.mem_span_singleton.mp this

theorem span_two_isPrime : (Ideal.span {(2 : Lam)}).IsPrime := by
  rw [span_two_eq_ker]; exact RingHom.ker_isPrime _

/-- `coeff 1 ((1 + t)^a) = a`. -/
theorem coeff_one_one_add_X_pow (a : ℕ) : coeff 1 ((1 + X : Lam) ^ a) = a := by
  induction a with
  | zero => simp [coeff_one]
  | succ n ih =>
    rw [pow_succ, mul_add, mul_one, map_add, ih, coeff_succ_mul_X, coeff_zero_eq_constantCoeff_apply,
      map_pow, map_add, constantCoeff_one, constantCoeff_X, add_zero, one_pow]
    push_cast; ring

/-- `t ∉ (2)`-type criterion: a series whose `t`-coefficient is an odd natural number is not in
`(2)`. -/
theorem not_mem_span_two_of_coeff_one {f : Lam} {a : ℕ} (ha : Odd a) (hf : coeff 1 f = a) :
    f ∉ Ideal.span {(2 : Lam)} := by
  intro h
  have h1 := (mem_span_two_iff f).mp h 1
  rw [hf] at h1
  obtain ⟨d, hd⟩ := h1
  have := congrArg (PadicInt.toZMod (p := 2)) hd
  rw [map_natCast, map_mul, map_ofNat, show (2 : ZMod 2) = 0 from rfl, zero_mul,
    ZMod.natCast_eq_zero_iff_even] at this
  exact (Nat.not_even_iff_odd.mpr ha) this

theorem X_not_mem_span_two : (X : Lam) ∉ Ideal.span {(2 : Lam)} :=
  not_mem_span_two_of_coeff_one (a := 1) odd_one (by simp [coeff_X])

theorem X_add_two_not_mem_span_two : (X + 2 : Lam) ∉ Ideal.span {(2 : Lam)} := by
  refine not_mem_span_two_of_coeff_one (a := 1) odd_one ?_
  rw [map_add, coeff_X, show (2 : Lam) = C (2 : ℤ_[2]) from (map_ofNat C 2).symm, coeff_C]
  simp

/-- `t + 2` as a polynomial over `ℤ₂`; it is distinguished at the maximal ideal `(2)`. -/
theorem isDistinguished_X_add_two :
    (Polynomial.X - Polynomial.C (-2 : ℤ_[2])).IsDistinguishedAt
      (IsLocalRing.maximalIdeal ℤ_[2]) where
  mem {n} hn := by
    rw [Polynomial.natDegree_X_sub_C] at hn
    obtain rfl : n = 0 := by omega
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero, zero_sub, neg_neg,
      PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton_self _
  monic := Polynomial.monic_X_sub_C _

theorem span_X_add_two_isPrime : (Ideal.span {(X + 2 : Lam)}).IsPrime := by
  have e := isDistinguished_X_add_two.algEquivQuotient
  have hcoe : ((Polynomial.X - Polynomial.C (-2 : ℤ_[2]) : Polynomial ℤ_[2]) : Lam) = X + 2 := by
    rw [Polynomial.coe_sub, Polynomial.coe_X, Polynomial.coe_C, map_neg, sub_neg_eq_add,
      map_ofNat]
  rw [hcoe] at e
  have e2 := Polynomial.quotientSpanXSubCAlgEquiv (R := ℤ_[2]) (-2)
  have : IsDomain (Lam ⧸ Ideal.span {(X + 2 : Lam)}) :=
    (e.symm.trans e2).toMulEquiv.isDomain_iff.mpr inferInstance
  exact (Ideal.Quotient.isDomain_iff_prime _).mp this

/-- **`(2)`, `(t)`, `(t+2)` are pairwise distinct nonzero primes of `Λ`** (tex L3729,
L3755–3760, L5184–5191: the primes at which the active and moving contractions are discussed).
PROVED. -/
def LamPrimes : Prop :=
  (Ideal.span {(2 : Lam)}).IsPrime ∧ (Ideal.span {(X : Lam)}).IsPrime ∧
    (Ideal.span {(X + 2 : Lam)}).IsPrime ∧
    Ideal.span {(2 : Lam)} ≠ ⊥ ∧ Ideal.span {(X : Lam)} ≠ ⊥ ∧ Ideal.span {(X + 2 : Lam)} ≠ ⊥ ∧
    Ideal.span {(X : Lam)} ≠ Ideal.span {(2 : Lam)} ∧
    Ideal.span {(X + 2 : Lam)} ≠ Ideal.span {(2 : Lam)} ∧
    Ideal.span {(X + 2 : Lam)} ≠ Ideal.span {(X : Lam)}

theorem two_ne_zero_lam : (2 : Lam) ≠ 0 := by
  intro h
  have := congrArg (coeff 0) h
  rw [show (2 : Lam) = C (2 : ℤ_[2]) from (map_ofNat C 2).symm, coeff_C, map_zero] at this
  simp at this

theorem X_add_two_ne_zero : (X + 2 : Lam) ≠ 0 := fun h =>
  X_add_two_not_mem_span_two (h ▸ Ideal.zero_mem _)

theorem lamPrimes_proof : LamPrimes := by
  refine ⟨span_two_isPrime, span_X_isPrime, span_X_add_two_isPrime, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Ne, Ideal.span_singleton_eq_bot]; exact two_ne_zero_lam
  · rw [Ne, Ideal.span_singleton_eq_bot]; exact X_ne_zero
  · rw [Ne, Ideal.span_singleton_eq_bot]; exact X_add_two_ne_zero
  · intro h; exact X_not_mem_span_two (h ▸ Ideal.mem_span_singleton_self _)
  · intro h; exact X_add_two_not_mem_span_two (h ▸ Ideal.mem_span_singleton_self _)
  · intro h
    have hm : (X + 2 : Lam) ∈ Ideal.span {(X : Lam)} := h ▸ Ideal.mem_span_singleton_self _
    rw [Ideal.mem_span_singleton, X_dvd_iff, map_add, constantCoeff_X, zero_add,
      map_ofNat] at hm
    exact two_ne_zero hm

/-- A height-one prime containing a prime element `x` is `(x)`. -/
theorem eq_of_height_one_of_mem {p : Ideal Lam} [p.IsPrime] (hp : p.height = 1) {x : Lam}
    (hxp : (Ideal.span {x}).IsPrime) (hx0 : x ≠ 0) (hx : x ∈ p) : p = Ideal.span {x} :=
  Ideal.eq_span_singleton_of_height_eq_one hp hx
    ((Ideal.span_singleton_prime hx0).mp hxp)

/-- **Active primes: `−2` is a unit at every height-one prime `𝔭 ≠ (2)`** (tex L3755–3757:
"Its active primes are precisely the primes ramified in that constituent, so inertia minus one is
`−2`, a unit at `𝔭 ≠ (2)`"; L5184–5185). PROVED. -/
def ActiveInertiaUnit : Prop :=
  ∀ (p : Ideal Lam) [p.IsPrime], p.height = 1 → p ≠ Ideal.span {(2 : Lam)} →
    (2 : Lam) ∉ p ∧ IsUnit (algebraMap Lam (Localization.AtPrime p) 2) ∧
      IsUnit (algebraMap Lam (Localization.AtPrime p) (-2))

theorem activeInertiaUnit_proof : ActiveInertiaUnit := by
  intro p _ hp hne
  have h2 : (2 : Lam) ∉ p := fun h =>
    hne (eq_of_height_one_of_mem hp span_two_isPrime two_ne_zero_lam h)
  have hu : IsUnit (algebraMap Lam (Localization.AtPrime p) 2) :=
    IsLocalization.map_units (Localization.AtPrime p) (⟨2, h2⟩ : p.primeCompl)
  refine ⟨h2, hu, ?_⟩
  rw [map_neg]; exact hu.neg

/-- **Moving prime: `t` is a unit at every height-one prime `𝔭 ≠ (t)`** (tex L3757–3758: "At
the moving prime inertia minus one is invertible unless `𝔭 = (t)`"; there inertia minus one is
`t` times a unit, L3753–3754; L5185–5186). PROVED. -/
def MovingInertiaUnit : Prop :=
  ∀ (p : Ideal Lam) [p.IsPrime], p.height = 1 → p ≠ Ideal.span {(X : Lam)} →
    (X : Lam) ∉ p ∧ IsUnit (algebraMap Lam (Localization.AtPrime p) X)

theorem movingInertiaUnit_proof : MovingInertiaUnit := by
  intro p _ hp hne
  have hX : (X : Lam) ∉ p := fun h => hne (eq_of_height_one_of_mem hp span_X_isPrime X_ne_zero h)
  exact ⟨hX, IsLocalization.map_units (Localization.AtPrime p) (⟨X, hX⟩ : p.primeCompl)⟩

/-- A principal prime generated by a nonzero element of `Λ` has height one (Krull's principal
ideal theorem; `Λ` is Noetherian). -/
theorem height_span_eq_one {x : Lam} (hxp : (Ideal.span {x}).IsPrime) (hx0 : x ≠ 0) :
    (Ideal.span {x}).height = 1 := by
  refine le_antisymm ?_ (Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero hx0))
  exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {x}) _
    ⟨⟨hxp, le_rfl⟩, fun _ hq _ => hq.2⟩

/-- **Non-vacuity: the quadratic specializations `(t)` and `(t+2)` are height-one primes
`≠ (2)`, and at `(t+2)` both `2` and `t` are units** (tex L3755–3760, "In particular `(t+2)` is
treated by the inertia contraction"; L5190–5191 "including both quadratic specializations").
So `ActiveInertiaUnit` and `MovingInertiaUnit` apply at `(t+2)`, and `ActiveInertiaUnit` at
`(t)`. PROVED. -/
def QuadraticPrimesHeightOne : Prop :=
  letI : (Ideal.span {(X + 2 : Lam)}).IsPrime := span_X_add_two_isPrime;
  (Ideal.span {(X : Lam)}).height = 1 ∧ (Ideal.span {(X + 2 : Lam)}).height = 1 ∧
    Ideal.span {(X : Lam)} ≠ Ideal.span {(2 : Lam)} ∧
    Ideal.span {(X + 2 : Lam)} ≠ Ideal.span {(2 : Lam)} ∧
    IsUnit (algebraMap Lam (Localization.AtPrime (Ideal.span {(X + 2 : Lam)})) 2) ∧
      IsUnit (algebraMap Lam (Localization.AtPrime (Ideal.span {(X + 2 : Lam)})) X)

theorem quadraticPrimesHeightOne_proof : QuadraticPrimesHeightOne := by
  obtain ⟨_, _, _, _, _, _, hX2, hY2, hYX⟩ := lamPrimes_proof
  have hX1 := height_span_eq_one span_X_isPrime X_ne_zero
  have hY1 := height_span_eq_one span_X_add_two_isPrime X_add_two_ne_zero
  refine ⟨hX1, hY1, hX2, hY2, ?_, ?_⟩
  · exact (activeInertiaUnit_proof _ hY1 hY2).2.1
  · exact (movingInertiaUnit_proof _ hY1 hYX).2

/-- **At `(t)`: nonzero central values are units** (tex L3758–3760: "at `(t)` the nonzero central
Frobenius determinants give integral adjugate contractions"; L5186–5187: "the central Frobenius
determinants are nonzero and hence units in `R`"). An element of `Λ` whose constant coefficient
(its value at `t = 0`) is nonzero is a unit of `Λ_(t)`; so a square matrix over `Λ` whose
determinant has nonzero constant coefficient becomes invertible over `Λ_(t)`, and its inverse
`det⁻¹ · adj` is integral there. PROVED. -/
def CentralDeterminantUnit : Prop :=
  letI : (Ideal.span {(X : Lam)}).IsPrime := span_X_isPrime;
    (∀ f : Lam, constantCoeff f ≠ 0 →
      IsUnit (algebraMap Lam (Localization.AtPrime (Ideal.span {(X : Lam)})) f)) ∧
    ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) Lam), constantCoeff M.det ≠ 0 →
      IsUnit (M.map (algebraMap Lam (Localization.AtPrime (Ideal.span {(X : Lam)}))))

theorem centralDeterminantUnit_proof : CentralDeterminantUnit := by
  let : (Ideal.span {(X : Lam)}).IsPrime := span_X_isPrime
  have hf : ∀ f : Lam, constantCoeff f ≠ 0 →
      IsUnit (algebraMap Lam (Localization.AtPrime (Ideal.span {(X : Lam)})) f) := by
    intro f hf
    have hfX : f ∉ Ideal.span {(X : Lam)} := by
      rw [Ideal.mem_span_singleton, X_dvd_iff]; exact hf
    exact IsLocalization.map_units (Localization.AtPrime (Ideal.span {(X : Lam)}))
      (⟨f, hfX⟩ : (Ideal.span {(X : Lam)}).primeCompl)
  refine ⟨hf, fun n M hM => ?_⟩
  rw [Matrix.isUnit_iff_isUnit_det]
  have h := RingHom.map_det (algebraMap Lam (Localization.AtPrime (Ideal.span {(X : Lam)}))) M
  rw [RingHom.mapMatrix_apply] at h
  rw [← h]
  exact hf _ hM

/-- **Residual Frobenius determinants are not in `(2)`** (tex L3730–3731: "the residual active
Frobenius is `(1+t)^a I` with `a` odd. Thus `A, D` are invertible over `𝒪[G]`"). For odd `a` and
odd `q`, `(1+t)^a − q ∉ (2)`; this covers `A = Φ − 1` (`q = 1`) and the augmentation `Φ − q` of
`D = Φ − N_q(g)` (tex L3472–3474, `N_q(1) = q`). Hence the determinant `((1+t)^a − q)^n` of the
scalar matrix `((1+t)^a − q) · 1ₙ` is not in `(2)`. (Its image in `𝒪 = (Λ_(2))^` is then a
unit by the determinant lane's `𝒪`-model lemma, and the matrices over `𝒪[G]` with that
augmentation are invertible by its augmentation criterion.) PROVED. -/
def ResidualFrobeniusNotInTwo : Prop :=
  ∀ a q : ℕ, Odd a → Odd q →
    ((1 + X : Lam) ^ a - q ∉ Ideal.span {(2 : Lam)}) ∧
    ∀ n : ℕ, (((1 + X : Lam) ^ a - q) • (1 : Matrix (Fin n) (Fin n) Lam)).det ∉
      Ideal.span {(2 : Lam)}

theorem residualFrobeniusNotInTwo_proof : ResidualFrobeniusNotInTwo := by
  intro a q ha hq
  have h1 : (1 + X : Lam) ^ a - q ∉ Ideal.span {(2 : Lam)} := by
    refine not_mem_span_two_of_coeff_one ha ?_
    rw [map_sub, coeff_one_one_add_X_pow, ← map_natCast (C (R := ℤ_[2])), coeff_C]
    simp
  refine ⟨h1, fun n => ?_⟩
  rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  intro h
  exact h1 (span_two_isPrime.mem_of_pow_mem n h)

end ZInQ.Contrib.CloudB3RC53.PairedFunctional

import ZInQKernel.Contrib.OneProof.RC.Adelic.Patch
import ZInQKernel.Contrib.OneProof.RC.LocalWeights.Product

/-! Appendix F's scalar phase and its multiplicative extension. -/

noncomputable section

namespace ZInQ.Manuscript.RC.ThetaJoin

open Adelic

variable {O : Type} [CommRing O]

/-- A finite set of exceptional places with its local scalar characters.
The same characters must be used to scale the local Schwartz factors. -/
structure PhaseData (O : Type) [CommRing O] where
  places : Finset Prime
  alpha : (q : Prime) → ℤ_[q.val]ˣ →* Oˣ
  exponent : ℕ
  alpha_order : ∀ q ∈ places, ∀ v, alpha q v ^ (2 ^ exponent : ℕ) = 1

namespace PhaseData

variable (A : PhaseData O)

/-- The exceptional places as a finite set of natural primes. -/
def support : Finset ℕ := A.places.map ⟨Subtype.val, Subtype.val_injective⟩

theorem mem_support (q : Prime) : q.val ∈ A.support ↔ q ∈ A.places := by
  simp [support]

/-- Positive integers prime to the exceptional set (or any integer coprime to it
that can be represented by a natural number). -/
def Away (n : ℕ) : Prop := ∀ q ∈ A.places, ¬ q.val ∣ n

/-- A natural number as a unit in a local integer ring. -/
def natUnit (q : Prime) (n : ℕ) (hn : ¬ q.val ∣ n) : ℤ_[q.val]ˣ :=
  (nat_isUnit q hn).unit

@[simp] theorem natUnit_val (q : Prime) (n : ℕ) (hn : ¬ q.val ∣ n) :
    ((natUnit q n hn : ℤ_[q.val]ˣ) : ℤ_[q.val]) = n :=
  (nat_isUnit q hn).unit_spec

private theorem away_mul (x y : ℕ) : A.Away (x * y) ↔ A.Away x ∧ A.Away y := by
  simp only [Away]
  constructor
  · intro h
    exact ⟨fun q hq hx => h q hq (dvd_mul_of_dvd_left hx y),
      fun q hq hy => h q hq (dvd_mul_of_dvd_right hy x)⟩
  · rintro ⟨hx, hy⟩ q hq hxy
    exact (q.prop.dvd_mul.mp hxy).elim (hx q hq) (hy q hq)

private theorem away_one : A.Away 1 :=
  fun q _ => q.prop.not_dvd_one

theorem away_of_not_mem (q : Prime) (hq : q.val ∉ A.support) : A.Away q.val := by
  intro r hr hd
  have he : r = q := Subtype.ext ((Nat.prime_dvd_prime_iff_eq r.prop q.prop).mp hd)
  exact hq ((A.mem_support q).mpr (he ▸ hr))

/-- The product of the local scalar multipliers at a unit integer. -/
def scalar (n : ℕ) (hn : A.Away n) : Oˣ :=
  ∏ q ∈ A.places.attach, A.alpha q.val (natUnit q.val n (hn q.val q.prop))

theorem scalar_mul {x y : ℕ} (hx : A.Away x) (hy : A.Away y) :
    A.scalar (x * y) ((A.away_mul x y).mpr ⟨hx, hy⟩) = A.scalar x hx * A.scalar y hy := by
  unfold scalar
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro q _
  rw [← map_mul]
  congr 1
  apply Units.ext
  simp

theorem scalar_order {n : ℕ} (hn : A.Away n) :
    A.scalar n hn ^ (2 ^ A.exponent : ℕ) = 1 := by
  classical
  unfold scalar
  rw [← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro q _
  exact A.alpha_order q.val q.prop _

/-- On the good set this is the inverse-idele convention for `η_B`: the
product of the local characters evaluated at the positive integer. -/
def phase (n : ℕ) : Oˣ :=
  open Classical in
  if hn : A.Away n then A.scalar n hn else 1

theorem phase_good (q : Prime) (hq : q.val ∉ A.support) :
    A.phase q.val = A.scalar q.val (A.away_of_not_mem q hq) := by
  classical
  exact dite_eq_left (A.away_of_not_mem q hq)

/-- The `sUnit` law, with the scalar inverse taken in the coefficient units. -/
theorem phase_unit (n : ℕ) : (A.phase n : O) * ((A.phase n)⁻¹ : Oˣ) = 1 :=
  (A.phase n).val_inv

/-- The `sOrder` law at every good prime. -/
theorem phase_order (q : Prime) (hq : q.val ∉ A.support) :
    (A.phase q.val : O) ^ (2 ^ A.exponent : ℕ) = 1 := by
  rw [A.phase_good q hq, ← Units.val_pow_eq_pow_val, A.scalar_order, Units.val_one]

/-- The imprimitive multiplicative extension from integers prime to the exceptional set. -/
def eta (m n : ℕ) : O :=
  open Classical in
  if A.Away n then (A.phase n : O) * (jacobiSym (-(m : ℤ)) n : O) else 0

theorem eta_one (m : ℕ) : A.eta m 1 = 1 := by
  classical
  have h := A.away_one
  simp [eta, phase, h, scalar, show ∀ q : Prime, ∀ h, natUnit q 1 h = 1 from
    fun q h => Units.ext (by simp), jacobiSym.one_right]

/-- The `ηMul` law. A nonempty exceptional set excludes zero. -/
theorem eta_mul (hne : A.places.Nonempty) (m x y : ℕ) :
    A.eta m (x * y) = A.eta m x * A.eta m y := by
  classical
  have hnz : ∀ n, A.Away n → n ≠ 0 := by
    rintro n hn rfl
    obtain ⟨q, hq⟩ := hne
    exact hn q hq (dvd_zero _)
  by_cases hx : A.Away x <;> by_cases hy : A.Away y
  · have hxy := (A.away_mul x y).mpr ⟨hx, hy⟩
    simp only [eta, phase, hxy, hx, hy, ite_true, dite_true]
    rw [A.scalar_mul hx hy, Units.val_mul, jacobiSym.mul_right' _ (hnz _ hx) (hnz _ hy),
      Int.cast_mul]
    ring
  · simp [eta, A.away_mul, hx, hy]
  · simp [eta, A.away_mul, hx, hy]
  · simp [eta, A.away_mul, hx, hy]

/-- The required `ηGood` value follows from the chosen inverse-idele convention. -/
theorem eta_good (m : ℕ) (q : Prime) (hq : q.val ∉ A.support) :
    A.eta m q.val = (A.phase q.val : O) * (jacobiSym (-(m : ℤ)) q.val : O) := by
  classical
  exact ite_eq_left (A.away_of_not_mem q hq)

/-- The sign of the scalar phase at minus one, before multiplying by the
odd fundamental discriminant character. -/
def scalarSign : Oˣ :=
  ∏ q ∈ A.places, A.alpha q (-1)

theorem scalarSign_sq : A.scalarSign * A.scalarSign = 1 := by
  classical
  unfold scalarSign
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro q _
  rw [← map_mul]
  have h : (-1 : ℤ_[q.val]ˣ) * (-1) = 1 := Units.ext (by simp)
  rw [h, map_one]

/-- The choice in (O.11). The negative discriminant character supplies an
extra minus sign; adjust by the odd dyadic sign only when necessary. -/
def unaryParity : Fin 2 :=
  open Classical in
  if (A.scalarSign : O) = 1 then 0 else 1

theorem unaryParity_odd [IsDomain O] :
    (A.scalarSign : O) * (-1) * (-1) ^ A.unaryParity.val = -1 := by
  classical
  have hh : (A.scalarSign : O) * (A.scalarSign : O) = 1 := by
    simpa only [Units.val_mul, Units.val_one] using
      congrArg (fun u : Oˣ => (u : O)) A.scalarSign_sq
  have hz : ((A.scalarSign : O) - 1) * ((A.scalarSign : O) + 1) = 0 := by
    linear_combination hh
  rcases mul_eq_zero.mp hz with hp | hn
  · have he := sub_eq_zero.mp hp
    simp [unaryParity, he]
  · have he := eq_neg_of_add_eq_zero_left hn
    have hem : (A.scalarSign : O) = -1 := he
    by_cases ho : (A.scalarSign : O) = 1
    · simp [unaryParity, ho]
    · rw [unaryParity, ite_eq_right ho, hem]
      simp

end PhaseData
end ZInQ.Manuscript.RC.ThetaJoin

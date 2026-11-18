import ZInQKernel.Contrib.OneProof.RC.AppF.Stage
import ZInQKernel.Contrib.OneProof.RC.Visibility.Theta

/-! Coefficients of the characteristic-zero lift of (O.4), and the integer divisions
(O.9)–(O.11) for the full-two-torsion case. The Brandt eigenrelation is used only at
precision `2^M`. -/

noncomputable section

open Finset QuaternionAlgebra
open scoped Quaternion
set_option maxHeartbeats 800000
namespace ZInQ.Manuscript.RC.ThetaCoeff

open ZInQ.Manuscript.RC.Odd
variable {O : Type} [CommRing O] {M : ℕ}

abbrev stageReduction (O : Type) [CommRing O] (M : ℕ) : O →+* StageRing O M :=
  Ideal.Quotient.mk (Ideal.span {(2 : O) ^ M})

/-- The actual weights and integral lifts of (O.3)–(O.4) and their identification with the
same stage's finite-precision sums (tex 8476–8494, 8496–8621). -/
structure Lift (S : AppF.ThetaStage (StageRing O M)) where
  geom : Visibility.ThetaStage O S.qa S.qb
  classes : geom.X ≃ S.X
  mass : ∀ z, Nat.card (geom.G z) = S.w (classes z)
  P : ∀ z, stageReduction O M (geom.P z : O) = S.P (classes z)
  normChar : ∀ z, stageReduction O M (geom.χN z) = S.χN (classes z)
  localSum : ∀ z (n : ℕ), stageReduction O M
    (∑ᶠ x ∈ {x : ℍ[ℚ,S.qa,0,S.qb] | x.re = 0 ∧ Visibility.nrd x = (n : ℚ)}, geom.f z x)
      = S.θ (classes z) n
  η : ℕ → O
  phase : ∀ n, stageReduction O M (η n) = S.η n
  /-- Exponent of the parity adjustment in (O.11), chosen so the unary character is odd. -/
  parity : Fin 2

variable {S : AppF.ThetaStage (StageRing O M)}

def Lift.H (L : Lift S) (n : ℕ) : O := Visibility.thetaCoeff L.geom n

def Lift.aθ (L : Lift S) (n : ℕ) : O := L.H (S.m * n)

theorem Lift.H_reduce (L : Lift S) (n : ℕ) :
    stageReduction O M (L.H n) = S.H n := by
  unfold Lift.H Visibility.thetaCoeff AppF.ThetaStage.H
  rw [map_sum, ← Equiv.sum_comp L.classes]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [map_mul, map_mul, map_mul, map_natCast, L.mass, L.P, L.normChar, L.localSum]
  ring

theorem Lift.aθ_reduce (L : Lift S) (n : ℕ) :
    stageReduction O M (L.aθ n) = S.aθ n := L.H_reduce _

private theorem lift_dvd {k : ℕ} {x : O} (hk : k ≤ M)
    (h : (2 : StageRing O M) ^ k ∣ stageReduction O M x) : (2 : O) ^ k ∣ x := by
  obtain ⟨y, hy⟩ := h
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  have he : stageReduction O M (x - (2 : O) ^ k * z) = 0 := by
    rw [map_sub, map_mul, map_pow, map_ofNat, hy, sub_self]
  have hm := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp he)
  simpa using dvd_add (two_pow_dvd_of_le hk hm) (dvd_mul_right ((2 : O) ^ k) z)

variable (L : Lift S)

/-- Input at one actual stage: the integral support (including any exact sieve) and the
finite-precision depth of App G. The finite-precision source is the Brandt source of `S`. -/
structure Divisions (δ : ℤ) (W R : ℕ) (adm : ℕ → Prop) : Prop where
  stage : OddStageSource O W R M δ S.η S.Good adm S.ap S.aθ
  precision : 2 ≤ R
  zero : L.aθ 0 = 0
  support : ∀ p, p.Prime → ¬ S.Good p → ∀ n, p ∣ n → L.aθ n = 0

/-- The theta exponents allowed by the actual stage, with zero extension performed later. -/
def Admissible (S : AppF.ThetaStage (StageRing O M)) (W : ℕ) (U : Finset ℕ) : Prop :=
  U.card ≤ W ∧ ∀ p ∈ U, S.Good p

def nU (δ : ℤ) (U : Finset ℕ) : ℤ := δ + U.card

def Lift.raw (U : Finset ℕ) : ℕ → O := TL L.η (U.sort (· ≤ ·)) L.aθ

private theorem TL_reduce (U : List ℕ) (n : ℕ) :
    stageReduction O M (TL L.η U L.aθ n) = TL S.η U S.aθ n := by
  induction U generalizing n with
  | nil => exact L.aθ_reduce n
  | cons p U ih =>
    simp only [TL_cons, Odd.Top, map_sub, map_mul, L.phase, ih, ← divCoeff_map]

private theorem TL_support {b : ℕ → O} {η : ℕ → O} {p : ℕ}
    (hp : p.Prime) (L : List ℕ) (hL : ∀ q ∈ L, q.Prime ∧ q ≠ p)
    (hb : ∀ n, p ∣ n → b n = 0) : ∀ n, p ∣ n → TL η L b n = 0 := by
  induction L with
  | nil => exact hb
  | cons q L ih =>
    have hq := hL q (by simp)
    have hqp : ¬ p ∣ q := fun h => hq.2 ((Nat.prime_dvd_prime_iff_eq hp hq.1).1 h).symm
    have ht := ih (fun k hk => hL k (by simp [hk]))
    intro n hn
    rw [TL_cons, Odd.Top, ht _ (dvd_mul_of_dvd_right hn _)]
    unfold divCoeff
    split_ifs with hd
    · have he := Nat.mul_div_cancel' hd
      have hpn : p ∣ q * (n / q) := by rw [he]; exact hn
      rw [ht _ ((hp.dvd_mul.mp hpn).resolve_left hqp)]
      simp
    · simp

variable {δ : ℤ} {W R : ℕ} {adm : ℕ → Prop} {U : Finset ℕ}

private theorem exponent_le (h : Divisions L δ W R adm) (hu : Admissible S W U) :
    (nU δ U + 1).toNat ≤ M := by
  have := h.stage.1
  have := h.precision
  have := hu.1
  have := budgetLevel_cast δ W R
  unfold nU
  omega

theorem raw_dvd (h : Divisions L δ W R adm) (hu : Admissible S W U) (n : ℕ) :
    (2 : O) ^ (nU δ U).toNat ∣ L.raw U n := by
  refine lift_dvd (le_trans (show (nU δ U).toNat ≤ (nU δ U + 1).toNat by omega)
    (exponent_le L h hu)) ?_
  rw [Lift.raw, TL_reduce]
  have hd := O9_odd_stage h.stage (U.sort (· ≤ ·)) (Finset.sort_nodup _ _)
    (fun p hp => hu.2 p (by simpa using hp)) (by simpa using hu.1) n
  simp only [Finset.length_sort, Finset.sort_toFinset] at hd
  exact two_pow_dvd_of_le (by unfold nU; omega) hd

private theorem raw_off (h : Divisions L δ W R adm) (hu : Admissible S W U)
    {n : ℕ} (hn : ¬ oddPart n ⊆ U) :
    (2 : O) ^ (nU δ U + 1).toNat ∣ L.raw U n := by
  apply lift_dvd (exponent_le L h hu)
  rw [Lift.raw, TL_reduce]
  have hd := O11_offJ h.stage.2 (U.sort (· ≤ ·)) (Finset.sort_nodup _ _)
    (fun p hp => hu.2 p (by simpa using hp)) (by simpa using hn)
  have := budgetLevel_cast δ W R
  have := hu.1
  have := h.precision
  simpa [nU, min_eq_right (show δ + (U.card : ℤ) + 1 ≤ (budgetLevel δ W R : ℤ) by omega)] using hd

/-- `χ_{-4}(k)^i k` on positive odd `k`, written with the Jacobi symbol. -/
def unaryWeight (i : Fin 2) (k : ℕ) : ℤ := jacobiSym (-1) k ^ i.val * k

private theorem unaryWeight_odd (i : Fin 2) (k : ℕ) (hk : Odd k) : Odd (unaryWeight i k) := by
  have h : Int.gcd (-1) (k : ℤ) = 1 := by simp [Int.gcd]
  rcases jacobiSym.eq_one_or_neg_one h with he | he
  · simpa [unaryWeight, he] using (show Odd (k : ℤ) by exact_mod_cast hk)
  · have ho : Odd (-1 : ℤ) := by decide
    simpa only [unaryWeight, he] using (ho.pow.mul (show Odd (k : ℤ) by exact_mod_cast hk))

private theorem raw_shell (h : Divisions L δ W R adm) (hu : Admissible S W U)
    {j k : ℕ} (hj : j ≠ 0) (hk : k ≠ 0) (hodd : Odd k) (hJ : oddPart j ⊆ U)
    (hs : ∀ p ∈ k.primeFactors, S.Good p) :
    (2 : O) ^ (nU δ U + 1).toNat ∣
      L.raw U (j * k ^ 2) - L.raw U j * (L.η k * (unaryWeight L.parity k : O)) := by
  apply lift_dvd (exponent_le L h hu)
  simpa only [Lift.raw, map_sub, map_mul, map_intCast, L.phase, TL_reduce, nU, Finset.length_sort] using
    O11_odd_stage h.stage (by have := h.precision; omega) (U.sort (· ≤ ·)) (Finset.sort_nodup _ _)
      (fun p hp => hu.2 p (by simpa using hp)) (by simpa using hu.1)
      (unaryWeight L.parity) (unaryWeight_odd L.parity) hj hk hodd (by simpa using hJ) hs

/-- The positive squarefree products of subsets, including the empty product. -/
def subscripts (U : Finset ℕ) : Finset ℕ := U.powerset.image fun J => ∏ p ∈ J, p

theorem mem_subscripts (hU : ∀ p ∈ U, p.Prime) (j : ℕ) :
    j ∈ subscripts U ↔ Squarefree j ∧ j.primeFactors ⊆ U := by
  simp only [subscripts, Finset.mem_image, Finset.mem_powerset]
  constructor
  · rintro ⟨J, hJ, rfl⟩
    have hp : ∀ p ∈ J, p.Prime := fun p hp => hU p (hJ hp)
    exact ⟨Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp₁ q hq hpq => (Nat.coprime_primes (hp p hp₁) (hp q hq)).mpr hpq |> Nat.coprime_iff_isRelPrime.mp) (fun p hp₁ => (hp p hp₁).squarefree), (Nat.primeFactors_prod hp).symm ▸ hJ⟩
  · rintro ⟨hs, hJ⟩
    exact ⟨j.primeFactors, hJ, Nat.prod_primeFactors_of_squarefree hs⟩

/-- The expansion of `Θ_j` in (O.11), with the actual coprimality sieve. -/
def Lift.unary (j n : ℕ) : O := by
  classical
  exact if h : ∃ k : ℕ, k ≠ 0 ∧ (∀ p ∈ k.primeFactors, S.Good p) ∧ n = j * k ^ 2
    then L.η h.choose * (unaryWeight L.parity h.choose : O)
  else 0

theorem Lift.unary_off {j n : ℕ} (hn : ∀ k : ℕ, n ≠ j * k ^ 2) : L.unary j n = 0 := by
  rw [Lift.unary, dite_eq_right]
  rintro ⟨k, _, _, h⟩
  exact hn k h

private theorem unary_shell {j k : ℕ} (hj : 0 < j) (hk : k ≠ 0)
    (hs : ∀ p ∈ k.primeFactors, S.Good p) :
    L.unary j (j * k ^ 2) = L.η k * (unaryWeight L.parity k : O) := by
  have h : ∃ t : ℕ, t ≠ 0 ∧ (∀ p ∈ t.primeFactors, S.Good p) ∧ j * k ^ 2 = j * t ^ 2 :=
    ⟨k, hk, hs, rfl⟩
  rw [Lift.unary, dite_eq_left h]
  have he : k = h.choose := Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0)
    (Nat.eq_of_mul_eq_mul_left hj h.choose_spec.2.2)
  rw [← he]

variable [IsDomain O] [CharZero O]

private def divide {d x : O} (h : d ∣ x) : O := h.choose

private theorem mul_divide {d x : O} (h : d ∣ x) : d * divide h = x := h.choose_spec.symm

/-- The manuscript's `2^{-n_U}`, also when the integer `n_U` is negative. -/
def Lift.B (h : Divisions L δ W R adm) (hu : Admissible S W U) (n : ℕ) : O :=
  2 ^ (-(nU δ U)).toNat * divide (raw_dvd L h hu n)

theorem B_spec (h : Divisions L δ W R adm) (hu : Admissible S W U) (n : ℕ) :
    2 ^ (nU δ U).toNat * L.B h hu n = 2 ^ (-(nU δ U)).toNat * L.raw U n := by
  simp only [Lift.B]
  rw [mul_left_comm, mul_divide]

private theorem B_bad (h : Divisions L δ W R adm) (hu : Admissible S W U)
    {p n : ℕ} (hp : p.Prime) (hbad : ¬ S.Good p) (hn : p ∣ n) : L.B h hu n = 0 := by
  have he : L.raw U n = 0 := TL_support hp _ (fun q hq =>
    have hq' := hu.2 q (by simpa using hq)
    ⟨S.good_prime q hq', fun e => hbad (e ▸ hq')⟩) (h.support p hp hbad) n hn
  exact (mul_eq_zero.mp (by rw [B_spec, he, mul_zero] :
    2 ^ (nU δ U).toNat * L.B h hu n = 0)).resolve_left (pow_ne_zero _ (by norm_num))

private theorem div_two_of_raw (h : Divisions L δ W R adm) (hu : Admissible S W U)
    (n j : ℕ) (z : O)
    (hd : (2 : O) ^ (nU δ U + 1).toNat ∣ L.raw U n - L.raw U j * z) :
    (2 : O) ∣ L.B h hu n - L.B h hu j * z := by
  by_cases he : 0 ≤ nU δ U
  · have he₁ : (-(nU δ U)).toNat = 0 := by omega
    have he₂ : (nU δ U + 1).toNat = (nU δ U).toNat + 1 := by omega
    have eq : (2 : O) ^ (nU δ U).toNat * (L.B h hu n - L.B h hu j * z) =
        L.raw U n - L.raw U j * z := by
      rw [mul_sub, ← mul_assoc, B_spec, B_spec, he₁, pow_zero, one_mul, one_mul]
    rw [← eq, he₂, pow_succ] at hd
    exact (mul_dvd_mul_iff_left (pow_ne_zero _ (by norm_num))).mp hd
  · have hk : 1 ≤ (-(nU δ U)).toNat := by omega
    simp only [Lift.B]
    rw [mul_assoc, ← mul_sub]
    exact dvd_mul_of_dvd_left (by simpa using (pow_dvd_pow (2 : O) hk)) _

private theorem B_off (h : Divisions L δ W R adm) (hu : Admissible S W U)
    {n : ℕ} (hn : ¬ oddPart n ⊆ U) : (2 : O) ∣ L.B h hu n := by
  simpa using div_two_of_raw L h hu n n 0 (by simpa using raw_off L h hu hn)

private theorem sum_unary_off (h : Divisions L δ W R adm) (hu : Admissible S W U)
    {n : ℕ} (hn : ¬ oddPart n ⊆ U) : ∑ j ∈ subscripts U, L.B h hu j * L.unary j n = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  rw [Lift.unary, dite_eq_right, mul_zero]
  rintro ⟨k, hk, _, rfl⟩
  obtain ⟨hj, hjU⟩ := (mem_subscripts (fun p hp => S.good_prime p (hu.2 p hp)) j).mp hj
  exact hn (by simpa [oddPart_mul_sq hj.ne_zero hk, oddPart_of_squarefree hj])

/-- (O.11), including nonshell indices and the sieve, is an exact division by integer two. -/
theorem Hnum_dvd (h : Divisions L δ W R adm) (hu : Admissible S W U) (n : ℕ) :
    (2 : O) ∣ L.B h hu n - ∑ j ∈ subscripts U, L.B h hu j * L.unary j n := by
  have hmem := mem_subscripts (fun p hp => S.good_prime p (hu.2 p hp))
  rcases eq_or_ne n 0 with rfl | hn
  · have hb : L.raw U 0 = 0 := by
      unfold Lift.raw
      induction (U.sort (· ≤ ·)) with
      | nil => exact h.zero
      | cons p V ih => simp [TL_cons, Odd.Top, divCoeff, ih]
    have hz : L.B h hu 0 = 0 :=
      (mul_eq_zero.mp (by rw [B_spec, hb, mul_zero] :
        2 ^ (nU δ U).toNat * L.B h hu 0 = 0)).resolve_left (pow_ne_zero _ (by norm_num))
    rw [hz, Finset.sum_eq_zero]
    · simp
    · intro j hj
      rw [Lift.unary, dite_eq_right, mul_zero]
      rintro ⟨k, hk, _, he⟩
      exact (mul_ne_zero ((hmem j).mp hj).1.ne_zero (pow_ne_zero _ hk)) he.symm
  by_cases hJ : oddPart n ⊆ U
  · obtain ⟨k, j, he, hj⟩ := exists_sq_mul_squarefree n
    rw [mul_comm] at he
    have hk : k ≠ 0 := by rintro rfl; simp at he; exact hn he.symm
    have hs : oddPart n = j.primeFactors := by
      rw [← he, oddPart_mul_sq hj.ne_zero hk, oddPart_of_squarefree hj]
    have hjU : j ∈ subscripts U := (hmem j).mpr ⟨hj, hs ▸ hJ⟩
    rw [Finset.sum_eq_single j]
    · by_cases hgood : ∀ p ∈ k.primeFactors, S.Good p
      · have hodd : Odd k := by
          rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
          intro hd
          exact S.good_ne_two _ (hgood 2 (Nat.mem_primeFactors.mpr ⟨Nat.prime_two, hd, hk⟩)) rfl
        rw [← he, unary_shell L (Nat.pos_of_ne_zero hj.ne_zero) hk hgood]
        exact div_two_of_raw L h hu _ _ _ (raw_shell L h hu hj.ne_zero hk hodd
          (by rwa [oddPart_of_squarefree hj, ← hs]) hgood)
      · have hb' := hgood
        push Not at hb'
        obtain ⟨p, hp, hb⟩ := hb'
        have hpk := Nat.mem_primeFactors.mp hp
        rw [B_bad L h hu hpk.1 (by simpa using hb) (he ▸ dvd_mul_of_dvd_right
          (dvd_pow hpk.2.1 (by decide : (2 : ℕ) ≠ 0)) j), Lift.unary, dite_eq_right]
        · simp
        · rintro ⟨t, _, ht, ht'⟩
          have e : k = t := Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0)
            (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hj.ne_zero) (he.trans ht'))
          exact hgood (e ▸ ht)
    · intro l hl hlj
      rw [Lift.unary, dite_eq_right, mul_zero]
      rintro ⟨t, ht, _, ht'⟩
      have hl' := ((hmem l).mp hl).1
      have : oddPart n = l.primeFactors := by
        rw [ht', oddPart_mul_sq hl'.ne_zero ht, oddPart_of_squarefree hl']
      apply hlj
      rw [← Nat.prod_primeFactors_of_squarefree hl', ← Nat.prod_primeFactors_of_squarefree hj,
        ← this, hs]
    · exact fun h => (h hjU).elim
  · rw [sum_unary_off L h hu hJ, sub_zero]
    exact B_off L h hu hJ

def Lift.HU (h : Divisions L δ W R adm) (hu : Admissible S W U) (n : ℕ) : O :=
  divide (Hnum_dvd L h hu n)

theorem HU_spec (h : Divisions L δ W R adm) (hu : Admissible S W U) (n : ℕ) :
    2 * L.HU h hu n = L.B h hu n - ∑ j ∈ subscripts U, L.B h hu j * L.unary j n :=
  mul_divide _

/-- Multiplication of an expansion by `1 + 2 ∑_{k>0} q^{k²}` (tex 9647–9648). -/
def timesTheta (f : ℕ → O) (n : ℕ) : O :=
  f n + 2 * ∑ k ∈ (Finset.Icc 1 n).filter (fun k => k ^ 2 ≤ n), f (n - k ^ 2)

def Lift.FourierF (h : Divisions L δ W R adm) (hu : Admissible S W U) : ℕ → O :=
  timesTheta (L.HU h hu)

def Lift.FourierB (h : Divisions L δ W R adm) (hu : Admissible S W U) : ℕ → O :=
  timesTheta (L.B h hu)

def Lift.FourierUnary (j : ℕ) : ℕ → O := timesTheta (L.unary j)

#print axioms Lift.H_reduce
#print axioms Lift.aθ_reduce
#print axioms lift_dvd
#print axioms TL_reduce
#print axioms TL_support
#print axioms exponent_le
#print axioms raw_dvd
#print axioms raw_off
#print axioms unaryWeight_odd
#print axioms raw_shell
#print axioms mem_subscripts
#print axioms Lift.unary_off
#print axioms unary_shell
#print axioms mul_divide
#print axioms B_spec
#print axioms B_bad
#print axioms div_two_of_raw
#print axioms B_off
#print axioms sum_unary_off
#print axioms Hnum_dvd
#print axioms HU_spec

end ZInQ.Manuscript.RC.ThetaCoeff

import ZInQKernel.Contrib.OneProof.RC.O12.Fourier
import ZInQKernel.Contrib.OneProof.RC.Odd.DivisionsFinal

/-! The two Fourier readings of the same theta coefficient source, at one
fixed stage and within the budget (tex 9670–9704 and 9905–9918). -/

noncomputable section

namespace ZInQ.Manuscript.RC.O12

open AddressGenuine PrintsArith Symbols
open ZInQ.Manuscript.RC.Odd
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2}
variable {T : TypeData L ε} {R : Finset ℕ → ZMod 2} {ap : ℕ → ℤ} {B : ℕ}
variable {chiType : GalQ →* Multiplicative L}
variable {X : GaloisConstituentModel T R ap B chiType}

attribute [local instance] GaloisConstituentModel.modMexp

/-- The multiplier (2^{-n_U-1}) of the undivided coefficient in (K),
where (n_U = δ + |U|). Integer exponents allow a negative source depth. -/
def scale (K : Type) [Field K] (δ : ℤ) (U : Finset ℕ) : K :=
  (2 : K) ^ (-(δ + (U.card : ℤ) + 1))

/-- The source and Fourier comparisons at the actual stage. In
`H_off_unary`, the division happens in characteristic zero and has an
integral witness before reduction. The difference can be zero for the even
source; the stated divisibility is the odd-stage precision, tex 9699–9704,
9916–9918. The unary subtraction in (O.11) is absent at these indices.
`source_symbol` specifies the meaning of the model's valuation symbol. -/
structure ThetaData (A : FourierData X) where
  δ : ℤ
  truncation : ℕ
  admissible : ℕ → Prop
  a : ℕ → X.O
  η : ℕ → X.O
  ratio : ℕ → ℤ
  H : Finset ℕ → ℕ → X.O
  residue_maximal : X.m.IsMaximal
  source : SourceHyp truncation δ η T.Good admissible ap a
  ratio_sign : ∀ p, T.Good p → ratio p = 1 ∨ ratio p = -1
  signed_recur : ∀ p (hp : T.Good p), @RecAt X.O _ p ⟨hp.1⟩ (η p) (ratio p) (ap p) a
  eta_phase : ∀ p, T.Good p → ∃ k : ℕ, η p ^ (2 ^ k) = 1
  good_hecke : A.FormwiseHecke
  theta_mod_two : ∀ U : Finset ℕ, (∀ s ∈ U, T.Good s) → U.card + 1 ≤ B →
    ∀ n, n ≠ 0 → (2 : X.O) ∣ A.coeff n (X.F U) - H U n
  H_off_unary : ∀ U : Finset ℕ, (∀ s ∈ U, T.Good s) → U.card + 1 ≤ B →
    ∀ (J : List ℕ), J.Nodup → J.toFinset = U → ∀ n : ℕ, ¬ oddPart n ⊆ U →
    ∃ b : X.O, algebraMap X.O X.K b =
      scale X.K δ U * algebraMap X.O X.K (TL η J a n) ∧ (2 : X.O) ∣ H U n - b
  source_symbol : ∀ (U : Finset ℕ) (q : ℕ), (∀ s ∈ U, T.Good s) → T.Good q → q ∉ U →
    (insert q U).card ≤ B → ∀ b : X.O,
    algebraMap X.O X.K b =
      scale X.K δ U * algebraMap X.O X.K (a ((∏ s ∈ U, s) * q)) →
      Ideal.Quotient.mk X.m b = if R (insert q U) = 0 then 0 else 1

namespace ThetaData

variable {A : FourierData X} (S : ThetaData A)

private theorem residue_two : Ideal.Quotient.mk X.m (2 : X.O) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr X.two_mem

private theorem residue_eq_of_two_dvd {a b : X.O} (h : (2 : X.O) ∣ a - b) :
    Ideal.Quotient.mk X.m a = Ideal.Quotient.mk X.m b := by
  obtain ⟨c, hc⟩ := h
  rw [← sub_eq_zero, ← map_sub, hc, map_mul, residue_two, zero_mul]

private theorem no_div_of_fresh {U : Finset ℕ} {q : ℕ}
    (hU : ∀ s ∈ U, T.Good s) (hq : T.Good q) (hqU : q ∉ U) :
    ∀ s ∈ U, ¬ s ∣ q :=
  fun s hs hd => hqU ((Nat.prime_dvd_prime_iff_eq (hU s hs).1 hq.1).mp hd ▸ hs)

/-- The phase `η(p)` disappears in the coefficient residue field (tex
9696–9698, 9931). -/
theorem eta_residue {p : ℕ} (hp : T.Good p) : Ideal.Quotient.mk X.m (S.η p) = 1 := by
  let : X.m.IsPrime := S.residue_maximal.isPrime
  let z := Ideal.Quotient.mk X.m (S.η p)
  obtain ⟨k, hk⟩ := S.eta_phase p hp
  have hz : z ^ (2 ^ k : ℕ) = 1 := by
    dsimp [z]
    rw [← map_pow, hk, map_one]
  have htwo : (2 : X.O ⧸ X.m) = 0 := by simpa only [map_ofNat] using (residue_two (X := X))
  change z = 1
  clear hk
  induction k with
  | zero => simpa using hz
  | succ k ih =>
    apply ih
    have hs : (z ^ (2 ^ k : ℕ)) ^ 2 = 1 ^ 2 := by
      rw [← pow_mul, ← pow_succ, hz, one_pow]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h | h
    · exact h
    · rw [h]
      apply neg_eq_iff_add_eq_zero.mpr
      simpa only [← two_mul, mul_one] using htwo

/-- At a fresh prime the normalized source coefficient is the integral
`H_U[q]` up to an integer-two error (tex 9681–9687, 9699–9704). -/
theorem fresh_normalized {U : Finset ℕ} {q : ℕ} (hU : ∀ s ∈ U, T.Good s)
    (hq : T.Good q) (hqU : q ∉ U) (hB : U.card + 1 ≤ B) :
    ∃ b : X.O, algebraMap X.O X.K b =
      scale X.K S.δ U * algebraMap X.O X.K (S.a ((∏ s ∈ U, s) * q)) ∧
        (2 : X.O) ∣ S.H U q - b := by
  classical
  let J := U.toList
  have hmem (s : ℕ) : s ∈ J ↔ s ∈ U := Finset.mem_toList
  have h := TL_fresh S.η S.a J (fun s hs => (hU s ((hmem s).mp hs)).1)
    U.nodup_toList (n := q) (fun s hs => no_div_of_fresh hU hq hqU s ((hmem s).mp hs))
  rw [show J.prod = ∏ s ∈ U, s from Finset.prod_toList U] at h
  simpa only [h] using S.H_off_unary U hU hB J U.nodup_toList
    (Finset.toList_toFinset U) q (theta_index_ne_fresh hq.1 hqU)

/-- The good Hecke formula at coefficient one and `θ ≡ 1 (mod 2)`
give the residue of `H_U[q]` (tex 9688–9693). -/
theorem fresh_residue {U : Finset ℕ} {q : ℕ} (hU : ∀ s ∈ U, T.Good s)
    (hq : T.Good q) (hqU : q ∉ U) (hB : U.card + 1 ≤ B) :
    A.orbitCoeff U (X.frob q) ⟨1, one_ne_zero⟩ = Ideal.Quotient.mk X.m (S.H U q) := by
  have hf := A.trace_coeff_of_not_dvd S.good_hecke hU hq hqU hB (n := 1)
    (fun h => hq.1.ne_one (Nat.dvd_one.mp h))
  rw [A.orbitCoeff_eq, hf, mul_one]
  exact residue_eq_of_two_dvd (S.theta_mod_two U hU hB q hq.1.ne_zero)

include S in
/-- The first half of `GaloisConstituentModel.Inputs`, the reading at an
added vertex (tex 9670–9704). -/
theorem coefficientOne {U : Finset ℕ} {q : ℕ} (hU : ∀ s ∈ U, T.Good s)
    (hq : T.Good q) (hqU : q ∉ U) (hB : (insert q U).card ≤ B) :
    R (insert q U) = X.readE U (X.tE (X.frob q) (X.FE U)) := by
  classical
  have hb : U.card + 1 ≤ B := by simpa only [Finset.card_insert_of_notMem hqU] using hB
  obtain ⟨b, hbK, hb2⟩ := S.fresh_normalized hU hq hqU hb
  rw [A.read_orbit, S.fresh_residue hU hq hqU hb, residue_eq_of_two_dvd hb2,
    S.source_symbol U q hU hq hqU hB b hbK]
  generalize R (insert q U) = r
  have hr : r = 0 ∨ r = 1 := (show ∀ x : ZMod 2, x = 0 ∨ x = 1 by decide) r
  rcases hr with rfl | rfl <;> simp [A.decode_one]

/-- The signed Legendre character in the omission coefficient, tex 9905–9910. -/
def omissionSign (p : ℕ) [Fact p.Prime] (V : Finset ℕ) (r : ℕ) : ℤ :=
  S.ratio p * legendreSym p (-(((∏ s ∈ V, s) * r : ℕ) : ℤ))

include S in
private theorem even_ap {p : ℕ} (hp : T.Good p) : Even (ap p) := by
  have e := (S.source.ap_mod p hp).dvd
  have h := (S.source.odd p hp)
  rcases e with ⟨d, hd⟩
  rcases h with ⟨k, hk⟩
  exact ⟨k + 1 - 2 * d, by omega⟩

private theorem decode_int_mul (k : ℤ) (b : X.O ⧸ X.m) :
    A.decode ((k : X.O ⧸ X.m) * b) = (k : ZMod 2) * A.decode b := by
  simp only [← zsmul_eq_mul, map_zsmul]

private theorem scale_erase [CharZero X.K] {U : Finset ℕ} {p : ℕ} (hpU : p ∈ U) :
    scale X.K S.δ U * (2 : X.K) = scale X.K S.δ (U.erase p) := by
  classical
  have hc := Finset.card_erase_add_one hpU
  have he : -(S.δ + (U.card : ℤ) + 1) + 1 =
      -(S.δ + ((U.erase p).card : ℤ) + 1) := by omega
  calc
    _ = scale X.K S.δ U * (2 : X.K) ^ (1 : ℤ) := by rw [zpow_one]
    _ = _ := by
      unfold scale
      rw [← zpow_add₀ (by norm_num : (2 : X.K) ≠ 0), he]

/-- At index (p) the good trace at (r) reads the omission coefficient:
the residue is (c_p(vr)) times the coefficient-one reading on (V).
The returned sign is the actual Legendre sign, tex 9905–9918. -/
theorem omission_at_p [CharZero X.K] {U : Finset ℕ} {p r : ℕ} (hpU : p ∈ U)
    (hU : ∀ s ∈ U, T.Good s) (hr : T.Good r) (hrU : r ∉ U)
    (hB : U.card + 1 ≤ B) :
    letI : Fact p.Prime := ⟨(hU p hpU).1⟩
    let κ := S.omissionSign p (U.erase p) r
    (κ = 1 ∨ κ = -1) ∧
      A.decode (A.orbitCoeff U (X.frob r) ⟨p, (hU p hpU).1.ne_zero⟩) =
        (Cp (ap p) κ : ZMod 2) * X.readE (U.erase p) (X.tE (X.frob r) (X.FE (U.erase p))) := by
  classical
  let hp := hU p hpU
  let : Fact p.Prime := ⟨hp.1⟩
  let V := U.erase p
  let J := V.toList
  let κ := S.omissionSign p V r
  have hV : ∀ s ∈ V, T.Good s := fun s hs => hU s (Finset.mem_of_mem_erase hs)
  have hrV : r ∉ V := fun h => hrU (Finset.mem_of_mem_erase h)
  have hVB : V.card + 1 ≤ B :=
    (Nat.add_le_add_right (Finset.card_le_card (Finset.erase_subset p U)) 1).trans hB
  have hn (q : ℕ) (hq : q ∈ J) : ¬ q ∣ r :=
    no_div_of_fresh hV hr hrV q (Finset.mem_toList.mp hq)
  have hpr : ¬ p ∣ r := no_div_of_fresh hU hr hrU p hpU
  have hrp : ¬ r ∣ p := fun hd => hrU
    ((Nat.prime_dvd_prime_iff_eq hr.1 hp.1).mp hd ▸ hpU)
  have hprod : ¬ p ∣ J.prod := by
    intro hd
    obtain ⟨q, hq, hdq⟩ := (Prime.dvd_prod_iff hp.1.prime).mp hd
    have hqV : q ∈ V := Finset.mem_toList.mp hq
    exact (Finset.mem_erase.mp hqV).1
      ((Nat.prime_dvd_prime_iff_eq hp.1 (hV q hqV).1).mp hdq).symm
  have hκ : κ = 1 ∨ κ = -1 := by
    apply legendreSym_neg_eq_one_or (ε := S.ratio p) _ (S.ratio_sign p hp)
    rw [← Finset.prod_toList V]
    exact fun h => (hp.1.dvd_mul.mp h).elim hprod hpr
  have hCp : ap p - κ - 1 = 2 * Cp (ap p) κ := by
    have ha := S.even_ap hp
    obtain ⟨k, hk⟩ := ha
    rcases hκ with h | h <;> rw [h] <;> unfold Cp <;> omega
  have hOff : ¬ oddPart (p * r) ⊆ U := by
    rw [oddPart_mul_prime hp.1 hr.1.ne_zero hpr]
    exact fun h => theta_index_ne_fresh hr.1 hrU (fun s hs => h (Finset.mem_insert_of_mem hs))
  have hpJ : p ∉ J := fun h => Finset.notMem_erase p U (Finset.mem_toList.mp h)
  have hJ : (p :: J).Nodup := List.nodup_cons.mpr ⟨hpJ, V.nodup_toList⟩
  have hJU : (p :: J).toFinset = U := by
    rw [List.toFinset_cons, show J.toFinset = V from Finset.toList_toFinset V]
    exact Finset.insert_erase hpU
  have hTL := TL_omission S.η S.a (S.signed_recur p hp) J
    (fun q hq => (hV q (Finset.mem_toList.mp hq)).1) V.nodup_toList hpJ hpr hn
  rw [show J.prod = ∏ s ∈ V, s from Finset.prod_toList V] at hTL
  change TL S.η (p :: J) S.a (p * r) =
    S.η p * ((ap p - κ - 1 : ℤ) : X.O) * S.a ((∏ s ∈ V, s) * r) at hTL
  rw [hCp] at hTL
  obtain ⟨b, hbK, hb2⟩ := S.H_off_unary U hU hB (p :: J) hJ hJU _ hOff
  obtain ⟨c, hcK, hc2⟩ := S.fresh_normalized hV hr hrV hVB
  have hbc : b = S.η p * (Cp (ap p) κ : X.O) * c := by
    apply A.integral_inclusion
    rw [hbK, hTL, map_mul, map_mul, map_intCast, Int.cast_mul, Int.cast_ofNat,
      map_mul, map_mul, map_intCast, hcK, ← S.scale_erase hpU]
    ring
  have hb' : Ideal.Quotient.mk X.m b =
      (Cp (ap p) κ : X.O ⧸ X.m) * Ideal.Quotient.mk X.m c := by
    simp only [hbc, map_mul, S.eta_residue hp, one_mul, map_intCast]
  have ht := A.trace_coeff_of_not_dvd S.good_hecke hU hr hrU hB hrp
  refine ⟨hκ, ?_⟩
  rw [A.orbitCoeff_eq, ht, mul_comm r p,
    residue_eq_of_two_dvd (S.theta_mod_two U hU hB (p * r) (Nat.mul_ne_zero hp.1.ne_zero hr.1.ne_zero)),
    residue_eq_of_two_dvd hb2, hb', decode_int_mul, A.read_orbit, S.fresh_residue hV hr hrV hVB, residue_eq_of_two_dvd hc2]

#print axioms residue_two
#print axioms residue_eq_of_two_dvd
#print axioms no_div_of_fresh
#print axioms eta_residue
#print axioms fresh_normalized
#print axioms fresh_residue
#print axioms coefficientOne
#print axioms even_ap
#print axioms decode_int_mul
#print axioms scale_erase
#print axioms omission_at_p

end ThetaData

end ZInQ.Manuscript.RC.O12

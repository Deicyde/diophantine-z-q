import ZInQKernel.Contrib.OneProof.RC.EvenJoin.ScopedConsumer

/-! The omitted coefficient in the even formula is a coefficient of the
fixed source. Its residue is the symbol of the omitted set (tex 9905–9916);
this calculation does not use a constituent model at that set. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenJoin

open AddressGenuine AuxInputs EvenBudget IsDedekindDomain NumberField O12 PrintsArith
open Symbols ThetaCoeff Wiring
open ZInQ.Manuscript.RC.Even ZInQ.Manuscript.RC.Odd
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

/-- The even source has character ratio one at good primes. -/
def evenOmissionSign (p : ℕ) [Fact p.Prime] (V : Finset ℕ) (r : ℕ) : ℤ :=
  legendreSym p (-(((∏ s ∈ V, s) * r : ℕ) : ℤ))

/-- Flipping the bit at the deleted prime flips the omission sign. -/
theorem evenOmissionSign_flip {p r₀ r₁ : ℕ} [Fact p.Prime]
    (hr₀ : r₀.Prime) (hr₁ : r₁.Prime) (hne₀ : r₀ ≠ p) (hne₁ : r₁ ≠ p)
    (hflip : legBit (r₁ : ℤ) p = legBit (r₀ : ℤ) p + 1) (V : Finset ℕ) :
    evenOmissionSign p V r₁ = -evenOmissionSign p V r₀ := by
  have hd (r : ℕ) (hr : r.Prime) (hne : r ≠ p) : ¬ (p : ℤ) ∣ (r : ℤ) :=
    fun e => hne ((Nat.prime_dvd_prime_iff_eq Fact.out hr).mp (Int.natCast_dvd_natCast.mp e)).symm
  have hz (r : ℕ) (hr : r.Prime) (hne : r ≠ p) : ((r : ℤ) : ZMod p) ≠ 0 :=
    fun e => hd r hr hne ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp e)
  have hleg : legendreSym p (r₁ : ℤ) = -legendreSym p (r₀ : ℤ) := by
    rw [legBit_eq_ite_legendreSym (hd r₀ hr₀ hne₀),
      legBit_eq_ite_legendreSym (hd r₁ hr₁ hne₁)] at hflip
    rcases legendreSym.eq_one_or_neg_one p (hz r₀ hr₀ hne₀) with h₀ | h₀ <;>
      rcases legendreSym.eq_one_or_neg_one p (hz r₁ hr₁ hne₁) with h₁ | h₁ <;>
      norm_num [h₀, h₁] at hflip <;> norm_num [h₀, h₁]
    exact (by decide : (1 : ZMod 2) ≠ 2) hflip
  simp only [evenOmissionSign, Nat.cast_mul, ← neg_mul, legendreSym.mul, hleg, mul_neg]

variable {ℓ : ℕ} {W : WData ℓ} {L : CentralNormalization (Ecurve ℓ)}
variable {τ : SqClass (conductor W.S)} {P : EvenSource W L τ}
variable {hS : SupportSpec W} {B : ℕ} [NeZero (conductor W.S)]
variable {F : IntermediateField ℚ ℂ} [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
variable (C₀ : SourceAtPlace P (FixedRing v) (FixedField v)) (i : Fin 2)
variable {X : Model P hS B} (A : FourierData X) (E : FixedPlaceExtension v X)

/-- Read the coefficient of index p on the large model at a fresh prime
as the fixed source's symbol of the omitted set times the omission factor. -/
theorem omission_reading_scoped (hm : X.m.IsMaximal)
    (hphase : ∀ p, (evenTypes W.S hS.1).Good p → ∃ t : ℕ, C₀.η p ^ (2 ^ t) = 1)
    {U : Finset ℕ} (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p)
    (hHecke : HeckeAt A U)
    (hcoef : ∀ n, n ≠ 0 → A.coeff n (X.F U) =
      E.ringMap (timesTheta (fixedH (hS := hS) C₀ i U hU) n))
    {p r : ℕ} (hpU : p ∈ U) (hr : (evenTypes W.S hS.1).Good r) (hrU : r ∉ U) :
    letI : Fact p.Prime := ⟨(hU p hpU).1⟩
    let κ := evenOmissionSign p (U.erase p) r
    (κ = 1 ∨ κ = -1) ∧
      A.decode (A.orbitCoeff U (X.frob r) ⟨p, (hU p hpU).1.ne_zero⟩) =
        (Cp ((Ecurve ℓ).LFunction p) κ : ZMod 2) * P.reading (insert r (U.erase p)) := by
  classical
  let : CharZero X.K := charZero_of_injective_ringHom E.fieldMap.injective
  let : IsDomain X.O := Function.Injective.isDomain _ A.integral_inclusion
  let : CharZero X.O := ⟨fun x y hxy => Nat.cast_injective (R := X.K)
    (by simpa only [map_natCast] using congrArg (algebraMap X.O X.K) hxy)⟩
  let C := E.source C₀
  let hp := hU p hpU
  let : Fact p.Prime := ⟨hp.1⟩
  let V := U.erase p
  let J := V.toList
  let κ := evenOmissionSign p V r
  let ap := (Ecurve ℓ).LFunction p
  have hV : ∀ s ∈ V, (evenTypes W.S hS.1).Good s := fun s hs => hU s (Finset.mem_of_mem_erase hs)
  have hrV : r ∉ V := fun h => hrU (Finset.mem_of_mem_erase h)
  have hn (q : ℕ) (hq : q ∈ J) : ¬ q ∣ r := fun e =>
    hrV ((Nat.prime_dvd_prime_iff_eq (hV q (Finset.mem_toList.mp hq)).1 hr.1).mp e ▸
      Finset.mem_toList.mp hq)
  have hpr : ¬ p ∣ r := fun e => hrU ((Nat.prime_dvd_prime_iff_eq hp.1 hr.1).mp e ▸ hpU)
  have hrp : ¬ r ∣ p := fun e => hrU ((Nat.prime_dvd_prime_iff_eq hr.1 hp.1).mp e ▸ hpU)
  have hprod : ¬ p ∣ J.prod := by
    intro hd
    obtain ⟨q, hq, hdq⟩ := (Prime.dvd_prod_iff hp.1.prime).mp hd
    have hqV : q ∈ V := Finset.mem_toList.mp hq
    exact (Finset.mem_erase.mp hqV).1
      ((Nat.prime_dvd_prime_iff_eq hp.1 (hV q hqV).1).mp hdq).symm
  have hκ : κ = 1 ∨ κ = -1 := by
    simpa only [κ, evenOmissionSign, one_mul] using
      (legendreSym_neg_eq_one_or (p := p) (ε := (1 : ℤ))
        (fun hd : p ∣ (∏ s ∈ V, s) * r => (hp.1.dvd_mul.mp hd).elim
          (fun h => hprod (by rwa [Finset.prod_toList V])) hpr) (Or.inl rfl))
  have hCp : ap - κ - 1 = 2 * Cp ap κ := by
    obtain ⟨k, hk⟩ := evenAp hS p hp
    change ap = k + k at hk
    rcases hκ with h | h <;> rw [h] <;> unfold Cp <;> omega
  have hOff : ¬ oddPart (p * r) ⊆ U := by
    rw [oddPart_mul_prime hp.1 hr.1.ne_zero hpr]
    exact fun h => theta_index_ne_fresh hr.1 hrU (fun s hs => h (Finset.mem_insert_of_mem hs))
  have hpJ : p ∉ J := fun h => Finset.notMem_erase p U (Finset.mem_toList.mp h)
  have hJ : (p :: J).Nodup := List.nodup_cons.mpr ⟨hpJ, V.nodup_toList⟩
  have hJU : (p :: J).toFinset = U := by
    rw [List.toFinset_cons, show J.toFinset = V from Finset.toList_toFinset V]
    exact Finset.insert_erase hpU
  have hTL := TL_omission C.η C.a (source_at_place_recur C hS A.integral_inclusion hp) J
    (fun q hq => (hV q (Finset.mem_toList.mp hq)).1) V.nodup_toList hpJ hpr hn
  rw [show J.prod = ∏ s ∈ V, s from Finset.prod_toList V, one_mul] at hTL
  change TL C.η (p :: J) C.a (p * r) =
    C.η p * ((ap - κ - 1 : ℤ) : X.O) * C.a ((∏ s ∈ V, s) * r) at hTL
  rw [hCp] at hTL
  have hscale : scale X.K (P.δ + C.k) U * (2 : X.K) = scale X.K (P.δ + C.k) V := by
    have hc := Finset.card_erase_add_one hpU
    have he : -(P.δ + C.k + (U.card : ℤ) + 1) + 1 =
        -(P.δ + C.k + (V.card : ℤ) + 1) := by dsimp [V]; omega
    calc
      _ = scale X.K (P.δ + C.k) U * (2 : X.K) ^ (1 : ℤ) := by rw [zpow_one]
      _ = _ := by rw [scale, ← zpow_add₀ (by norm_num : (2 : X.K) ≠ 0), he]; rfl
  have hc := evenH_off hS A C i hV J V.nodup_toList (Finset.toList_toFinset V)
    (theta_index_ne_fresh hr.1 hrV)
  rw [TL_fresh C.η C.a J (fun q hq => (hV q (Finset.mem_toList.mp hq)).1)
    V.nodup_toList hn, show J.prod = ∏ s ∈ V, s from Finset.prod_toList V] at hc
  have hb : evenH hS A C i U (p * r) =
      C.η p * (Cp ap κ : X.O) * evenH hS A C i V r := by
    apply A.integral_inclusion
    rw [evenH_off hS A C i hU (p :: J) hJ hJU hOff, hTL, map_mul, map_mul, map_intCast,
      Int.cast_mul, Int.cast_ofNat, map_mul, map_mul, map_intCast, hc, ← hscale]
    ring
  have hη : ∃ t : ℕ, C.η p ^ (2 ^ t) = 1 := by
    obtain ⟨t, ht⟩ := hphase p hp
    exact ⟨t, by simpa only [C, FixedPlaceExtension.source, map_pow, map_one] using congrArg E.ringMap ht⟩
  have hred : Ideal.Quotient.mk X.m (evenH hS A C i U (p * r)) =
      (Cp ap κ : X.O ⧸ X.m) * Ideal.Quotient.mk X.m (evenH hS A C i V r) := by
    simp only [hb, map_mul, O12Theta.phase_residue hm X.two_mem hη, one_mul, map_intCast]
  obtain ⟨d, hd⟩ := hHecke r hr hrU
  refine ⟨hκ, ?_⟩
  rw [A.orbitCoeff_eq, hd, ite_eq_right hrp, add_zero, mul_comm r p,
    hcoef _ (Nat.mul_ne_zero hp.1.ne_zero hr.1.ne_zero), ← map_fixed_theta E C₀ A i U hU,
    O12Theta.residue_congr X.two_mem (timesTheta_congr (evenH hS A C i U) (p * r)),
    hred, even_source_symbol hS A C hm hV hr hrV hc, ← zsmul_eq_mul, map_zsmul, zsmul_eq_mul]
  generalize P.reading (insert r V) = a
  rcases (show ∀ a : ZMod 2, a = 0 ∨ a = 1 by decide) a with rfl | rfl <;> simp [A.decode_one, ap, κ, V]

end ZInQ.Manuscript.RC.EvenJoin

import ZInQKernel.Contrib.OneProof.RC.O12.Inputs
import ZInQKernel.Contrib.OneProof.RC.O12Theta.Omission
import ZInQKernel.Contrib.OneProof.RC.O12Theta.Symbol

/-! Apply the existing local identity at the realized forms for a fixed
`U` and its omitted subset. Only representatives outside the ambient Hecke
exclusions are needed for this application. -/

noncomputable section

namespace ZInQ.Manuscript.RC.O12Theta

open AddressGenuine PrintsArith TraceLimits ThetaCoeff O12 Symbols ZInQ.Manuscript.RC.Odd
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped Classical MatrixGroups

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2} {T : TypeData L ε}
variable {χ : GalQ →* Multiplicative L} {R₀ : Finset ℕ → ZMod 2} {B : ℕ} {ap : ℕ → ℤ}
variable {X : GaloisConstituentModel T R₀ ap B χ}
variable [CharZero X.O] [IsDomain X.O] [CharZero X.K]
variable {M W R : ℕ} {S : AppF.ThetaStage (StageRing X.O M)} {δ : ℤ} {adm : ℕ → Prop}
variable (A : FourierData X) (E : Lift S) (D : Divisions E δ W R adm)

private theorem orbitCoeff_eq_good {avoid : Finset ℕ}
    (ops : GoodOperators T avoid X.frob X.ρ X.Λ)
    (F : ∀ U, DeterminantFourierData ops X.m (X.F U)) (hF : ∀ U, (F U).coeff = A.coeff)
    (U : Finset ℕ) {q : ℕ} (hq : T.Good q) (ha : q ∉ avoid) (n : PosIndex)
    (hn : ¬ q ∣ n.val) :
    A.orbitCoeff U (X.frob q) n = Ideal.Quotient.mk X.m (A.coeff (q * n.val) (X.F U)) := by
  obtain ⟨_, h⟩ := A.goodHecke_of_data ops U (F U) (hF U) hq ha
  rw [A.orbitCoeff_eq, h, ite_eq_right hn, add_zero]

/-- The reduced coefficient at the omission index on the two actual forms.
The two trace evaluations use only good Hecke on the ambient domain. -/
theorem omission_read_of_stage {avoid : Finset ℕ}
    (ops : GoodOperators T avoid X.frob X.ρ X.Λ)
    (F : ∀ U, DeterminantFourierData ops X.m (X.F U)) (hF : ∀ U, (F U).coeff = A.coeff)
    (hap : S.ap = ap) (hm : X.m.IsMaximal)
    {U : Finset ℕ} {p r : ℕ} (hpU : p ∈ U) (hp : T.Good p) (hr : T.Good r)
    (hrU : r ∉ U) (hrA : r ∉ avoid)
    (hu : Admissible S W U) (hv : Admissible S W (U.erase p))
    (hfu : A.coeff (p * r) (X.F U) = E.FourierF D hu (p * r))
    (hfv : A.coeff r (X.F (U.erase p)) = E.FourierF D hv r)
    (hphase : ∃ k : ℕ, E.η p ^ (2 ^ k) = 1) :
    letI : Fact p.Prime := ⟨hp.1⟩
    let κ := ratio p hp.1 * legendreSym p (-(((∏ s ∈ U.erase p, s) * r : ℕ) : ℤ))
    A.decode (A.orbitCoeff U (X.frob r) ⟨p, hp.1.ne_zero⟩) =
      (Cp (ap p) κ : ZMod 2) *
        X.read (U.erase p) (X.redE (X.tΛ (X.frob r) (X.F (U.erase p)))) := by
  letI : Fact p.Prime := ⟨hp.1⟩
  let κ := ratio p hp.1 * legendreSym p (-(((∏ s ∈ U.erase p, s) * r : ℕ) : ℤ))
  let c := Cp (ap p) κ
  have hrp : ¬ r ∣ p := fun h =>
    hrU ((Nat.prime_dvd_prime_iff_eq hr.1 hp.1).mp h ▸ hpU)
  have hr1 : ¬ r ∣ 1 := fun h => hr.1.ne_one (Nat.dvd_one.mp h)
  have hU := orbitCoeff_eq_good A ops F hF U hr hrA ⟨p, hp.1.ne_zero⟩ hrp
  have hV := orbitCoeff_eq_good A ops F hF (U.erase p) hr hrA ⟨1, one_ne_zero⟩ hr1
  change A.decode (A.orbitCoeff U (X.frob r) ⟨p, hp.1.ne_zero⟩) = (c : ZMod 2) * _
  have hc := omission_coeff_mod_two E D A.integral_inclusion hu hpU hr.1 hrU hv
  change (2 : X.O) ∣ E.HU D hu (p * r) -
    E.η p * (Cp (S.ap p) κ : X.O) * E.HU D hv r at hc
  rw [hap] at hc
  have hred := residue_congr X.two_mem hc
  simp only [map_mul, phase_residue hm X.two_mem hphase, one_mul, map_intCast] at hred
  rw [A.read_orbit, hU, hV]
  simp only [mul_one]
  rw [mul_comm r p, hfu, hfv, residue_congr X.two_mem (fourierF_sub_hu E D hu _),
    residue_congr X.two_mem (fourierF_sub_hu E D hv _), hred]
  simp only [← zsmul_eq_mul, map_zsmul, c]

private theorem ratio_flip {p r₀ r₁ : ℕ} (hp : T.Good p) [Fact p.Prime]
    (hr₀ : T.Good r₀) (hr₁ : T.Good r₁) (hne₀ : r₀ ≠ p) (hne₁ : r₁ ≠ p)
    (hflip : legBit (r₁ : ℤ) p = legBit (r₀ : ℤ) p + 1) (V : Finset ℕ) :
    ratio p hp.1 * legendreSym p (-(((∏ s ∈ V, s) * r₁ : ℕ) : ℤ)) =
      -(ratio p hp.1 * legendreSym p (-(((∏ s ∈ V, s) * r₀ : ℕ) : ℤ))) := by
  have hd (r : ℕ) (hr : T.Good r) (hne : r ≠ p) : ¬ (p : ℤ) ∣ (r : ℤ) :=
    fun e => hne ((Nat.prime_dvd_prime_iff_eq hp.1 hr.1).mp (Int.natCast_dvd_natCast.mp e)).symm
  have hneZ (r : ℕ) (hr : T.Good r) (hne : r ≠ p) : ((r : ℤ) : ZMod p) ≠ 0 :=
    fun e => hd r hr hne ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp e)
  have hleg : legendreSym p (r₁ : ℤ) = -legendreSym p (r₀ : ℤ) := by
    rw [legBit_eq_ite_legendreSym (hd r₀ hr₀ hne₀),
      legBit_eq_ite_legendreSym (hd r₁ hr₁ hne₁)] at hflip
    rcases legendreSym.eq_one_or_neg_one p (hneZ r₀ hr₀ hne₀) with h₀ | h₀ <;>
      rcases legendreSym.eq_one_or_neg_one p (hneZ r₁ hr₁ hne₁) with h₁ | h₁ <;>
      norm_num [h₀, h₁] at hflip <;> norm_num [h₀, h₁]
    exact (by decide : (1 : ZMod 2) ≠ 2) hflip
  have sign_eq (r : ℕ) : ratio p hp.1 * legendreSym p (-(((∏ s ∈ V, s) * r : ℕ) : ℤ)) =
      ratio p hp.1 * legendreSym p (-((∏ s ∈ V, s : ℕ) : ℤ)) * legendreSym p (r : ℤ) := by
    rw [Nat.cast_mul, ← neg_mul, legendreSym.mul, mul_assoc]
  rw [sign_eq, sign_eq, hleg, mul_neg]

/-- The manuscript's second input at an actual pair of realized forms.
The local blocks and the at-one comparison are named on these same vectors. -/
theorem o12_at_one_of_stage {avoid : Finset ℕ}
    (ops : GoodOperators T avoid X.frob X.ρ X.Λ)
    (F : ∀ U, DeterminantFourierData ops X.m (X.F U)) (hF : ∀ U, (F U).coeff = A.coeff)
    (hap : S.ap = ap) (hm : X.m.IsMaximal) (htyp : IsTypeChar T χ)
    (U : Finset ℕ) (p : ℕ) (hpU : p ∈ U) (hU : ∀ s ∈ U, T.Good s)
    (hB : U.card + 1 ≤ B) (g : GalQ)
    (hu : Admissible S W U) (hv : Admissible S W (U.erase p))
    (hfu : ∀ n, A.coeff n (X.F U) = E.FourierF D hu n)
    (hfv : ∀ n, A.coeff n (X.F (U.erase p)) = E.FourierF D hv n)
    (hphase : ∃ k : ℕ, E.η p ^ (2 ^ k) = 1)
    (localData : ∀ P : LocalPair p, ∃ Dp : LocalBlocks X U P, A.UpAtOne Dp (hU p hpU).1.ne_zero) :
    ∃ (τ φ : GalQ) (κ₀ : ℤ), (κ₀ = 1 ∨ κ₀ = -1) ∧
      χ τ = 1 ∧ (∀ s ∈ U, s ≠ p → bitChar s τ = 1) ∧
      bitChar p τ = Multiplicative.ofAdd 1 ∧
      χ φ = Multiplicative.ofAdd (T.typ p) ∧
      (∀ s ∈ U, s ≠ p → bitChar s φ = Multiplicative.ofAdd (legBit p s)) ∧
      (Cp (ap p) (-κ₀) : ZMod 2) *
          X.read (U.erase p) (X.redE (X.tΛ (g * τ * φ) (X.F (U.erase p)))) -
      (Cp (ap p) κ₀ : ZMod 2) * X.read (U.erase p) (X.redE (X.tΛ (g * φ) (X.F (U.erase p)))) =
      X.read U (X.redE (X.tΛ (g * τ) (X.F U))) - X.read U (X.redE (X.tΛ g (X.F U))) := by
  let hp := hU p hpU
  letI : Fact p.Prime := ⟨hp.1⟩
  let V := U.erase p
  let κ (r : ℕ) := ratio p hp.1 * legendreSym p (-(((∏ s ∈ V, s) * r : ℕ) : ℤ))
  obtain ⟨P⟩ := localPair_exists hp
  obtain ⟨hτT, hτB, hτp, hφT, hφB⟩ := localPair_characters htyp hU hp P
  obtain ⟨Dp, hUp⟩ := localData P
  obtain ⟨r₀, j₀, n₀, hn₀, hr₀, hr₀s, e₀⟩ := X.chebotarev U hU hB (g * P.φ) (U ∪ avoid)
  obtain ⟨r₁, j₁, n₁, hn₁, hr₁, hr₁s, e₁⟩ := X.chebotarev U hU hB (g * P.τ * P.φ) (U ∪ avoid)
  have hr₀U : r₀ ∉ U := fun h => hr₀s (Finset.mem_union_left _ h)
  have hr₁U : r₁ ∉ U := fun h => hr₁s (Finset.mem_union_left _ h)
  have hne₀ : r₀ ≠ p := fun e => hr₀U (e ▸ hpU)
  have hne₁ : r₁ ≠ p := fun e => hr₁U (e ▸ hpU)
  have b₀ := (X.bit_frob r₀ p hr₀ hp hne₀).symm.trans (representative_bit X hpU hn₀ e₀)
  have b₁ := (X.bit_frob r₁ p hr₁ hp hne₁).symm.trans (representative_bit X hpU hn₁ e₁)
  have hflip : legBit (r₁ : ℤ) p = legBit (r₀ : ℤ) p + 1 := by
    apply Multiplicative.ofAdd.injective
    rw [ofAdd_add, b₁, b₀, map_mul, map_mul, map_mul, hτp]
    ac_rfl
  have hs : κ r₁ = -κ r₀ := ratio_flip hp hr₀ hr₁ hne₀ hne₁ hflip V
  have hκ : κ r₀ = 1 ∨ κ r₀ = -1 := by
    apply legendreSym_neg_eq_one_or _ (ratio_sign hp.1)
    intro h
    rcases hp.1.dvd_mul.mp h with h | h
    · obtain ⟨q, hq, hd⟩ := (Prime.dvd_finsetProd_iff hp.1.prime (fun q : ℕ => q)).mp h
      exact (Finset.mem_erase.mp hq).1
        ((Nat.prime_dvd_prime_iff_eq hp.1 (hU q (Finset.mem_of_mem_erase hq)).1).mp hd).symm
    · exact hne₀ ((Nat.prime_dvd_prime_iff_eq hp.1 hr₀.1).mp h).symm
  have read (r : ℕ) (hr : T.Good r) (hrU : r ∉ U) (hrA : r ∉ avoid) :
      A.decode (A.orbitCoeff U (X.frob r) ⟨p, hp.1.ne_zero⟩) =
        (Cp (ap p) (κ r) : ZMod 2) * X.read V (X.redE (X.tΛ (X.frob r) (X.F V))) :=
    omission_read_of_stage A E D ops F hF hap hm hpU hp hr hrU hrA hu hv (hfu _) (hfv _) hphase
  have hc₀ := read r₀ hr₀ hr₀U (fun h => hr₀s (Finset.mem_union_right _ h))
  have hc₁ := read r₁ hr₁ hr₁U (fun h => hr₁s (Finset.mem_union_right _ h))
  rw [hs] at hc₁
  have eqCoeff {r : ℕ} {x h n : GalQ} (hn : n ∈ X.N U) (e : X.frob r = h * x * h⁻¹ * n) :
      A.orbitCoeff U (X.frob r) ⟨p, hp.1.ne_zero⟩ = A.orbitCoeff U x ⟨p, hp.1.ne_zero⟩ :=
    congrArg (fun v : X.C → X.O ⧸ X.m => v (A.index ⟨p, hp.1.ne_zero⟩))
      (representative_trace X (Finset.Subset.refl U) hn e)
  rw [eqCoeff hn₀ e₀, representative_trace X (Finset.erase_subset p U) hn₀ e₀] at hc₀
  rw [eqCoeff hn₁ e₁, representative_trace X (Finset.erase_subset p U) hn₁ e₁] at hc₁
  have ho := congrArg A.decode (A.o12_reduced Dp hp.1.ne_zero hUp hU hB g)
  rw [map_sub, map_sub, hc₀, hc₁, ← A.read_orbit, ← A.read_orbit] at ho
  exact ⟨P.τ, P.φ, κ r₀, hκ, hτT, hτB, hτp, hφT, hφB, ho⟩

#print axioms orbitCoeff_eq_good
#print axioms omission_read_of_stage
#print axioms ratio_flip
#print axioms o12_at_one_of_stage

end ZInQ.Manuscript.RC.O12Theta

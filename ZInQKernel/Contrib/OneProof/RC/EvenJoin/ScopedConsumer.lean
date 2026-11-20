import ZInQKernel.Contrib.OneProof.RC.EvenJoin.Scoped

/-! Fresh-prime reading, fixed-set factorization, primary isolation, and
the unit seed use a single row at a time. The deletion comparison for
(O.12) is kept at its existing output interface. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenJoin

open ZInQ.Manuscript AddressGenuine AuxInputs EvenBudget NumberField O12 ThetaCoeff Wiring
open IsDedekindDomain PrintsArith Symbols
open ZInQ.Manuscript.RC.Even ZInQ.Manuscript.RC.Odd
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open Multiplicative

attribute [local instance] GaloisConstituentModel.modMst

variable {ℓ : ℕ} {W : WData ℓ} {L : CentralNormalization (Ecurve ℓ)}
variable {τ : SqClass (conductor W.S)} {P : EvenSource W L τ}
variable {hS : SupportSpec W} {B : ℕ} [NeZero (conductor W.S)]
variable {F : IntermediateField ℚ ℂ} [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
variable (C₀ : SourceAtPlace P (FixedRing v) (FixedField v)) (i : Fin 2)
variable {X : Model P hS B} (A : FourierData X) (E : FixedPlaceExtension v X)

private theorem residue_of_dvd_two {x y : X.O} (h : (2 : X.O) ∣ x - y) :
    Ideal.Quotient.mk X.m x = Ideal.Quotient.mk X.m y := by
  obtain ⟨z, hz⟩ := h
  rw [← sub_eq_zero, ← map_sub, hz, map_mul,
    Ideal.Quotient.eq_zero_iff_mem.mpr X.two_mem, zero_mul]

include E in
/-- At a fresh prime the positive coefficient of this seed reads the fixed
source's valuation symbol. No other seed of the carrier is used. -/
theorem coefficient_one_scoped (hm : X.m.IsMaximal)
    {U : Finset ℕ} (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p)
    (hHecke : HeckeAt A U)
    (hcoef : ∀ n, n ≠ 0 → A.coeff n (X.F U) =
      E.ringMap (timesTheta (fixedH (hS := hS) C₀ i U hU) n))
    {q : ℕ} (hq : (evenTypes W.S hS.1).Good q) (hqU : q ∉ U) :
    P.reading (insert q U) = X.readK U (X.tK (X.frob q) (X.FK U)) := by
  classical
  let : CharZero X.K := charZero_of_injective_ringHom E.fieldMap.injective
  let C := E.source C₀
  let J := U.toList
  have hj (p : ℕ) (hp : p ∈ J) := (hU p (Finset.mem_toList.mp hp)).1
  have hd (p : ℕ) (hp : p ∈ J) : ¬ p ∣ q := fun hpq =>
    hqU ((Nat.prime_dvd_prime_iff_eq (hj p hp) hq.1).mp hpq ▸ Finset.mem_toList.mp hp)
  have hfresh := TL_fresh C.η C.a J hj U.nodup_toList hd
  rw [show J.prod = ∏ p ∈ U, p from Finset.prod_toList U] at hfresh
  have hH := evenH_off hS A C i hU J U.nodup_toList (Finset.toList_toFinset U)
    (theta_index_ne_fresh hq.1 hqU)
  rw [hfresh] at hH
  obtain ⟨D, hD⟩ := hHecke q hq hqU
  rw [GaloisConstituentModel.FK, X.tK_mk, X.readK_mk, A.read_at_one, hD, ite_eq_right
    (fun h : q ∣ 1 => hq.1.ne_one (Nat.dvd_one.mp h)), add_zero, mul_one,
    hcoef q hq.1.ne_zero, ← map_fixed_theta E C₀ A i U hU q,
    residue_of_dvd_two (timesTheta_congr (evenH hS A C i U) q),
    even_source_symbol hS A C hm hU hq hqU hH]
  generalize P.reading (insert q U) = r
  rcases (show ∀ r : ZMod 2, r = 0 ∨ r = 1 by decide) r with rfl | rfl
  · simp
  · simp [A.decode_one]

/-- Right invariance on one reduced trace orbit (tex 9741–9750). The
ambient congruence subgroup is only used via its action on this seed. -/
theorem trace_join_at (X : Model P hS B) {U : Finset ℕ}
    (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p) (hB : U.card + 1 ≤ B)
    (g x : GalQ) (hx : x ∈ Subgroup.closure (sqSet GalQ) ⊔ X.N U) :
    X.tK (g * x) (X.FK U) = X.tK g (X.FK U) := by
  rw [← Subgroup.closure_eq (X.N U), ← Subgroup.closure_union] at hx
  induction hx using Subgroup.closure_induction generalizing g with
  | mem x hx =>
    rcases hx with ⟨h, rfl⟩ | hn
    · exact trace_square_invariance X.tK X.dK (X.FK U) X.trace_mul
        (X.det_orbit' U hU hB) (X.two_fresh' U hU hB) g h
    · rw [GaloisConstituentModel.FK, X.tK_mk, X.tK_mk, X.mk_eq_mk_iff]
      exact X.level_mem_Kst U U hU hB (Finset.Subset.refl U) g x hn
  | one => simp
  | mul x y _ _ ihx ihy => rw [← mul_assoc, ihy, ihx]
  | inv x _ ihx => rw [← ihx (g * x⁻¹), inv_mul_cancel_right]

variable (H : BudgetRealizationScoped (hS := hS) C₀ i B)

include H in
/-- Fixed-set factorization for the exact same source as in the old handoff. -/
theorem fixedU_of_joined_scoped : FixedUFactorization (evenTypes W.S hS.1) P.reading B := by
  classical
  intro U q r hcard hU hq hr hqU hrU ht hb
  have hB : U.card + 1 ≤ B := by simpa only [Finset.card_insert_of_notMem hqU] using hcard
  obtain ⟨X, A, E, _, _, _, hm, hHecke, _, hcoef⟩ := H.2.2 U hU hB
  have htyp : IsTypeChar (evenTypes W.S hS.1) (typChar (conductor W.S)) :=
    isTypeChar_typeData _ (conductor_pos hS.1) _
  have hx : (X.frob q)⁻¹ * X.frob r ∈ Subgroup.closure (sqSet GalQ) ⊔ X.N U := by
    refine X.kummer U hU hB _ ?_ fun p hp => ?_
    · rw [map_mul, map_inv, htyp q _ hq (X.frob_spec q hq),
        htyp r _ hr (X.frob_spec r hr), ht]
      exact inv_mul_cancel (ofAdd ((evenTypes W.S hS.1).typ r))
    · rw [map_mul, map_inv, X.bit_frob q p hq (hU p hp) (fun h => hqU (h ▸ hp)),
        X.bit_frob r p hr (hU p hp) (fun h => hrU (h ▸ hp)), hb p hp, inv_mul_cancel]
  have he := trace_join_at X hU hB (X.frob q) _ hx
  rw [mul_inv_cancel_left] at he
  rw [coefficient_one_scoped C₀ i A E hm hU hHecke hcoef hq hqU,
    coefficient_one_scoped C₀ i A E hm hU hHecke hcoef hr hrU, he]

include H in
/-- A fresh vertex with trivial type and quadratic labels has reading zero. -/
theorem primary_of_joined_scoped : PrimaryReading (evenTypes W.S hS.1) P.reading B := by
  classical
  intro U q hU hq hqU hcard ht hb
  have hB : U.card + 1 ≤ B := by simpa only [Finset.card_insert_of_notMem hqU] using hcard
  obtain ⟨X, A, E, _, _, _, hm, hHecke, _, hcoef⟩ := H.2.2 U hU hB
  have htyp : IsTypeChar (evenTypes W.S hS.1) (typChar (conductor W.S)) :=
    isTypeChar_typeData _ (conductor_pos hS.1) _
  have hx : X.frob q ∈ Subgroup.closure (sqSet GalQ) ⊔ X.N U := by
    refine X.kummer U hU hB _ ?_ fun p hp => ?_
    · rw [htyp q _ hq (X.frob_spec q hq), ht, ofAdd_zero]
    · rw [X.bit_frob q p hq (hU p hp) (fun h => hqU (h ▸ hp)), hb p hp, ofAdd_zero]
  have he := trace_join_at X hU hB 1 _ hx
  rw [one_mul] at he
  rw [coefficient_one_scoped C₀ i A E hm hU hHecke hcoef hq hqU, he, X.trace_one,
    show (2 : ZMod 2) = 0 from rfl, zero_smul, map_zero]

/-- The attained minimum has a unit seed on the scoped interface alone. -/
theorem unitSeed_of_joined_scoped
    (H : ∀ B, BudgetRealizationScoped (hS := hS) C₀ i B) :
    ∃ Γ, IsUnitSeed (evenSign W.S) (P.symbol hS) Γ :=
  P.unitSeed hS (fun B => fixedU_of_joined_scoped C₀ i (H B))

/-- Replacement for the rules-and-seed consumer once the unmodified
deletion reading is supplied. All its other inputs now use the scoped budget. -/
theorem rules_and_seed_of_joined_scoped
    (H : ∀ B, BudgetRealizationScoped (hS := hS) C₀ i B)
    (hO12 : ∀ B, O12Reading (evenTypes W.S hS.1) P.reading
      (fun p => (Ecurve ℓ).LFunction p) B) :
    CoefficientRules (evenSign W.S) (P.symbol hS) ∧
      ∃ Γ, IsUnitSeed (evenSign W.S) (P.symbol hS) Γ :=
  ⟨coefficientRules_symb _ _ _ (fun B => fixedU_of_joined_scoped C₀ i (H B))
    hO12 (evenAp hS) (fun B => primary_of_joined_scoped C₀ i (H B)),
    unitSeed_of_joined_scoped C₀ i H⟩

end ZInQ.Manuscript.RC.EvenJoin

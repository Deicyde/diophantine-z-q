import ZInQKernel.Contrib.OneProof.RC.EvenJoin.JointQuotient
import ZInQKernel.Contrib.OneProof.RC.EvenJoin.JointOmission

/-! Apply (O.12) on the larger row and read each fresh prime using the
reduced trace of its own row. Both rows use the same fixed source. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenJoin

open AddressGenuine AuxInputs EvenBudget IsDedekindDomain NumberField O12 PrintsArith
open Symbols ThetaCoeff Wiring Multiplicative
open ZInQ.Manuscript.RC.Even ZInQ.Manuscript.RC.Odd
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

attribute [local instance] GaloisConstituentModel.modMst

variable {ℓ : ℕ} {W : WData ℓ} {L : CentralNormalization (Ecurve ℓ)}
variable {τ : SqClass (conductor W.S)} {P : EvenSource W L τ}
variable {hS : SupportSpec W} {B : ℕ} [NeZero (conductor W.S)]
variable {F : IntermediateField ℚ ℂ} [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

private theorem exists_character_cut (m : ℕ) [NeZero m] (U : Finset ℕ) :
    ∃ K : IntermediateField ℚ Qbar, FiniteDimensional ℚ K ∧ IsGalois ℚ K ∧
      ∀ n ∈ K.fixingSubgroup, typChar m n = 1 ∧ ∀ s ∈ U, bitChar s n = 1 := by
  obtain ⟨K₁, f₁, e₁⟩ := exists_fixingSubgroup_le_ker_typChar m
  obtain ⟨K₂, f₂, e₂⟩ := exists_fixingSubgroup_le_ker_bitChar U
  have := f₁
  have := f₂
  let K₀ := K₁ ⊔ K₂
  let K := IntermediateField.normalClosure ℚ K₀ Qbar
  have : FiniteDimensional ℚ K₀ := by
    change FiniteDimensional ℚ (↑(K₁ ⊔ K₂) : Type)
    infer_instance
  have : Normal ℚ K := normalClosure.normal ℚ K₀ Qbar
  refine ⟨K, normalClosure.is_finiteDimensional ℚ K₀ Qbar, ⟨⟩, fun n hn => ?_⟩
  have h := IntermediateField.fixingSubgroup_antitone K₀.le_normalClosure hn
  exact ⟨e₁ n (IntermediateField.fixingSubgroup_antitone le_sup_left h),
    e₂ n (IntermediateField.fixingSubgroup_antitone le_sup_right h)⟩

/-- The retained characters control the whole coefficientwise reduced trace
of this row, by the previously proved fixed-set trace invariance. -/
theorem reduced_trace_of_class (X : Model P hS B) {U : Finset ℕ}
    (hU : ∀ s ∈ U, (evenTypes W.S hS.1).Good s) (hB : U.card + 1 ≤ B)
    {x g h n : GalQ} (he : x = h * g * h⁻¹ * n)
    (ht : typChar (conductor W.S) n = 1) (hb : ∀ s ∈ U, bitChar s n = 1) :
    X.redE (X.tΛ x (X.F U)) = X.redE (X.tΛ g (X.F U)) := by
  have e := trace_join_at X hU hB (h * g * h⁻¹) n (X.kummer U hU hB n ht hb)
  rw [GaloisConstituentModel.FK, X.tK_mk, X.tK_mk, X.mk_eq_mk_iff] at e
  rw [he]
  calc
    _ = X.redE (X.tΛ (h * g * h⁻¹) (X.F U)) :=
      eq_of_sub_eq_zero (by simpa only [map_sub] using LinearMap.mem_ker.mp (X.Kst_le_ker e))
    _ = _ := by rw [X.tΛ_conj]

private theorem reading_eq_orbit_one
    (C₀ : SourceAtPlace P (FixedRing v) (FixedField v)) (i : Fin 2)
    {X : Model P hS B} (A : FourierData X) (E : FixedPlaceExtension v X)
    (hm : X.m.IsMaximal) {U : Finset ℕ} (hU : ∀ s ∈ U, (evenTypes W.S hS.1).Good s)
    (hHecke : HeckeAt A U)
    (hcoef : ∀ n, n ≠ 0 → A.coeff n (X.F U) =
      E.ringMap (timesTheta (fixedH (hS := hS) C₀ i U hU) n))
    {q : ℕ} (hq : (evenTypes W.S hS.1).Good q) (hqU : q ∉ U) :
    P.reading (insert q U) = A.decode (A.orbitCoeff U (X.frob q) ⟨1, one_ne_zero⟩) := by
  rw [← A.read_orbit, ← X.readK_mk, ← X.tK_mk]
  exact coefficient_one_scoped C₀ i A E hm hU hHecke hcoef hq hqU

variable (C₀ : SourceAtPlace P (FixedRing v) (FixedField v)) (i : Fin 2)

/-- The exact deletion-reading input of the scoped rules theorem. The two
per-set models may be different, including their coefficient fields. -/
theorem o12_of_joined_scoped (H : BudgetRealizationScoped (hS := hS) C₀ i B) :
    O12Reading (evenTypes W.S hS.1) P.reading (fun p => (Ecurve ℓ).LFunction p) B := by
  classical
  intro U p hpU hU hB l bq
  let V := U.erase p
  let T := evenTypes W.S hS.1
  let m := conductor W.S
  have hV : ∀ s ∈ V, T.Good s := fun s hs => hU s (Finset.mem_of_mem_erase hs)
  have hVB : V.card + 1 ≤ B :=
    (Nat.add_le_add_right (Finset.card_le_card (Finset.erase_subset p U)) 1).trans hB
  obtain ⟨X, A, E, _, _, _, hm, hHecke, hLocal, hcoef⟩ := H.2.2 U hU hB
  obtain ⟨Y, A', E', _, _, _, hm', hHecke', _, hcoef'⟩ := H.2.2 V hV hVB
  let : CharZero X.K := charZero_of_injective_ringHom E.fieldMap.injective
  have htyp : IsTypeChar T (typChar m) := isTypeChar_typeData _ (conductor_pos hS.1) _
  obtain ⟨g, hgT, hgB⟩ := X.chi_surj htyp U hU l bq
  let hp := hU p hpU
  let : Fact p.Prime := ⟨hp.1⟩
  obtain ⟨D⟩ := localPair_exists hp
  obtain ⟨hτT, hτB, hτp, hφT, hφB⟩ := localPair_characters htyp hU hp D
  obtain ⟨S⟩ := hLocal p hpU D
  let Q := O12Local.combine S.cusp.sector S.eisenstein S.disjoint S.support
  have hUp : A.UpAtOne Q hp.1.ne_zero :=
    O12Local.combine_upAtOne A _ _ S.disjoint S.support _
      (O12Local.cuspidal_upAtOne A _ _ S.whittaker) S.eisenstein_shift
  obtain ⟨KU, hKU, gKU, eU⟩ := exists_character_cut m U
  obtain ⟨KV, hKV, gKV, eV⟩ := exists_character_cut m V
  have := hKU
  have := hKV
  have := gKU
  have := gKV
  -- These cuts suffice for the two reduced trace orbits. The character cut
  -- records the retained labels (including the bit at the deleted prime).
  let target : Fin 4 → GalQ := ![g, g * D.τ, g * D.φ, g * D.τ * D.φ]
  obtain ⟨q, hq⟩ := joint_frobenius KU KV KU (U ∪ T.m.primeFactors) target
  have good (j : Fin 4) : T.Good (q j) := by
    have h := hq j
    exact ⟨h.1, (Nat.Prime.coprime_iff_not_dvd h.1).mpr fun hd =>
      h.2.1 (Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨h.1, hd, T.m_pos.ne'⟩))⟩
  have fresh (j : Fin 4) : q j ∉ U := fun h =>
    (hq j).2.1 (Finset.mem_union_left _ h)
  have freshV (j : Fin 4) : q j ∉ V := fun h => fresh j (Finset.mem_of_mem_erase h)
  have liftClass (j : Fin 4) (σ : GalQ) (hσ : IsFrobAt σ (q j)) :=
    (hq j).2.2.elim fun _ ⟨_, _, _, _, h⟩ => h σ hσ
  have chars (j : Fin 4) : ofAdd (T.typ (q j)) = typChar m (target j) ∧
      ∀ s ∈ U, ofAdd (legBit (q j) s) = bitChar s (target j) := by
    obtain ⟨h, n, hn, he⟩ := liftClass j _ (X.frob_spec (q j) (good j))
    rw [fixingSubgroup_jointCut] at hn
    obtain ⟨ht, hb⟩ := eU n hn.2
    constructor
    · rw [← X.typ_frob htyp (q j) (good j), he, map_mul, ht]
      calc
        _ = typChar m (h * target j * h⁻¹) := mul_one _
        _ = _ := by
          rw [map_mul, map_mul, map_inv]
          calc
            _ = typChar m (target j) * (typChar m h * (typChar m h)⁻¹) :=
              (mul_assoc (typChar m h) (typChar m (target j)) (typChar m h)⁻¹).trans
                (mul_left_comm (typChar m h) (typChar m (target j)) (typChar m h)⁻¹)
            _ = _ := (congrArg (typChar m (target j) * ·) (mul_inv_cancel (typChar m h))).trans
              (mul_one (typChar m (target j)))
    · intro s hs
      rw [← X.bit_frob _ s (good j) (hU s hs) (fun h => fresh j (h ▸ hs)),
        he, map_mul, hb s hs, mul_one, map_conj_of_comm]
  have traceU (j : Fin 4) (n : PosIndex) :
      A.orbitCoeff U (X.frob (q j)) n = A.orbitCoeff U (target j) n := by
    obtain ⟨h, a, ha, he⟩ := liftClass j _ (X.frob_spec (q j) (good j))
    rw [fixingSubgroup_jointCut] at ha
    obtain ⟨ht, hb⟩ := eU a ha.1.1
    exact congrFun (reduced_trace_of_class X hU hB he ht hb) (A.index n)
  have readV (j : Fin 4) :
      P.reading (insert (q j) V) = Y.read V (Y.redE (Y.tΛ (target j) (Y.F V))) := by
    obtain ⟨h, a, ha, he⟩ := liftClass j _ (Y.frob_spec (q j) (good j))
    rw [fixingSubgroup_jointCut] at ha
    obtain ⟨ht, hb⟩ := eV a ha.1.2
    rw [reading_eq_orbit_one C₀ i A' E' hm' hV hHecke' hcoef' (good j) (freshV j),
      ← A'.read_orbit, reduced_trace_of_class Y hV hVB he ht hb]
  have omittedTrace :
      Y.redE (Y.tΛ (target 3) (Y.F V)) = Y.redE (Y.tΛ (target 2) (Y.F V)) := by
    refine reduced_trace_of_class Y hV hVB (h := 1) (n := D.φ⁻¹ * D.τ * D.φ) ?_ ?_ ?_
    · change g * D.τ * D.φ = 1 * (g * D.φ) * 1⁻¹ * (D.φ⁻¹ * D.τ * D.φ)
      group
    · change typChar m (D.φ⁻¹ * D.τ * D.φ) = 1
      rw [map_mul, map_mul, map_inv, hτT]
      exact (congrArg (· * typChar m D.φ) (mul_one _)).trans (inv_mul_cancel (typChar m D.φ))
    · intro s hs
      obtain ⟨hne, hsU⟩ := Finset.mem_erase.mp hs
      rw [map_mul, map_mul, map_inv, hτB s hsU hne, mul_one, inv_mul_cancel]
  have omittedSame : P.reading (insert (q 3) V) = P.reading (insert (q 2) V) :=
    (readV 3).trans ((congrArg (Y.read V) omittedTrace).trans (readV 2).symm)
  have readU (j : Fin 4) :
      P.reading (insert (q j) U) = A.decode (A.orbitCoeff U (target j) ⟨1, one_ne_zero⟩) :=
    (reading_eq_orbit_one C₀ i A E hm hU hHecke hcoef (good j) (fresh j)).trans
      (congrArg A.decode (traceU j _))
  have eqt (j : Fin 4) (a) (h : typChar m (target j) = ofAdd a) : T.typ (q j) = a :=
    ofAdd.injective ((chars j).1.trans h)
  have eqb (j : Fin 4) (s : ℕ) (hs : s ∈ U) (a : ZMod 2)
      (h : bitChar s (target j) = ofAdd a) : legBit (q j) s = a :=
    ofAdd.injective (((chars j).2 s hs).trans h)
  have flip : legBit (q 3) p = legBit (q 2) p + 1 := by
    apply ofAdd.injective
    rw [ofAdd_add, (chars 3).2 p hpU, (chars 2).2 p hpU]
    change bitChar p (g * D.τ * D.φ) = bitChar p (g * D.φ) * ofAdd (1 : ZMod 2)
    simp only [map_mul, hτp]
    ac_rfl
  obtain ⟨hκ, c₀⟩ := omission_reading_scoped C₀ i A E hm H.2.1 hU hHecke hcoef hpU (good 2) (fresh 2)
  obtain ⟨-, c₁⟩ := omission_reading_scoped C₀ i A E hm H.2.1 hU hHecke hcoef hpU (good 3) (fresh 3)
  let κ := evenOmissionSign p V (q 2)
  have hsign : evenOmissionSign p V (q 3) = -κ :=
    evenOmissionSign_flip (good 2).1 (good 3).1
      (fun h => fresh 2 (h ▸ hpU)) (fun h => fresh 3 (h ▸ hpU)) flip V
  change A.decode (A.orbitCoeff U (X.frob (q 3)) ⟨p, hp.1.ne_zero⟩) =
    (Cp _ (evenOmissionSign p V (q 3)) : ZMod 2) * P.reading (insert (q 3) V) at c₁
  rw [hsign, traceU 3, readV 3, omittedTrace] at c₁
  rw [traceU 2, readV 2] at c₀
  have ho := congrArg A.decode (A.o12_reduced Q hp.1.ne_zero hUp hU hB g)
  change A.decode (A.orbitCoeff U (target 3) ⟨p, hp.1.ne_zero⟩ -
      A.orbitCoeff U (target 2) ⟨p, hp.1.ne_zero⟩) =
    A.decode (A.orbitCoeff U (target 1) ⟨1, one_ne_zero⟩ -
      A.orbitCoeff U (target 0) ⟨1, one_ne_zero⟩) at ho
  rw [map_sub, map_sub, c₁, c₀, ← readV 2, ← readU 1, ← readU 0] at ho
  refine ⟨q 0, q 1, q 2, q 3, κ, good 0, good 1, good 2, good 3,
    fresh 0, fresh 1, fresh 2, fresh 3, eqt 0 _ hgT, eqt 1 _ ?_,
    fun s hs => eqb 0 s hs _ (hgB s hs), fun s hs hsp => eqb 1 s hs _ ?_,
    eqb 1 p hpU _ ?_, eqt 2 _ ?_, eqt 3 _ ?_, fun s hs hsp => ⟨eqb 2 s hs _ ?_, eqb 3 s hs _ ?_⟩,
    flip, hκ, ?_⟩
  · change typChar m (g * D.τ) = _
    rw [map_mul, hgT, hτT]
    exact mul_one (ofAdd l : Multiplicative (SqClass m))
  · change bitChar s (g * D.τ) = _
    rw [map_mul, hgB s hs, hτB s hs hsp, mul_one]
  · change bitChar p (g * D.τ) = _
    rw [map_mul, hgB p hpU, hτp, ← ofAdd_add]
  · change typChar m (g * D.φ) = _
    rw [map_mul, hgT, hφT, ← ofAdd_add, add_comm]
  · change typChar m (g * D.τ * D.φ) = _
    rw [map_mul, map_mul, hgT, hτT, hφT]
    calc
      _ = ofAdd l * ofAdd (T.typ p) := congrArg (· * ofAdd (T.typ p)) (mul_one _)
      _ = _ := congrArg ofAdd (add_comm l (T.typ p))
  · change bitChar s (g * D.φ) = _
    rw [map_mul, hgB s hs, hφB s hs hsp, ← ofAdd_add, add_comm]
  · change bitChar s (g * D.τ * D.φ) = _
    rw [map_mul, map_mul, hgB s hs, hτB s hs hsp, mul_one, hφB s hs hsp, ← ofAdd_add, add_comm]
  · change (Cp ((Ecurve ℓ).LFunction p) (-κ) : ZMod 2) * P.reading (insert (q 3) V) -
      (Cp ((Ecurve ℓ).LFunction p) κ : ZMod 2) * P.reading (insert (q 2) V) = _
    rw [omittedSame]
    exact ho

/-- The scoped rules and unit seed, with the explicit deletion input
discharged by the joint quotient. -/
theorem rules_and_seed_of_joined_joint
    (H : ∀ B, BudgetRealizationScoped (hS := hS) C₀ i B) :
    CoefficientRules (evenSign W.S) (P.symbol hS) ∧
      ∃ Γ, IsUnitSeed (evenSign W.S) (P.symbol hS) Γ :=
  rules_and_seed_of_joined_scoped C₀ i H (fun B => o12_of_joined_scoped C₀ i (H B))

end ZInQ.Manuscript.RC.EvenJoin

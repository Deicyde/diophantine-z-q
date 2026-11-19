import ZInQKernel.Contrib.OneProof.RC.O12.Inputs

/-! Descend a single common-space reading to the dictionary. The only
representatives used for omission can be chosen outside the ambient
exclusions (tex 9919–9945). The comparisons at prescribed primes use
the fixed-set trace orbit (tex 9745–9750, 9947–9948). -/

noncomputable section

namespace ZInQ.Manuscript.RC.O12Realize

open AddressGenuine PrintsArith Symbols Finset
open ZInQ.Manuscript.RC.Odd
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2} {T : TypeData L ε}
variable {χ : GalQ →* Multiplicative L} {R : Finset ℕ → ZMod 2} {ap : ℕ → ℤ} {B : ℕ}

abbrev traceRead (X : GaloisConstituentModel T R ap B χ) (U : Finset ℕ) (g : GalQ) : ZMod 2 :=
  X.read U (X.redE (X.tΛ g (X.F U)))

/-- The first constituent input at one pair. -/
def FreshAt (X : GaloisConstituentModel T R ap B χ) (U : Finset ℕ) (q : ℕ) : Prop :=
  R (insert q U) = traceRead X U (X.frob q)

/-- The second constituent input, restricted to one set and one omission. -/
def OmissionAt (X : GaloisConstituentModel T R ap B χ) (U : Finset ℕ) (p : ℕ) : Prop :=
  ∀ g : GalQ, ∃ (τ φ : GalQ) (κ : ℤ), (κ = 1 ∨ κ = -1) ∧
    χ τ = 1 ∧ (∀ s ∈ U, s ≠ p → bitChar s τ = 1) ∧
    bitChar p τ = Multiplicative.ofAdd 1 ∧
    χ φ = Multiplicative.ofAdd (T.typ p) ∧
    (∀ s ∈ U, s ≠ p → bitChar s φ = Multiplicative.ofAdd (legBit p s)) ∧
    (Cp (ap p) (-κ) : ZMod 2) * traceRead X (U.erase p) (g * τ * φ) -
      (Cp (ap p) κ : ZMod 2) * traceRead X (U.erase p) (g * φ) =
    traceRead X U (g * τ) - traceRead X U g

/-- The readings in a common space for the root and its subsets. Fresh
representatives for omission may avoid the ambient exclusions. -/
structure ReadingsOn (X : GaloisConstituentModel T R ap B χ) (U avoid : Finset ℕ) : Prop where
  fresh : ∀ V ⊆ U, ∀ q, T.Good q → q ∉ V → q ∉ avoid → FreshAt X V q
  omission : ∀ p ∈ U, OmissionAt X U p

/-- Product labels in the precise shape of the existing dictionary input,
at one fixed root. All representatives are selected outside `U ∪ avoid`. -/
theorem o12_at (X : GaloisConstituentModel T R ap B χ) (htyp : IsTypeChar T χ)
    {U avoid : Finset ℕ} (h : ReadingsOn X U avoid)
    (p : ℕ) (hpU : p ∈ U) (hU : ∀ s ∈ U, T.Good s) (hB : U.card + 1 ≤ B)
    (ℓ : L) (bq : ℕ → ZMod 2) :
    ∃ (q qτ r0 r1 : ℕ) (κ : ℤ),
      T.Good q ∧ T.Good qτ ∧ T.Good r0 ∧ T.Good r1 ∧ q ∉ U ∧ qτ ∉ U ∧ r0 ∉ U ∧ r1 ∉ U ∧
      T.typ q = ℓ ∧ T.typ qτ = ℓ ∧ (∀ s ∈ U, legBit q s = bq s) ∧
      (∀ s ∈ U, s ≠ p → legBit qτ s = bq s) ∧ legBit qτ p = bq p + 1 ∧
      T.typ r0 = T.typ p + ℓ ∧ T.typ r1 = T.typ p + ℓ ∧
      (∀ s ∈ U, s ≠ p → legBit r0 s = legBit p s + bq s ∧ legBit r1 s = legBit p s + bq s) ∧
      legBit r1 p = legBit r0 p + 1 ∧ (κ = 1 ∨ κ = -1) ∧
      (Cp (ap p) (-κ) : ZMod 2) * R (insert r1 (U.erase p)) -
        (Cp (ap p) κ : ZMod 2) * R (insert r0 (U.erase p)) =
      R (insert qτ U) - R (insert q U) := by
  obtain ⟨g, hgT, hgB⟩ := X.chi_surj htyp U hU ℓ bq
  obtain ⟨τ, φ, κ, hκ, hτT, hτB, hτp, hφT, hφB, hO⟩ := h.omission p hpU g
  have rep (y : GalQ) :
      ∃ q, T.Good q ∧ q ∉ U ∧ Multiplicative.ofAdd (T.typ q) = χ y ∧
        (∀ s ∈ U, Multiplicative.ofAdd (legBit q s) = bitChar s y) ∧
        ∀ V ⊆ U, R (insert q V) = traceRead X V y := by
    obtain ⟨q, j, n, hn, hq, hqa, hqf⟩ := X.chebotarev U hU hB y (U ∪ avoid)
    have hqU : q ∉ U := fun hq' => hqa (mem_union_left _ hq')
    refine ⟨q, hq, hqU, ?_, ?_, ?_⟩
    · rw [← X.typ_frob htyp q hq, hqf, map_mul, (X.N_chi U n hn).1, mul_one, map_conj_of_comm]
    · intro s hs
      rw [← X.bit_frob q s hq (hU s hs) (fun e => hqU (e ▸ hs))]
      exact O12.representative_bit X hs hn hqf
    · intro V hV
      calc
        R (insert q V) = traceRead X V (X.frob q) :=
          h.fresh V hV q hq (fun hq' => hqU (hV hq')) (fun hq' => hqa (mem_union_right _ hq'))
        _ = traceRead X V y := congrArg (X.read V) (O12.representative_trace X hV hn hqf)
  obtain ⟨q, hq, hqU, tq, b, v⟩ := rep g
  obtain ⟨qτ, hqτ, hqτU, tqτ, bτ, vτ⟩ := rep (g * τ)
  obtain ⟨r0, hr0, hr0U, tr0, b0, v0⟩ := rep (g * φ)
  obtain ⟨r1, hr1, hr1U, tr1, b1, v1⟩ := rep (g * τ * φ)
  refine ⟨q, qτ, r0, r1, κ, hq, hqτ, hr0, hr1, hqU, hqτU, hr0U, hr1U,
    Multiplicative.ofAdd.injective (tq.trans hgT), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hκ, ?_⟩
  · rw [map_mul, hτT, mul_one, hgT] at tqτ
    exact Multiplicative.ofAdd.injective tqτ
  · intro s hs
    exact Multiplicative.ofAdd.injective ((b s hs).trans (hgB s hs))
  · intro s hs hsp
    have e := bτ s hs
    rw [map_mul, hτB s hs hsp, mul_one, hgB s hs] at e
    exact Multiplicative.ofAdd.injective e
  · have e := bτ p hpU
    rw [map_mul, hgB p hpU, hτp, ← ofAdd_add] at e
    exact Multiplicative.ofAdd.injective e
  · rw [map_mul, hgT, hφT, ← ofAdd_add, add_comm] at tr0
    exact Multiplicative.ofAdd.injective tr0
  · rw [map_mul, map_mul, hτT, mul_one, hgT, hφT, ← ofAdd_add, add_comm] at tr1
    exact Multiplicative.ofAdd.injective tr1
  · intro s hs hsp
    have e0 := b0 s hs
    have e1 := b1 s hs
    rw [map_mul, hgB s hs, hφB s hs hsp, ← ofAdd_add, add_comm] at e0
    rw [map_mul, map_mul, hτB s hs hsp, mul_one, hgB s hs, hφB s hs hsp,
      ← ofAdd_add, add_comm] at e1
    exact ⟨Multiplicative.ofAdd.injective e0, Multiplicative.ofAdd.injective e1⟩
  · have e0 := b0 p hpU
    have e1 := b1 p hpU
    rw [map_mul] at e0
    rw [map_mul, map_mul, hτp] at e1
    apply Multiplicative.ofAdd.injective
    rw [ofAdd_add, e0, e1]
    ac_rfl
  · rw [v1 _ (erase_subset p U), v0 _ (erase_subset p U), vτ _ (subset_refl U), v _ (subset_refl U)]
    exact hO

/-- The residue reading depends only on the type and the bits at the root.
Use the existing operator-stable quotient only in this one common space. -/
theorem traceRead_eq_of_labels (X : GaloisConstituentModel T R ap B χ)
    {U : Finset ℕ} (hU : ∀ s ∈ U, T.Good s) (hB : U.card + 1 ≤ B)
    {g g' : GalQ} (ht : χ g = χ g') (hb : ∀ s ∈ U, bitChar s g = bitChar s g') :
    traceRead X U g = traceRead X U g' := by
  let inst := X.modMst
  have hx : g⁻¹ * g' ∈ Subgroup.closure (sqSet GalQ) ⊔ X.N U := by
    apply X.kummer U hU hB
    · rw [map_mul, map_inv, ht, inv_mul_cancel]
    · intro s hs
      rw [map_mul, map_inv, hb s hs, inv_mul_cancel]
  have orbit (a x : GalQ) (h : x ∈ Subgroup.closure (sqSet GalQ) ⊔ X.N U) :
      X.tK (a * x) (X.FK U) = X.tK a (X.FK U) := by
    rw [← Subgroup.closure_eq (X.N U), ← Subgroup.closure_union] at h
    induction h using Subgroup.closure_induction generalizing a with
    | mem x hx =>
      rcases hx with ⟨y, rfl⟩ | hn
      · exact trace_square_invariance X.tK X.dK (X.FK U) X.trace_mul
          (X.det_orbit' U hU hB) (X.two_fresh' U hU hB) a y
      · rw [GaloisConstituentModel.FK, X.tK_mk, X.tK_mk, X.mk_eq_mk_iff]
        exact X.level_mem_Kst U U hU hB (subset_refl U) a x hn
    | one => simp
    | mul x y _ _ ihx ihy => rw [← mul_assoc, ihy, ihx]
    | inv x _ ihx => rw [← ihx (a * x⁻¹), inv_mul_cancel_right]
  have e := orbit g (g⁻¹ * g') hx
  rw [mul_inv_cancel_left] at e
  have h := congrArg (X.readK U) e.symm
  simpa only [GaloisConstituentModel.FK, X.tK_mk, X.readK_mk] using h

/-- One instance of the fixed-set consumer, on two prescribed fresh primes. -/
theorem fixedU_at (X : GaloisConstituentModel T R ap B χ) (htyp : IsTypeChar T χ)
    {U : Finset ℕ} (hU : ∀ s ∈ U, T.Good s) (hB : U.card + 1 ≤ B)
    {q q' : ℕ} (hq : T.Good q) (hq' : T.Good q') (hqU : q ∉ U) (hq'U : q' ∉ U)
    (hread : FreshAt X U q) (hread' : FreshAt X U q')
    (ht : T.typ q = T.typ q') (hb : ∀ s ∈ U, legBit q s = legBit q' s) :
    R (insert q U) = R (insert q' U) := by
  rw [FreshAt] at hread hread'
  rw [hread, hread']
  apply traceRead_eq_of_labels X hU hB
  · rw [X.typ_frob htyp q hq, X.typ_frob htyp q' hq', ht]
  · intro s hs
    rw [X.bit_frob q s hq (hU s hs) (fun e => hqU (e ▸ hs)),
      X.bit_frob q' s hq' (hU s hs) (fun e => hq'U (e ▸ hs)), hb s hs]

/-- The same fixed-set orbit gives the dictionary's primary reading. -/
theorem primary_at (X : GaloisConstituentModel T R ap B χ) (htyp : IsTypeChar T χ)
    {U : Finset ℕ} (hU : ∀ s ∈ U, T.Good s) (hB : U.card + 1 ≤ B)
    {q : ℕ} (hq : T.Good q) (hqU : q ∉ U) (hread : FreshAt X U q)
    (ht : T.typ q = 0) (hb : ∀ s ∈ U, legBit q s = 0) :
    R (insert q U) = 0 := by
  rw [FreshAt] at hread
  rw [hread]
  have e : traceRead X U (X.frob q) = traceRead X U 1 := by
    apply traceRead_eq_of_labels X hU hB
    · rw [X.typ_frob htyp q hq, ht, ofAdd_zero, map_one]
    · intro s hs
      rw [X.bit_frob q s hq (hU s hs) (fun e => hqU (e ▸ hs)), hb s hs, ofAdd_zero, map_one]
  rw [e]
  let inst := X.modMst
  have h := congrArg (X.readK U) (X.trace_one (X.FK U))
  simpa only [show (2 : ZMod 2) = 0 from rfl, zero_smul, map_zero,
    GaloisConstituentModel.FK, X.tK_mk, X.readK_mk] using h

/-- The exact dictionary input used by `Rules.symb_contraction`. No global
constituent model and no formula at an excluded prime are needed. -/
theorem o12_of_windows (htyp : IsTypeChar T χ)
    (windows : ∀ U, (∀ s ∈ U, T.Good s) → U.card + 1 ≤ B →
      ∃ (X : GaloisConstituentModel T R ap B χ) (avoid : Finset ℕ), ReadingsOn X U avoid) :
    O12Reading T R ap B := by
  intro U p hpU hU hB ℓ bq
  obtain ⟨X, avoid, h⟩ := windows U hU hB
  exact o12_at X htyp h p hpU hU hB ℓ bq

/-- The prescribed prime comparisons have no ambient avoidance guard.
For each root, the readings used in both conclusions are in its own space. -/
theorem fixedU_primary_of_windows (htyp : IsTypeChar T χ)
    (windows : ∀ U, (∀ s ∈ U, T.Good s) → U.card + 1 ≤ B →
      ∃ X : GaloisConstituentModel T R ap B χ, ∀ q, T.Good q → q ∉ U → FreshAt X U q) :
    FixedUFactorization T R B ∧ PrimaryReading T R B := by
  constructor
  · intro U q q' hc hU hq hq' hqU hq'U ht hb
    have hB : U.card + 1 ≤ B := by rwa [card_insert_of_notMem hqU] at hc
    obtain ⟨X, h⟩ := windows U hU hB
    exact fixedU_at X htyp hU hB hq hq' hqU hq'U (h q hq hqU) (h q' hq' hq'U) ht hb
  · intro U q hU hq hqU hc ht hb
    have hB : U.card + 1 ≤ B := by rwa [card_insert_of_notMem hqU] at hc
    obtain ⟨X, h⟩ := windows U hU hB
    exact primary_at X htyp hU hB hq hqU (h q hq hqU) ht hb

/-- Feed the existing dictionary with the exact three readings at the odd
budget. The coefficient parity is the existing elliptic-curve input. -/
theorem rulesUpTo_of_windows {W : ℕ} (htyp : IsTypeChar T χ) (hap : ApEven T ap)
    (omissionWindows : ∀ U, (∀ s ∈ U, T.Good s) → U.card + 1 ≤ W + 1 →
      ∃ (X : GaloisConstituentModel T R ap (W + 1) χ) (avoid : Finset ℕ), ReadingsOn X U avoid)
    (rootWindows : ∀ U, (∀ s ∈ U, T.Good s) → U.card + 1 ≤ W + 1 →
      ∃ X : GaloisConstituentModel T R ap (W + 1) χ, ∀ q, T.Good q → q ∉ U → FreshAt X U q) :
    RulesUpTo ε (symb T R) W := by
  obtain ⟨hswap, hprim⟩ := fixedU_primary_of_windows htyp rootWindows
  exact rulesUpTo_symb T R ap W hswap (o12_of_windows htyp omissionWindows) hap hprim

end ZInQ.Manuscript.RC.O12Realize

#print axioms ZInQ.Manuscript.RC.O12Realize.o12_at
#print axioms ZInQ.Manuscript.RC.O12Realize.traceRead_eq_of_labels
#print axioms ZInQ.Manuscript.RC.O12Realize.fixedU_at
#print axioms ZInQ.Manuscript.RC.O12Realize.primary_at
#print axioms ZInQ.Manuscript.RC.O12Realize.o12_of_windows
#print axioms ZInQ.Manuscript.RC.O12Realize.fixedU_primary_of_windows
#print axioms ZInQ.Manuscript.RC.O12Realize.rulesUpTo_of_windows

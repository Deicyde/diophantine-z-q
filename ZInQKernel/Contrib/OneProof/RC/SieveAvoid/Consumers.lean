import ZInQKernel.Contrib.OneProof.RC.SieveAvoid.Hecke
import ZInQKernel.Contrib.OneProof.RC.O12Realize.Stage

/-! Pass the fresh domain through the dictionary ports without changing
the type, the Frobenius labels, or the coefficient identities. -/

noncomputable section

namespace ZInQ.Manuscript.RC.SieveAvoid

open O12Realize O12 AddressGenuine PrintsArith Symbols Finset
open ZInQ.Manuscript.RC.Odd
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2} {T : TypeData L ε}
variable {χ : GalQ →* Multiplicative L} {R : Finset ℕ → ZMod 2} {ap : ℕ → ℤ} {B : ℕ}

/-- Omission with an actual root and four representatives outside the
coefficient support (tex 9919–9945). -/
def O12Reading' (T : TypeData L ε) (R : Finset ℕ → ZMod 2) (ap : ℕ → ℤ)
    (B : ℕ) (Scoeff : Finset ℕ) : Prop :=
  ∀ (U : Finset ℕ) (p : ℕ), p ∈ U → GoodSet T Scoeff U → U.card + 1 ≤ B →
    ∀ (ℓ : L) (bq : ℕ → ZMod 2),
    ∃ (q qτ r0 r1 : ℕ) (κ : ℤ),
      T.Good q ∧ T.Good qτ ∧ T.Good r0 ∧ T.Good r1 ∧ q ∉ Scoeff ∪ U ∧ qτ ∉ Scoeff ∪ U ∧
      r0 ∉ Scoeff ∪ U ∧ r1 ∉ Scoeff ∪ U ∧
      T.typ q = ℓ ∧ T.typ qτ = ℓ ∧ (∀ s ∈ U, legBit q s = bq s) ∧
      (∀ s ∈ U, s ≠ p → legBit qτ s = bq s) ∧ legBit qτ p = bq p + 1 ∧
      T.typ r0 = T.typ p + ℓ ∧ T.typ r1 = T.typ p + ℓ ∧
      (∀ s ∈ U, s ≠ p → legBit r0 s = legBit p s + bq s ∧ legBit r1 s = legBit p s + bq s) ∧
      legBit r1 p = legBit r0 p + 1 ∧ (κ = 1 ∨ κ = -1) ∧
      (Cp (ap p) (-κ) : ZMod 2) * R (insert r1 (U.erase p)) -
        (Cp (ap p) κ : ZMod 2) * R (insert r0 (U.erase p)) =
      R (insert qτ U) - R (insert q U)

/-- Product labels in the precise shape of the existing dictionary input,
at one fixed root. All representatives are selected outside `U ∪ (Scoeff ∪ avoid)`. -/
theorem o12_at' (X : GaloisConstituentModel T R ap B χ) (htyp : IsTypeChar T χ)
    {U Scoeff avoid : Finset ℕ} (h : ReadingsOn X U (Scoeff ∪ avoid))
    (p : ℕ) (hpU : p ∈ U) (hU : GoodSet T Scoeff U) (hB : U.card + 1 ≤ B)
    (ℓ : L) (bq : ℕ → ZMod 2) :
    ∃ (q qτ r0 r1 : ℕ) (κ : ℤ),
      T.Good q ∧ T.Good qτ ∧ T.Good r0 ∧ T.Good r1 ∧ q ∉ Scoeff ∪ U ∧ qτ ∉ Scoeff ∪ U ∧
      r0 ∉ Scoeff ∪ U ∧ r1 ∉ Scoeff ∪ U ∧
      T.typ q = ℓ ∧ T.typ qτ = ℓ ∧ (∀ s ∈ U, legBit q s = bq s) ∧
      (∀ s ∈ U, s ≠ p → legBit qτ s = bq s) ∧ legBit qτ p = bq p + 1 ∧
      T.typ r0 = T.typ p + ℓ ∧ T.typ r1 = T.typ p + ℓ ∧
      (∀ s ∈ U, s ≠ p → legBit r0 s = legBit p s + bq s ∧ legBit r1 s = legBit p s + bq s) ∧
      legBit r1 p = legBit r0 p + 1 ∧ (κ = 1 ∨ κ = -1) ∧
      (Cp (ap p) (-κ) : ZMod 2) * R (insert r1 (U.erase p)) -
        (Cp (ap p) κ : ZMod 2) * R (insert r0 (U.erase p)) =
      R (insert qτ U) - R (insert q U) := by
  have hUg : ∀ s ∈ U, T.Good s := fun s hs => (hU s hs).1
  obtain ⟨g, hgT, hgB⟩ := X.chi_surj htyp U hUg ℓ bq
  obtain ⟨τ, φ, κ, hκ, hτT, hτB, hτp, hφT, hφB, hO⟩ := h.omission p hpU g
  have rep (y : GalQ) :
      ∃ q, T.Good q ∧ q ∉ Scoeff ∪ U ∧ Multiplicative.ofAdd (T.typ q) = χ y ∧
        (∀ s ∈ U, Multiplicative.ofAdd (legBit q s) = bitChar s y) ∧
        ∀ V ⊆ U, R (insert q V) = traceRead X V y := by
    obtain ⟨q, j, n, hn, hq, hqa, hqf⟩ := X.chebotarev U hUg hB y (U ∪ (Scoeff ∪ avoid))
    have hqU : q ∉ U := fun hq' => hqa (mem_union_left _ hq')
    have hqfsh : q ∉ Scoeff ∪ U := by
      intro e
      rcases mem_union.mp e with hqS | hq'
      · exact hqa (mem_union_right _ (mem_union_left _ hqS))
      · exact hqU hq'
    refine ⟨q, hq, hqfsh, ?_, ?_, ?_⟩
    · rw [← X.typ_frob htyp q hq, hqf, map_mul, (X.N_chi U n hn).1, mul_one, map_conj_of_comm]
    · intro s hs
      rw [← X.bit_frob q s hq (hUg s hs) (fun e => hqU (e ▸ hs))]
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

/-- The fixed-set equality on prescribed allowed primes (tex 2108–2112,
9745–9750). -/
def FixedUFactorization' (T : TypeData L ε) (R : Finset ℕ → ZMod 2) (B : ℕ)
    (Scoeff : Finset ℕ) : Prop :=
  ∀ (U : Finset ℕ) (q q' : ℕ), (insert q U).card ≤ B → GoodSet T Scoeff U →
    T.Good q → T.Good q' → q ∉ Scoeff ∪ U → q' ∉ Scoeff ∪ U →
    T.typ q = T.typ q' → (∀ s ∈ U, legBit q s = legBit q' s) →
    R (insert q U) = R (insert q' U)

/-- The primary reading on a prescribed allowed prime (tex 9947–9952). -/
def PrimaryReading' (T : TypeData L ε) (R : Finset ℕ → ZMod 2) (B : ℕ)
    (Scoeff : Finset ℕ) : Prop :=
  ∀ (U : Finset ℕ) (q : ℕ), GoodSet T Scoeff U → T.Good q → q ∉ Scoeff ∪ U →
    (insert q U).card ≤ B → T.typ q = 0 → (∀ s ∈ U, legBit q s = 0) →
    R (insert q U) = 0

theorem o12_of_windows' {Scoeff : Finset ℕ} (htyp : IsTypeChar T χ)
    (windows : ∀ U, GoodSet T Scoeff U → U.card + 1 ≤ B →
      ∃ (X : GaloisConstituentModel T R ap B χ) (avoid : Finset ℕ),
        ReadingsOn X U (Scoeff ∪ avoid)) :
    O12Reading' T R ap B Scoeff := by
  intro U p hpU hU hB ℓ bq
  obtain ⟨X, avoid, h⟩ := windows U hU hB
  exact o12_at' X htyp h p hpU hU hB ℓ bq

theorem fixedU_primary_of_windows' {Scoeff : Finset ℕ} (htyp : IsTypeChar T χ)
    (windows : ∀ U, GoodSet T Scoeff U → U.card + 1 ≤ B →
      ∃ X : GaloisConstituentModel T R ap B χ,
        ∀ q, T.Good q → q ∉ Scoeff ∪ U → FreshAt X U q) :
    FixedUFactorization' T R B Scoeff ∧ PrimaryReading' T R B Scoeff := by
  constructor
  · intro U q q' hc hU hq hq' hqf hq'f ht hb
    have hqU : q ∉ U := fun h => hqf (mem_union_right _ h)
    have hq'U : q' ∉ U := fun h => hq'f (mem_union_right _ h)
    have hB : U.card + 1 ≤ B := by rwa [card_insert_of_notMem hqU] at hc
    obtain ⟨X, h⟩ := windows U hU hB
    exact fixedU_at X htyp (fun s hs => (hU s hs).1) hB hq hq' hqU hq'U
      (h q hq hqf) (h q' hq' hq'f) ht hb
  · intro U q hU hq hqf hc ht hb
    have hqU : q ∉ U := fun h => hqf (mem_union_right _ h)
    have hB : U.card + 1 ≤ B := by rwa [card_insert_of_notMem hqU] at hc
    obtain ⟨X, h⟩ := windows U hU hB
    exact primary_at X htyp (fun s hs => (hU s hs).1) hB hq hqU (h q hq hqf) ht hb

/-- The two constituent inputs with the same coefficient identities on the
actual tested domain. -/
def Inputs' (X : GaloisConstituentModel T R ap B χ) (Scoeff : Finset ℕ) : Prop :=
  (∀ U q, GoodSet T Scoeff U → T.Good q → q ∉ Scoeff ∪ U →
    (insert q U).card ≤ B → FreshAt X U q) ∧
  (∀ U p, p ∈ U → GoodSet T Scoeff U → U.card + 1 ≤ B → OmissionAt X U p)

#print axioms o12_at'
#print axioms o12_of_windows'
#print axioms fixedU_primary_of_windows'

end ZInQ.Manuscript.RC.SieveAvoid

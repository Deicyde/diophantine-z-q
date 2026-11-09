import ZInQKernel.RouteK.Slots.Dirichlet
import ZInQKernel.RouteK.Slots.Multiplier
import ZInQKernel.RouteK.Slots.Theta

/-!
# Route K slots: the slots `q₀`, `r_p`, `r_ℓ` (lemma L3)

`docs/research/slot-k.md` §2.4. Let `P` be the set of primes of `β` (odd), `T` the set of primes
of `θ` (odd, disjoint from `P`), `p₀ ∈ P`, `s = [β < 0]` and `x = s + 1 ∈ 𝔽₂`. The slots are

- a prime `q₀ ≡ 3 (mod 8)`, `q₀ ∤ 2βθ`, with `[q₀/p] = 1 + λ_p x` for `p ∈ P ∖ {p₀}`,
  `[q₀/p₀] = x + Σ_{p ∈ P∖{p₀}} (1 + λ_p x)` and `[q₀/ℓ] = 0` for `ℓ ∈ T`;
- primes `r_p ≡ 1 (mod 8)` for `p ∈ P ∖ {p₀}` with `[r_p/p] = [r_p/p₀] = 1` and `[r_p/y] = 0` for
  `y ∈ (P ∖ {p, p₀}) ∪ T ∪ {q₀}` and for the other `r_{p'}`;
- primes `r_ℓ ≡ 1 (mod 8)` for `ℓ ∈ T` with `[r_ℓ/ℓ] = [r_ℓ/q₀] = 1` and `[r_ℓ/y] = 0` for
  `y ∈ P ∪ (T ∖ {ℓ})`, for all `r_p` and for the other `r_{ℓ'}`;

all pairwise distinct and prime to `2βθ`. The note chooses the glue slots "one after the other",
imposing `[r/r'] = 0` only against the earlier `r'`; since glue slots are `≡ 1 (mod 4)`,
reciprocity makes these conditions symmetric, and `Slots` records them for all pairs. The reverse
symbols `[y/slot]` are then fixed by reciprocity (`Slots.rev_rP`, `Slots.rev_rT`,
`Slots.rev_q₀`). The referee report (rv-slot-k-proof, finding 1) notes that the condition
`[q₀/ℓ] = 0` is never used by the proof of DL; it is kept here because the note imposes it.
-/

namespace ZInQ.RouteK

open scoped BigOperators

/-- The set `P` of primes of `β`. -/
def primesOf (β : ℤ) : Finset ℕ := β.natAbs.primeFactors

/-- `s = [β < 0] ∈ 𝔽₂`. -/
def signBit (β : ℤ) : ZMod 2 := if β < 0 then 1 else 0

/-- The slot data of slot-k §2.4 for `β`, `θ` and the distinguished prime `p₀ ∈ P`, with
`P = primesOf β`, `T = primesOf θ`, `G = P ∖ {p₀}` and `x = signBit β + 1`. -/
structure Slots (β θ : ℤ) (p₀ : ℕ) where
  /-- The symmetry-breaking slot `q₀`. -/
  q₀ : ℕ
  /-- The glue slots `r_p`, `p ∈ P ∖ {p₀}`. -/
  rP : ℕ → ℕ
  /-- The glue slots `r_ℓ`, `ℓ ∈ T`. -/
  rT : ℕ → ℕ
  q₀_prime : q₀.Prime
  q₀_mod_eight : q₀ % 8 = 3
  q₀_not_dvd : ¬ (q₀ : ℤ) ∣ 2 * β * θ
  q₀_sym_P : ∀ p ∈ primesOf β \ {p₀}, legBit p q₀ = 1 + lamBit p * (signBit β + 1)
  q₀_sym_p₀ : legBit p₀ q₀ =
    (signBit β + 1) + ∑ p ∈ primesOf β \ {p₀}, (1 + lamBit p * (signBit β + 1))
  q₀_sym_T : ∀ ℓ ∈ primesOf θ, legBit ℓ q₀ = 0
  rP_prime : ∀ p ∈ primesOf β \ {p₀}, (rP p).Prime
  rP_mod_eight : ∀ p ∈ primesOf β \ {p₀}, rP p % 8 = 1
  rP_not_dvd : ∀ p ∈ primesOf β \ {p₀}, ¬ (rP p : ℤ) ∣ 2 * β * θ
  rP_ne_q₀ : ∀ p ∈ primesOf β \ {p₀}, rP p ≠ q₀
  rP_injOn : Set.InjOn rP ↑(primesOf β \ {p₀})
  rP_sym_self : ∀ p ∈ primesOf β \ {p₀}, legBit p (rP p) = 1
  rP_sym_p₀ : ∀ p ∈ primesOf β \ {p₀}, legBit p₀ (rP p) = 1
  rP_sym_P : ∀ p ∈ primesOf β \ {p₀}, ∀ y ∈ primesOf β, y ≠ p → y ≠ p₀ → legBit y (rP p) = 0
  rP_sym_T : ∀ p ∈ primesOf β \ {p₀}, ∀ ℓ ∈ primesOf θ, legBit ℓ (rP p) = 0
  rP_sym_q₀ : ∀ p ∈ primesOf β \ {p₀}, legBit q₀ (rP p) = 0
  rP_sym_rP : ∀ p ∈ primesOf β \ {p₀}, ∀ p' ∈ primesOf β \ {p₀}, p' ≠ p →
    legBit (rP p') (rP p) = 0
  rT_prime : ∀ ℓ ∈ primesOf θ, (rT ℓ).Prime
  rT_mod_eight : ∀ ℓ ∈ primesOf θ, rT ℓ % 8 = 1
  rT_not_dvd : ∀ ℓ ∈ primesOf θ, ¬ (rT ℓ : ℤ) ∣ 2 * β * θ
  rT_ne_q₀ : ∀ ℓ ∈ primesOf θ, rT ℓ ≠ q₀
  rT_ne_rP : ∀ ℓ ∈ primesOf θ, ∀ p ∈ primesOf β \ {p₀}, rT ℓ ≠ rP p
  rT_injOn : Set.InjOn rT ↑(primesOf θ)
  rT_sym_self : ∀ ℓ ∈ primesOf θ, legBit ℓ (rT ℓ) = 1
  rT_sym_q₀ : ∀ ℓ ∈ primesOf θ, legBit q₀ (rT ℓ) = 1
  rT_sym_P : ∀ ℓ ∈ primesOf θ, ∀ p ∈ primesOf β, legBit p (rT ℓ) = 0
  rT_sym_T : ∀ ℓ ∈ primesOf θ, ∀ ℓ' ∈ primesOf θ, ℓ' ≠ ℓ → legBit ℓ' (rT ℓ) = 0
  rT_sym_rP : ∀ ℓ ∈ primesOf θ, ∀ p ∈ primesOf β \ {p₀}, legBit (rP p) (rT ℓ) = 0
  rT_sym_rT : ∀ ℓ ∈ primesOf θ, ∀ ℓ' ∈ primesOf θ, ℓ' ≠ ℓ → legBit (rT ℓ') (rT ℓ) = 0

theorem mem_primesOf {β : ℤ} {p : ℕ} : p ∈ primesOf β ↔ p.Prime ∧ (p : ℤ) ∣ β ∧ β ≠ 0 := by
  rw [primesOf, Nat.mem_primeFactors, Int.natAbs_ne_zero, ← Int.natCast_dvd]

theorem odd_of_mem_primesOf {β : ℤ} (hβ : Odd β) {p : ℕ} (hp : p ∈ primesOf β) :
    p.Prime ∧ p ≠ 2 := by
  obtain ⟨hpp, hd, -⟩ := mem_primesOf.mp hp
  refine ⟨hpp, fun h => ?_⟩
  subst h
  exact (Int.not_even_iff_odd.mpr hβ) (even_iff_two_dvd.mpr (by exact_mod_cast hd))

/-- For squarefree `β`, `|β| = ∏_{p ∈ P} p`. -/
theorem natAbs_eq_prod_primesOf {β : ℤ} (hβ : Squarefree β) :
    ((β.natAbs : ℕ) : ℤ) = ∏ p ∈ primesOf β, (p : ℤ) := by
  rw [primesOf, ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree
    (Int.squarefree_natAbs.mpr hβ)]

/-- A prime outside `{2} ∪ P ∪ T` does not divide `2βθ`. -/
theorem not_dvd_two_mul_of_not_mem {β θ : ℤ} (hβ : β ≠ 0) (hθ : θ ≠ 0) {q : ℕ} (hq : q.Prime)
    (h2 : q ≠ 2) (hP : q ∉ primesOf β) (hT : q ∉ primesOf θ) : ¬ (q : ℤ) ∣ 2 * β * θ := by
  have hqZ : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  intro hd
  rcases hqZ.dvd_or_dvd hd with hd | hd
  · rcases hqZ.dvd_or_dvd hd with hd | hd
    · exact h2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (by exact_mod_cast hd))
    · exact hP (mem_primesOf.mpr ⟨hq, hd, hβ⟩)
  · exact hT (mem_primesOf.mpr ⟨hq, hd, hθ⟩)

theorem nat_mod_eight_of_modEq {q : ℕ} {a : ℕ} (h : (q : ℤ) ≡ a [ZMOD 8]) (ha : a < 8) :
    q % 8 = a := by
  have := Int.natCast_modEq_iff.mp
    (by exact_mod_cast h : ((q : ℕ) : ℤ) ≡ ((a : ℕ) : ℤ) [ZMOD ((8 : ℕ) : ℤ)])
  rw [Nat.ModEq, Nat.mod_eq_of_lt ha] at this
  exact this

/-- **Glue family**: given a finite set `S` of odd primes and for each index `i ∈ I` prescribed bits
`b i y` at the `y ∈ S`, there are primes `r i ≡ 1 (mod 8)`, distinct, outside `S ∪ A`, with
`[r i/y] = b i y` for `y ∈ S` and `[r j/r i] = 0` for `i ≠ j`. (Chosen one after the other; the
symbol between two glue primes is symmetric by reciprocity.) -/
theorem exists_glue_family (S : Finset ℕ) (hS : ∀ y ∈ S, y.Prime ∧ y ≠ 2) (I : Finset ℕ)
    (b : ℕ → ℕ → ZMod 2) (A : Finset ℕ) :
    ∃ r : ℕ → ℕ, (∀ i ∈ I, (r i).Prime ∧ r i % 8 = 1 ∧ r i ∉ A ∧ r i ∉ S ∧
        ∀ y ∈ S, legBit y (r i) = b i y) ∧
      Set.InjOn r ↑I ∧ ∀ i ∈ I, ∀ j ∈ I, i ≠ j → legBit (r j) (r i) = 0 := by
  classical
  induction I using Finset.induction_on with
  | empty => exact ⟨id, by simp, by simp, by simp⟩
  | @insert i₀ I hi₀ ih =>
    obtain ⟨r, hr, hinj, hsym⟩ := ih
    have hS' : ∀ y ∈ S ∪ I.image r, y.Prime ∧ y ≠ 2 := by
      intro y hy
      rcases Finset.mem_union.mp hy with hy | hy
      · exact hS y hy
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
        exact ⟨(hr j hj).1, fun h => by have := (hr j hj).2.1; omega⟩
    obtain ⟨r₀, hr₀, hr₀A, hr₀S, hr₀8, hr₀b⟩ := exists_prime_slot_bits (S ∪ I.image r) hS'
      (fun y => if y ∈ S then b i₀ y else 0) (a := 1) odd_one A
    have hr₀8' : r₀ % 8 = 1 := nat_mod_eight_of_modEq (by exact_mod_cast hr₀8) (by norm_num)
    have hr₀ne : ∀ j ∈ I, r j ≠ r₀ := fun j hj h =>
      hr₀S (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, hj, h⟩))
    -- the new prime against the old ones, in both directions
    have hnew : ∀ j ∈ I, legBit (r j) r₀ = 0 := fun j hj => by
      have := hr₀b (r j) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, hj, rfl⟩))
      simpa [(hr j hj).2.2.2.1] using this
    have hold : ∀ j ∈ I, legBit r₀ (r j) = 0 := fun j hj => by
      rw [legBit_symm_of_one_mod_four hr₀ (hr j hj).1
        (fun h => by have := (hr j hj).2.1; omega) (Ne.symm (hr₀ne j hj)) (by omega)]
      exact hnew j hj
    refine ⟨fun i => if i = i₀ then r₀ else r i, ?_, ?_, ?_⟩
    · intro i hi
      by_cases h : i = i₀
      · subst h
        simp only [ite_true]
        refine ⟨hr₀, hr₀8', hr₀A, fun h => hr₀S (Finset.mem_union_left _ h), fun y hy => ?_⟩
        have := hr₀b y (Finset.mem_union_left _ hy)
        simpa [hy] using this
      · simp only [h, ite_false]
        exact hr i ((Finset.mem_insert.mp hi).resolve_left h)
    · intro i hi j hj hij
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hi hj
      by_cases h1 : i = i₀ <;> by_cases h2 : j = i₀ <;>
        simp only [h1, h2, ite_true, ite_false] at hij
      · rw [h1, h2]
      · exact absurd hij.symm (hr₀ne j (hj.resolve_left h2))
      · exact absurd hij (hr₀ne i (hi.resolve_left h1))
      · exact hinj (hi.resolve_left h1) (hj.resolve_left h2) hij
    · intro i hi j hj hij
      by_cases h1 : i = i₀ <;> by_cases h2 : j = i₀ <;> simp only [h1, h2, ite_true, ite_false]
      · exact absurd (h1.trans h2.symm) hij
      · exact hnew j ((Finset.mem_insert.mp hj).resolve_left h2)
      · exact hold i ((Finset.mem_insert.mp hi).resolve_left h1)
      · exact hsym i ((Finset.mem_insert.mp hi).resolve_left h1) j
          ((Finset.mem_insert.mp hj).resolve_left h2) hij

/-- **L3** (slot-k §2.4): for odd coprime `β`, `θ` and any `p₀ ∈ P`, the slots `q₀`, `r_p`
(`p ∈ P ∖ {p₀}`) and `r_ℓ` (`ℓ ∈ T`) exist. -/
theorem exists_slots {β θ : ℤ} (hβ : Odd β) (hθ : Odd θ) (hcop : IsCoprime β θ) {p₀ : ℕ}
    (hp₀ : p₀ ∈ primesOf β) : Nonempty (Slots β θ p₀) := by
  classical
  have hβ0 : β ≠ 0 := by rintro rfl; exact (Int.not_even_iff_odd.mpr hβ) (by decide)
  have hθ0 : θ ≠ 0 := by rintro rfl; exact (Int.not_even_iff_odd.mpr hθ) (by decide)
  have hPodd := fun p (hp : p ∈ primesOf β) => odd_of_mem_primesOf hβ hp
  have hTodd := fun p (hp : p ∈ primesOf θ) => odd_of_mem_primesOf hθ hp
  have hdisj : ∀ p ∈ primesOf β, p ∉ primesOf θ := by
    intro p hp hpT
    obtain ⟨hpp, hd1, -⟩ := mem_primesOf.mp hp
    obtain ⟨-, hd2, -⟩ := mem_primesOf.mp hpT
    exact (Nat.prime_iff_prime_int.mp hpp).not_isUnit (hcop.isUnit_of_dvd' hd1 hd2)
  have hG : ∀ {p}, p ∈ primesOf β \ {p₀} → p ∈ primesOf β ∧ p ≠ p₀ := fun hp => by
    simpa using hp
  -- the slot `q₀`
  obtain ⟨q₀, hq₀, -, hq₀S, hq₀8, hq₀b⟩ := exists_prime_slot_bits (primesOf β ∪ primesOf θ)
    (fun y hy => (Finset.mem_union.mp hy).elim (hPodd y) (hTodd y))
    (fun y => if y ∈ primesOf θ then 0 else if y = p₀ then
      (signBit β + 1) + ∑ p ∈ primesOf β \ {p₀}, (1 + lamBit p * (signBit β + 1))
      else 1 + lamBit y * (signBit β + 1)) (a := 3) (by decide) ∅
  have hq₀8' : q₀ % 8 = 3 := nat_mod_eight_of_modEq (by exact_mod_cast hq₀8) (by norm_num)
  have hq₀2 : q₀ ≠ 2 := by omega
  have hq₀P : q₀ ∉ primesOf β := fun h => hq₀S (Finset.mem_union_left _ h)
  have hq₀T : q₀ ∉ primesOf θ := fun h => hq₀S (Finset.mem_union_right _ h)
  -- the slots `r_p`
  have hS₁ : ∀ y ∈ primesOf β ∪ primesOf θ ∪ {q₀}, y.Prime ∧ y ≠ 2 := by
    intro y hy
    rcases Finset.mem_union.mp hy with hy | hy
    · exact (Finset.mem_union.mp hy).elim (hPodd y) (hTodd y)
    · rw [Finset.mem_singleton.mp hy]; exact ⟨hq₀, hq₀2⟩
  obtain ⟨rP, hrP, hrPinj, hrPsym⟩ := exists_glue_family _ hS₁ (primesOf β \ {p₀})
    (fun p y => if y = p ∨ y = p₀ then 1 else 0) ∅
  have hrP2 : ∀ p ∈ primesOf β \ {p₀}, rP p ≠ 2 := fun p hp h => by
    have := (hrP p hp).2.1; omega
  have hrPS : ∀ p ∈ primesOf β \ {p₀}, rP p ∉ primesOf β ∧ rP p ∉ primesOf θ ∧ rP p ≠ q₀ :=
    fun p hp => by
      have := (hrP p hp).2.2.2.1
      simp only [Finset.mem_union, Finset.mem_singleton, not_or] at this
      exact ⟨this.1.1, this.1.2, this.2⟩
  -- the slots `r_ℓ`
  have hS₂ : ∀ y ∈ primesOf β ∪ primesOf θ ∪ {q₀} ∪ (primesOf β \ {p₀}).image rP,
      y.Prime ∧ y ≠ 2 := by
    intro y hy
    rcases Finset.mem_union.mp hy with hy | hy
    · exact hS₁ y hy
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
      exact ⟨(hrP p hp).1, hrP2 p hp⟩
  obtain ⟨rT, hrT, hrTinj, hrTsym⟩ := exists_glue_family _ hS₂ (primesOf θ)
    (fun ℓ y => if y = ℓ ∨ y = q₀ then 1 else 0) ∅
  have hrT2 : ∀ ℓ ∈ primesOf θ, rT ℓ ≠ 2 := fun ℓ hℓ h => by
    have := (hrT ℓ hℓ).2.1; omega
  have hrTS : ∀ ℓ ∈ primesOf θ, rT ℓ ∉ primesOf β ∧ rT ℓ ∉ primesOf θ ∧ rT ℓ ≠ q₀ ∧
      ∀ p ∈ primesOf β \ {p₀}, rT ℓ ≠ rP p := fun ℓ hℓ => by
    have := (hrT ℓ hℓ).2.2.2.1
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_image, not_or,
      not_exists, not_and] at this
    exact ⟨this.1.1.1, this.1.1.2, this.1.2, fun p hp h => this.2 p hp h.symm⟩
  have mS₁ : ∀ {y}, y ∈ primesOf β ∨ y ∈ primesOf θ ∨ y = q₀ →
      y ∈ primesOf β ∪ primesOf θ ∪ {q₀} := fun h => by
    simp only [Finset.mem_union, Finset.mem_singleton]; tauto
  have mS₂ : ∀ {y}, y ∈ primesOf β ∪ primesOf θ ∪ {q₀} →
      y ∈ primesOf β ∪ primesOf θ ∪ {q₀} ∪ (primesOf β \ {p₀}).image rP :=
    fun h => Finset.mem_union_left _ h
  exact ⟨{
    q₀ := q₀
    rP := rP
    rT := rT
    q₀_prime := hq₀
    q₀_mod_eight := hq₀8'
    q₀_not_dvd := not_dvd_two_mul_of_not_mem hβ0 hθ0 hq₀ hq₀2 hq₀P hq₀T
    q₀_sym_P := fun p hp => by
      have := hq₀b p (Finset.mem_union_left _ (hG hp).1)
      simpa [hdisj p (hG hp).1, (hG hp).2] using this
    q₀_sym_p₀ := by
      have := hq₀b p₀ (Finset.mem_union_left _ hp₀)
      simpa [hdisj p₀ hp₀] using this
    q₀_sym_T := fun ℓ hℓ => by
      have := hq₀b ℓ (Finset.mem_union_right _ hℓ)
      simpa [hℓ] using this
    rP_prime := fun p hp => (hrP p hp).1
    rP_mod_eight := fun p hp => (hrP p hp).2.1
    rP_not_dvd := fun p hp => not_dvd_two_mul_of_not_mem hβ0 hθ0 (hrP p hp).1 (hrP2 p hp)
      (hrPS p hp).1 (hrPS p hp).2.1
    rP_ne_q₀ := fun p hp => (hrPS p hp).2.2
    rP_injOn := hrPinj
    rP_sym_self := fun p hp => by
      simpa using (hrP p hp).2.2.2.2 p (mS₁ (Or.inl (hG hp).1))
    rP_sym_p₀ := fun p hp => by
      simpa using (hrP p hp).2.2.2.2 p₀ (mS₁ (Or.inl hp₀))
    rP_sym_P := fun p hp y hy hyp hyp₀ => by
      simpa [hyp, hyp₀] using (hrP p hp).2.2.2.2 y (mS₁ (Or.inl hy))
    rP_sym_T := fun p hp ℓ hℓ => by
      have h1 : ℓ ≠ p := fun h => hdisj p (hG hp).1 (h ▸ hℓ)
      have h2 : ℓ ≠ p₀ := fun h => hdisj p₀ hp₀ (h ▸ hℓ)
      simpa [h1, h2] using (hrP p hp).2.2.2.2 ℓ (mS₁ (Or.inr (Or.inl hℓ)))
    rP_sym_q₀ := fun p hp => by
      have h1 : q₀ ≠ p := fun h => hq₀P (h ▸ (hG hp).1)
      have h2 : q₀ ≠ p₀ := fun h => hq₀P (h ▸ hp₀)
      simpa [h1, h2] using (hrP p hp).2.2.2.2 q₀ (mS₁ (Or.inr (Or.inr rfl)))
    rP_sym_rP := fun p hp p' hp' hne => hrPsym p hp p' hp' (Ne.symm hne)
    rT_prime := fun ℓ hℓ => (hrT ℓ hℓ).1
    rT_mod_eight := fun ℓ hℓ => (hrT ℓ hℓ).2.1
    rT_not_dvd := fun ℓ hℓ => not_dvd_two_mul_of_not_mem hβ0 hθ0 (hrT ℓ hℓ).1 (hrT2 ℓ hℓ)
      (hrTS ℓ hℓ).1 (hrTS ℓ hℓ).2.1
    rT_ne_q₀ := fun ℓ hℓ => (hrTS ℓ hℓ).2.2.1
    rT_ne_rP := fun ℓ hℓ => (hrTS ℓ hℓ).2.2.2
    rT_injOn := hrTinj
    rT_sym_self := fun ℓ hℓ => by
      simpa using (hrT ℓ hℓ).2.2.2.2 ℓ (mS₂ (mS₁ (Or.inr (Or.inl hℓ))))
    rT_sym_q₀ := fun ℓ hℓ => by
      simpa using (hrT ℓ hℓ).2.2.2.2 q₀ (mS₂ (mS₁ (Or.inr (Or.inr rfl))))
    rT_sym_P := fun ℓ hℓ p hp => by
      have h1 : p ≠ ℓ := fun h => hdisj p hp (h ▸ hℓ)
      have h2 : p ≠ q₀ := fun h => hq₀P (h ▸ hp)
      simpa [h1, h2] using (hrT ℓ hℓ).2.2.2.2 p (mS₂ (mS₁ (Or.inl hp)))
    rT_sym_T := fun ℓ hℓ ℓ' hℓ' hne => by
      have h2 : ℓ' ≠ q₀ := fun h => hq₀T (h ▸ hℓ')
      simpa [hne, h2] using (hrT ℓ hℓ).2.2.2.2 ℓ' (mS₂ (mS₁ (Or.inr (Or.inl hℓ'))))
    rT_sym_rP := fun ℓ hℓ p hp => by
      have h1 : rP p ≠ ℓ := fun h => (hrPS p hp).2.1 (h ▸ hℓ)
      have h2 : rP p ≠ q₀ := (hrPS p hp).2.2
      simpa [h1, h2] using (hrT ℓ hℓ).2.2.2.2 (rP p)
        (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩))
    rT_sym_rT := fun ℓ hℓ ℓ' hℓ' hne => hrTsym ℓ hℓ ℓ' hℓ' (Ne.symm hne) }⟩

namespace Slots

variable {β θ : ℤ} {p₀ : ℕ} (D : Slots β θ p₀)

/-- Reverse symbols at a glue slot `r_p ≡ 1 (mod 4)`: `[y/r_p] = [r_p/y]` for every odd prime
`y ≠ r_p`. -/
theorem rev_rP {p : ℕ} (hp : p ∈ primesOf β \ {p₀}) {y : ℕ} (hy : y.Prime) (hy2 : y ≠ 2)
    (hne : y ≠ D.rP p) : legBit (D.rP p) y = legBit y (D.rP p) :=
  legBit_symm_of_one_mod_four (D.rP_prime p hp) hy hy2 (Ne.symm hne)
    (by have := D.rP_mod_eight p hp; omega)

/-- Reverse symbols at a glue slot `r_ℓ ≡ 1 (mod 4)`: `[y/r_ℓ] = [r_ℓ/y]` for every odd prime
`y ≠ r_ℓ`. -/
theorem rev_rT {ℓ : ℕ} (hℓ : ℓ ∈ primesOf θ) {y : ℕ} (hy : y.Prime) (hy2 : y ≠ 2)
    (hne : y ≠ D.rT ℓ) : legBit (D.rT ℓ) y = legBit y (D.rT ℓ) :=
  legBit_symm_of_one_mod_four (D.rT_prime ℓ hℓ) hy hy2 (Ne.symm hne)
    (by have := D.rT_mod_eight ℓ hℓ; omega)

/-- Reverse symbols at `q₀ ≡ 3 (mod 4)`: `[y/q₀] = [q₀/y] + λ_y` for every odd prime `y ≠ q₀`. -/
theorem rev_q₀ {y : ℕ} (hy : y.Prime) (hy2 : y ≠ 2) (hne : y ≠ D.q₀) :
    legBit D.q₀ y = legBit y D.q₀ + lamBit y :=
  legBit_symm_of_three_mod_four D.q₀_prime hy hy2 (Ne.symm hne)
    (by have := D.q₀_mod_eight; omega)

/-- By construction `Σ_{p∈P} [q₀/p] = x`. -/
theorem sum_q₀_sym (hp₀ : p₀ ∈ primesOf β) :
    ∑ p ∈ primesOf β, legBit p D.q₀ = signBit β + 1 := by
  rw [← Finset.add_sum_erase _ _ hp₀, D.q₀_sym_p₀, ← Finset.sdiff_singleton_eq_erase,
    Finset.sum_congr rfl D.q₀_sym_P, add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- The set of slots `{q₀} ∪ {r_p} ∪ {r_ℓ}`. -/
def primes : Finset ℕ :=
  insert D.q₀ ((primesOf β \ {p₀}).image D.rP ∪ (primesOf θ).image D.rT)

/-- The construction uses `ω(β) + ω(θ)` slots. -/
theorem card_primes (hp₀ : p₀ ∈ primesOf β) :
    D.primes.card = (primesOf β).card + (primesOf θ).card := by
  classical
  have h1 : D.q₀ ∉ (primesOf β \ {p₀}).image D.rP ∪ (primesOf θ).image D.rT := by
    simp only [Finset.mem_union, Finset.mem_image, not_or, not_exists, not_and]
    exact ⟨fun p hp h => D.rP_ne_q₀ p hp h, fun ℓ hℓ h => D.rT_ne_q₀ ℓ hℓ h⟩
  have h2 : Disjoint ((primesOf β \ {p₀}).image D.rP) ((primesOf θ).image D.rT) := by
    rw [Finset.disjoint_left]
    simp only [Finset.mem_image, not_exists, not_and]
    rintro _ ⟨p, hp, rfl⟩ ℓ hℓ h
    exact D.rT_ne_rP ℓ hℓ p hp h
  have h3 := Finset.card_pos.mpr ⟨p₀, hp₀⟩
  have h4 : (primesOf β \ {p₀}).card = (primesOf β).card - 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr hp₀), Finset.card_singleton]
  rw [primes, Finset.card_insert_of_notMem h1, Finset.card_union_of_disjoint h2,
    Finset.card_image_of_injOn D.rP_injOn, Finset.card_image_of_injOn D.rT_injOn, h4]
  omega

end Slots

/-- **L3 for the inputs of DL**: for an admissible `B` and a signed divisor `m` of 2730 with `β`
odd, the slots exist for every `p₀ ∈ P`. -/
theorem exists_slots_of_admissible {B : ℚ} (hB : Admissible B) {m : ℤ} (hm : m ∣ 2730)
    (hβ : Odd (betaOf B m)) {p₀ : ℕ} (hp₀ : p₀ ∈ primesOf (betaOf B m)) :
    Nonempty (Slots (betaOf B m) (thetaOf B m) p₀) := by
  have h8 := (theta1 hB hm).2.1
  exact exists_slots hβ (Int.odd_iff.mpr (by omega)) (theta2_isCoprime hB hm) hp₀

/-- **Step 0 and L3 together** (slot-k §2.4): for every admissible `B` there is a signed divisor
`m` of 2730 with `β` odd and `|β| ≡ 7 (mod 8)`; then `P ≠ ∅`, and for every `p₀ ∈ P` the slots
exist. -/
theorem exists_multiplier_and_slots {B : ℚ} (hB : Admissible B) :
    ∃ m : ℤ, m ∣ 2730 ∧ Odd (betaOf B m) ∧ (betaOf B m).natAbs % 8 = 7 ∧
      (primesOf (betaOf B m)).Nonempty ∧
      ∀ p₀ ∈ primesOf (betaOf B m), Nonempty (Slots (betaOf B m) (thetaOf B m) p₀) := by
  obtain ⟨m, hm, hβ, h7⟩ := exists_multiplier hB
  refine ⟨m, hm, hβ, h7, ?_, fun p₀ hp₀ => exists_slots_of_admissible hB hm hβ hp₀⟩
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd (n := (betaOf B m).natAbs) (by omega)
  exact ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hd, by omega⟩⟩

end ZInQ.RouteK

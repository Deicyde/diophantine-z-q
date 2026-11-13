import ZInQKernel.Density.Abel
import ZInQKernel.Density.Description

/-!
# The residue set `A_L` and the main term (pd-paper §2.1 remark 3, Lemma 3.1)

For `L : ℕ`, `QL L` is the set `Q_L` of primes `5 ≤ ℓ ≤ L` with `ℓ ≡ 1 (mod 4)`, the moduli are
`modSet L = {8, 7} ∪ Q_L`, and `ML L = ∏ modSet L = 56 ∏_{ℓ ∈ Q_L} ℓ` (`ML_eq`). The Chinese
remainder theorem (`ZMod.prodEquivPi`) gives `crt L : ZMod (ML L) ≃+* Π i, ZMod i`, and

  `AL L = {a : a ≡ 1 (mod 8), a mod 7 ∈ {3, 5, 6}, a mod ℓ ∉ {0, −1} for ℓ ∈ Q_L}`.

* `card_AL`: `#A_L = 3 ∏_{ℓ ∈ Q_L} (ℓ − 2)`; `totient_ML`: `φ(M_L) = 4 · 6 ∏_{ℓ ∈ Q_L} (ℓ − 1)`;
* `deltaL_eq`: `δ_L = #A_L/φ(M_L) = (1/8) ∏_{ℓ ∈ Q_L} (ℓ − 2)/(ℓ − 1)`;
* `deltaL_ge`: `δ_L ≥ 3/(8(L − 1))` for `L ≥ 4`;
* `isUnit_of_mem_AL`: every element of `A_L` is a unit;
* `mem_CL`: a prime `p` with `p mod M_L ∈ A_L` (the set `C_L`) is in the class of Proposition 1.6
  (`InClass p`) and satisfies `ℓ ∤ p + 1` for every `ℓ ∈ Q_L`;
* `phi_CL_lower` (Lemma 3.1): `Φ_{C_L}(x) ≥ δ_L/(x − 1) − K_L` on `(1, 2]`, from Mathlib's
  `ArithmeticFunction.vonMangoldt.LSeries_residueClass_lower_bound` summed over `A_L`, with the
  prime powers removed by `summable_residueClass_non_primes_div` (at exponent 1, compared with
  exponent `x`: the referee's remark F5).
-/

namespace ZInQ.Density

open Finset

/-- `Q_L`: the primes `5 ≤ ℓ ≤ L` with `ℓ ≡ 1 (mod 4)`. -/
def QL (L : ℕ) : Finset ℕ := (Icc 5 L).filter (fun ℓ => ℓ.Prime ∧ ℓ % 4 = 1)

theorem mem_QL {L ℓ : ℕ} : ℓ ∈ QL L ↔ 5 ≤ ℓ ∧ ℓ ≤ L ∧ ℓ.Prime ∧ ℓ % 4 = 1 := by
  simp [QL, and_assoc]

/-- The moduli `{8, 7} ∪ Q_L`. -/
def modSet (L : ℕ) : Finset ℕ := insert 8 (insert 7 (QL L))

theorem seven_notMem_QL (L : ℕ) : 7 ∉ QL L := by
  rw [mem_QL]; omega

theorem eight_notMem_insert (L : ℕ) : 8 ∉ insert 7 (QL L) := by
  rw [mem_insert, mem_QL]
  rintro (h | ⟨-, -, h, -⟩)
  · omega
  · exact absurd h (by decide)

/-- `M_L = ∏ (8, 7, ℓ ∈ Q_L)`, as the product over the subtype (the form `ZMod.prodEquivPi`
uses). -/
def ML (L : ℕ) : ℕ := ∏ i : modSet L, (i : ℕ)

theorem ML_eq (L : ℕ) : ML L = 8 * (7 * ∏ ℓ ∈ QL L, ℓ) := by
  rw [ML, prod_coe_sort (modSet L) (fun i => i), modSet, prod_insert (eight_notMem_insert L),
    prod_insert (seven_notMem_QL L)]

theorem prod_QL_pos (L : ℕ) : 0 < ∏ ℓ ∈ QL L, ℓ :=
  prod_pos fun ℓ hℓ => (mem_QL.1 hℓ).2.2.1.pos

instance (L : ℕ) : NeZero (ML L) := ⟨by rw [ML_eq]; have := prod_QL_pos L; positivity⟩

theorem coprime_modSet {L i j : ℕ} (hi : i ∈ modSet L) (hj : j ∈ modSet L) (hij : i ≠ j) :
    Nat.Coprime i j := by
  have h8 : ∀ ℓ ∈ QL L, Nat.Coprime 8 ℓ := fun ℓ hℓ => by
    obtain ⟨h5, -, hp, -⟩ := mem_QL.1 hℓ
    have := Nat.Coprime.pow_left 3 ((Nat.coprime_primes Nat.prime_two hp).2 (by omega))
    simpa using this
  have h7 : ∀ ℓ ∈ QL L, Nat.Coprime 7 ℓ := fun ℓ hℓ => by
    obtain ⟨h5, -, hp, h4⟩ := mem_QL.1 hℓ
    exact (Nat.coprime_primes (by norm_num) hp).2 (by omega)
  simp only [modSet, mem_insert] at hi hj
  rcases hi with rfl | rfl | hi <;> rcases hj with rfl | rfl | hj
  · exact absurd rfl hij
  · norm_num
  · exact h8 j hj
  · norm_num
  · exact absurd rfl hij
  · exact h7 j hj
  · exact (h8 i hi).symm
  · exact (h7 i hi).symm
  · exact (Nat.coprime_primes (mem_QL.1 hi).2.2.1 (mem_QL.1 hj).2.2.1).2 hij

theorem pairwise_coprime_modSet (L : ℕ) :
    Pairwise (Function.onFun Nat.Coprime fun i : modSet L => (i : ℕ)) :=
  fun i j hij => coprime_modSet i.2 j.2 (fun h => hij (Subtype.ext h))

/-- The Chinese remainder isomorphism `ZMod M_L ≃+* Π_{i ∈ {8, 7} ∪ Q_L} ZMod i`. -/
noncomputable def crt (L : ℕ) : ZMod (ML L) ≃+* ((i : modSet L) → ZMod (i : ℕ)) :=
  ZMod.prodEquivPi (fun i : modSet L => (i : ℕ)) (pairwise_coprime_modSet L)

theorem crt_apply_natCast (L n : ℕ) (i : modSet L) :
    crt L (n : ZMod (ML L)) i = (n : ZMod (i : ℕ)) := by
  show ZMod.prodEquivPi (fun i : modSet L => (i : ℕ)) (pairwise_coprime_modSet L)
    (n : ZMod (∏ i : modSet L, (i : ℕ))) i = n
  rw [ZMod.prodEquivPi_apply, map_natCast]

/-- The condition on the component modulo `i`: `= 1` modulo 8, a non-square modulo 7, and
`∉ {0, −1}` modulo `ℓ ∈ Q_L`. -/
def cond (i : ℕ) (z : ZMod i) : Prop :=
  if i = 8 then z = 1 else if i = 7 then (z = 3 ∨ z = 5 ∨ z = 6) else (z ≠ 0 ∧ z ≠ -1)

instance (i : ℕ) : DecidablePred (cond i) := fun z => by unfold cond; infer_instance

/-- The residue set `A_L ⊆ ZMod M_L`. -/
noncomputable def AL (L : ℕ) : Finset (ZMod (ML L)) :=
  univ.filter (fun a => ∀ i : modSet L, cond i (crt L a i))

theorem card_cond_eight : Nat.card {z : ZMod 8 // cond 8 z} = 1 := by
  simp only [cond, ite_true]
  simp

theorem card_cond_seven : Nat.card {z : ZMod 7 // cond 7 z} = 3 := by
  simp only [cond, show (7 : ℕ) ≠ 8 by norm_num, ite_false, ite_true]
  rw [Nat.card_eq_fintype_card]
  decide

theorem card_cond_prime {ℓ : ℕ} (hℓ : ℓ.Prime) (h8 : ℓ ≠ 8) (h7 : ℓ ≠ 7) :
    Nat.card {z : ZMod ℓ // cond ℓ z} = ℓ - 2 := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  simp only [cond, h8, h7, ite_false]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hset : univ.filter (fun z : ZMod ℓ => z ≠ 0 ∧ z ≠ -1) = univ \ {0, -1} := by
    ext z; simp [not_or]
  have h01 : (0 : ZMod ℓ) ≠ -1 := (neg_ne_zero.2 one_ne_zero).symm
  rw [hset, card_sdiff_of_subset (subset_univ _), card_univ, ZMod.card, card_pair h01]

/-- **CRT count.** `#A_L = 3 ∏_{ℓ ∈ Q_L} (ℓ − 2)`. -/
theorem card_AL (L : ℕ) : (AL L).card = 3 * ∏ ℓ ∈ QL L, (ℓ - 2) := by
  have e1 : (AL L).card = Nat.card {a : ZMod (ML L) // ∀ i : modSet L, cond i (crt L a i)} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]; rfl
  have e2 : Nat.card {a : ZMod (ML L) // ∀ i : modSet L, cond i (crt L a i)} =
      Nat.card {f : (i : modSet L) → ZMod (i : ℕ) // ∀ i : modSet L, cond i (f i)} :=
    Nat.card_congr ((crt L).toEquiv.subtypeEquiv fun a => Iff.rfl)
  have e3 : Nat.card {f : (i : modSet L) → ZMod (i : ℕ) // ∀ i : modSet L, cond i (f i)} =
      Nat.card ((i : modSet L) → {z : ZMod (i : ℕ) // cond i z}) :=
    Nat.card_congr Equiv.subtypePiEquivPi
  rw [e1, e2, e3, Nat.card_pi,
    prod_coe_sort (modSet L) (fun i => Nat.card {z : ZMod i // cond i z}), modSet,
    prod_insert (eight_notMem_insert L), prod_insert (seven_notMem_QL L), card_cond_eight,
    card_cond_seven, one_mul]
  congr 1
  refine prod_congr rfl fun ℓ hℓ => ?_
  obtain ⟨h5, -, hp, h4⟩ := mem_QL.1 hℓ
  exact card_cond_prime hp (by omega) (by omega)

theorem totient_prod_primes (s : Finset ℕ) (hs : ∀ ℓ ∈ s, ℓ.Prime) :
    Nat.totient (∏ ℓ ∈ s, ℓ) = ∏ ℓ ∈ s, (ℓ - 1) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hpa := hs a (mem_insert_self a s)
    have hs' : ∀ ℓ ∈ s, ℓ.Prime := fun ℓ hℓ => hs ℓ (mem_insert_of_mem hℓ)
    rw [prod_insert ha, prod_insert ha, Nat.totient_mul, Nat.totient_prime hpa, ih hs']
    exact Nat.Coprime.prod_right fun ℓ hℓ =>
      (Nat.coprime_primes hpa (hs' ℓ hℓ)).2 (fun h => ha (h ▸ hℓ))

/-- `φ(M_L) = 4 · 6 ∏_{ℓ ∈ Q_L} (ℓ − 1)`. -/
theorem totient_ML (L : ℕ) : Nat.totient (ML L) = 4 * (6 * ∏ ℓ ∈ QL L, (ℓ - 1)) := by
  have hQ : ∀ ℓ ∈ QL L, ℓ.Prime := fun ℓ hℓ => (mem_QL.1 hℓ).2.2.1
  have c7 : Nat.Coprime 7 (∏ ℓ ∈ QL L, ℓ) := Nat.Coprime.prod_right fun ℓ hℓ =>
    (Nat.coprime_primes (by norm_num) (hQ ℓ hℓ)).2 (fun h => seven_notMem_QL L (h ▸ hℓ))
  have c8 : Nat.Coprime 8 (7 * ∏ ℓ ∈ QL L, ℓ) :=
    Nat.Coprime.mul_right (by norm_num) (Nat.Coprime.prod_right fun ℓ hℓ =>
      coprime_modSet (L := L) (by simp [modSet]) (by simp [modSet, hℓ])
        (fun h => by subst h; exact eight_notMem_insert L (mem_insert_of_mem hℓ)))
  rw [ML_eq, Nat.totient_mul c8, Nat.totient_mul c7, Nat.totient_prime (p := 7) (by norm_num),
    totient_prod_primes _ hQ, show Nat.totient 8 = 4 by decide]

/-- `δ_L = #A_L / φ(M_L)`. -/
noncomputable def deltaL (L : ℕ) : ℝ := ((AL L).card : ℝ) / (Nat.totient (ML L) : ℝ)

/-- `δ_L = (1/8) ∏_{ℓ ∈ Q_L} (ℓ − 2)/(ℓ − 1)`. -/
theorem deltaL_eq (L : ℕ) :
    deltaL L = (1 / 8) * ∏ ℓ ∈ QL L, (((ℓ : ℝ) - 2) / ((ℓ : ℝ) - 1)) := by
  have h2 : ∀ ℓ ∈ QL L, (((ℓ - 2 : ℕ) : ℝ)) = (ℓ : ℝ) - 2 := fun ℓ hℓ => by
    have := (mem_QL.1 hℓ).1; rw [Nat.cast_sub (by omega)]; norm_num
  have h1 : ∀ ℓ ∈ QL L, (((ℓ - 1 : ℕ) : ℝ)) = (ℓ : ℝ) - 1 := fun ℓ hℓ => by
    have := (mem_QL.1 hℓ).1; rw [Nat.cast_sub (by omega)]; norm_num
  have hpos : 0 < ∏ ℓ ∈ QL L, ((ℓ : ℝ) - 1) := prod_pos fun ℓ hℓ => by
    have : (5 : ℝ) ≤ ℓ := by exact_mod_cast (mem_QL.1 hℓ).1
    linarith
  rw [deltaL, card_AL, totient_ML, prod_div_distrib]
  push_cast
  rw [prod_congr rfl h2, prod_congr rfl h1]
  field_simp
  ring

theorem prod_tel (k : ℕ) :
    ∏ n ∈ Icc 5 (k + 4), (((n : ℝ) - 2) / ((n : ℝ) - 1)) = 3 / ((k : ℝ) + 3) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [show k + 1 + 4 = (k + 4) + 1 by ring, prod_Icc_succ_top (by omega), ih]
    rw [show ((k + 4 + 1 : ℕ) : ℝ) = (k : ℝ) + 5 by push_cast; ring,
      show ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 by push_cast; ring,
      show (k : ℝ) + 5 - 2 = k + 3 by ring, show (k : ℝ) + 5 - 1 = k + 4 by ring,
      show (k : ℝ) + 1 + 3 = k + 4 by ring]
    have : (0 : ℝ) < k + 3 := by positivity
    field_simp

/-- **Main term.** `δ_L ≥ 3/(8(L − 1))` for `L ≥ 4`. -/
theorem deltaL_ge {L : ℕ} (hL : 4 ≤ L) : 3 / (8 * ((L : ℝ) - 1)) ≤ deltaL L := by
  set f : ℕ → ℝ := fun n => ((n : ℝ) - 2) / ((n : ℝ) - 1) with hf
  have hf01 : ∀ n ∈ Icc 5 L, 0 ≤ f n ∧ f n ≤ 1 := by
    intro n hn
    have : (5 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.1 hn).1
    refine ⟨div_nonneg (by linarith) (by linarith), (div_le_one (by linarith)).2 (by linarith)⟩
  have hsub : QL L ⊆ Icc 5 L := fun ℓ hℓ => by
    obtain ⟨h1, h2, -⟩ := mem_QL.1 hℓ; exact mem_Icc.2 ⟨h1, h2⟩
  have htel : ∏ n ∈ Icc 5 L, f n = 3 / ((L : ℝ) - 1) := by
    have := prod_tel (L - 4)
    rw [show L - 4 + 4 = L by omega] at this
    rw [this, Nat.cast_sub hL]
    congr 1; push_cast; ring
  have hle : ∏ n ∈ Icc 5 L, f n ≤ ∏ ℓ ∈ QL L, f ℓ := by
    rw [← prod_sdiff hsub]
    have h1 : ∏ n ∈ Icc 5 L \ QL L, f n ≤ 1 :=
      prod_le_one₀ (fun n hn => (hf01 n (sdiff_subset hn)).1)
        (fun n hn => (hf01 n (sdiff_subset hn)).2)
    have h2 : 0 ≤ ∏ ℓ ∈ QL L, f ℓ := prod_nonneg fun ℓ hℓ => (hf01 ℓ (hsub hℓ)).1
    nlinarith
  rw [deltaL_eq]
  have hL1 : (0 : ℝ) < (L : ℝ) - 1 := by
    have : (4 : ℝ) ≤ L := by exact_mod_cast hL
    linarith
  calc 3 / (8 * ((L : ℝ) - 1)) = 1 / 8 * (3 / ((L : ℝ) - 1)) := by field_simp
    _ ≤ 1 / 8 * ∏ ℓ ∈ QL L, f ℓ := by rw [← htel]; exact mul_le_mul_of_nonneg_left hle (by norm_num)
    _ = _ := rfl

theorem zmod7_ne_zero : ∀ z : ZMod 7, (z = 3 ∨ z = 5 ∨ z = 6) → z ≠ 0 := by decide

theorem isUnit_of_cond {L i : ℕ} (hi : i ∈ modSet L) {z : ZMod i} (h : cond i z) : IsUnit z := by
  simp only [modSet, mem_insert] at hi
  rcases hi with rfl | rfl | hQ
  · simp only [cond, ite_true] at h
    rw [h]; exact isUnit_one
  · have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    simp only [cond, show (7 : ℕ) ≠ 8 by norm_num, ite_false, ite_true] at h
    exact isUnit_iff_ne_zero.2 (zmod7_ne_zero z h)
  · obtain ⟨h5, -, hp, h4⟩ := mem_QL.1 hQ
    have : Fact i.Prime := ⟨hp⟩
    simp only [cond, show i ≠ 8 by omega, show i ≠ 7 by omega, ite_false] at h
    exact isUnit_iff_ne_zero.2 h.1

/-- Every element of `A_L` is a unit modulo `M_L`. -/
theorem isUnit_of_mem_AL {L : ℕ} {a : ZMod (ML L)} (ha : a ∈ AL L) : IsUnit a := by
  have h := (mem_filter.1 ha).2
  rw [← isUnit_map_iff (crt L) a, Pi.isUnit_iff]
  exact fun i => isUnit_of_cond i.2 (h i)

/-- `C_L`: the primes `p` with `p mod M_L ∈ A_L`. -/
def CL (L : ℕ) : Set ℕ := {p | p.Prime ∧ (p : ZMod (ML L)) ∈ AL L}

/-- A prime of `C_L` is in the class of Proposition 1.6 and `ℓ ∤ p + 1` for `ℓ ∈ Q_L`. -/
theorem mem_CL {L p : ℕ} (h : p ∈ CL L) :
    p.Prime ∧ InClass p ∧ ∀ ℓ ∈ QL L, ¬ ℓ ∣ p + 1 := by
  obtain ⟨hp, hA⟩ := h
  have hc := (mem_filter.1 hA).2
  have c8 := hc ⟨8, by simp [modSet]⟩
  have c7 := hc ⟨7, by simp [modSet]⟩
  rw [crt_apply_natCast] at c8 c7
  simp only [cond, ite_true] at c8
  simp only [cond, show (7 : ℕ) ≠ 8 by norm_num, ite_false, ite_true] at c7
  refine ⟨hp, ⟨?_, ?_⟩, fun ℓ hℓ hdvd => ?_⟩
  · rw [← ZMod.val_natCast, c8]; rfl
  · rcases c7 with h | h | h <;> [left; (right; left); (right; right)] <;>
      (rw [← ZMod.val_natCast, h]; rfl)
  · obtain ⟨h5, -, hpℓ, h4⟩ := mem_QL.1 hℓ
    have cℓ := hc ⟨ℓ, by simp [modSet, hℓ]⟩
    rw [crt_apply_natCast] at cℓ
    simp only [cond, show ℓ ≠ 8 by omega, show ℓ ≠ 7 by omega, ite_false] at cℓ
    have h0 : ((p + 1 : ℕ) : ZMod ℓ) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    push_cast at h0
    exact cℓ.2 (eq_neg_of_add_eq_zero_left h0)

theorem CL_subset_primes (L : ℕ) : CL L ⊆ {p | p.Prime} := fun _ h => h.1

open ArithmeticFunction in
/-- `Σ Λ(n)/n^x` converges for `x > 1`. -/
theorem summable_vonMangoldt_div_rpow {x : ℝ} (hx : 1 < x) :
    Summable (fun n : ℕ => vonMangoldt n / (n : ℝ) ^ x) := by
  have := (LSeriesSummable_vonMangoldt (s := (x : ℂ)) (by simpa using hx)).norm
  refine this.congr fun n => ?_
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · simp [hn]
  · simp [Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]

open ArithmeticFunction in
/-- **Lemma 3.1.** There is `K_L` with `Φ_{C_L}(x) ≥ δ_L/(x − 1) − K_L` for all `x ∈ (1, 2]`. -/
theorem phi_CL_lower (L : ℕ) :
    ∃ K : ℝ, ∀ x ∈ Set.Ioc (1 : ℝ) 2, deltaL L / (x - 1) - K ≤ PhiS (CL L) x := by
  have hC : ∀ a ∈ AL L, ∃ C : ℝ, ∀ {x : ℝ} (_ : x ∈ Set.Ioc 1 2),
      ((ML L).totient : ℝ)⁻¹ / (x - 1) - C ≤ ∑' n, vonMangoldt.residueClass a n / (n : ℝ) ^ x :=
    fun a ha => vonMangoldt.LSeries_residueClass_lower_bound (isUnit_of_mem_AL ha)
  choose! C hCa using hC
  set g : ℕ → ℝ := fun n => ∑ a ∈ AL L, (if n.Prime then 0 else vonMangoldt.residueClass a n)
    with hg
  have hg0 : ∀ n, 0 ≤ g n := fun n => sum_nonneg fun a _ => by
    split_ifs
    · exact le_rfl
    · exact vonMangoldt.residueClass_nonneg a n
  have hgsum : Summable (fun n : ℕ => g n / n) := by
    have : (fun n : ℕ => g n / n) = fun n : ℕ =>
        ∑ a ∈ AL L, (if n.Prime then 0 else vonMangoldt.residueClass a n) / n := by
      funext n; rw [hg, sum_div]
    rw [this]
    exact summable_sum fun a _ => vonMangoldt.summable_residueClass_non_primes_div a
  refine ⟨∑ a ∈ AL L, C a + ∑' n : ℕ, g n / n, fun x hx => ?_⟩
  have hx1 : 1 < x := hx.1
  have hsumA : ∀ a ∈ AL L, Summable (fun n : ℕ => vonMangoldt.residueClass a n / (n : ℝ) ^ x) :=
    fun a _ => Summable.of_nonneg_of_le
      (fun n => div_nonneg (vonMangoldt.residueClass_nonneg a n) (by positivity))
      (fun n => div_le_div_of_nonneg_right (vonMangoldt.residueClass_le a n) (by positivity))
      (summable_vonMangoldt_div_rpow hx1)
  have h1 : ∑ a ∈ AL L, (((ML L).totient : ℝ)⁻¹ / (x - 1) - C a) ≤
      ∑ a ∈ AL L, ∑' n, vonMangoldt.residueClass a n / (n : ℝ) ^ x :=
    sum_le_sum fun a ha => hCa a ha hx
  rw [← Summable.tsum_finsetSum hsumA] at h1
  -- split off the prime powers
  have hdec : ∀ n : ℕ, ∑ a ∈ AL L, vonMangoldt.residueClass a n / (n : ℝ) ^ x =
      phiTerm (CL L) x n + g n / (n : ℝ) ^ x := by
    intro n
    rw [← sum_div, phiTerm, ← add_div]
    congr 1
    have hres : ∀ a : ZMod (ML L), vonMangoldt.residueClass a n =
        if (n : ZMod (ML L)) = a then vonMangoldt n else 0 := fun a => by
      simp [vonMangoldt.residueClass, Set.indicator_apply]
    by_cases hp : n.Prime
    · have hg' : g n = 0 := by simp [hg, hp]
      rw [hg', add_zero]
      simp only [hres]
      rw [sum_ite_eq (AL L) (n : ZMod (ML L)) (fun _ => vonMangoldt n)]
      simp only [Set.indicator_apply, CL, Set.mem_ofPred_eq, hp, true_and,
        vonMangoldt_apply_prime hp]
    · have hn : n ∉ CL L := fun h => hp h.1
      rw [Set.indicator_of_notMem hn, zero_add]
      simp [hg, hp]
  have hgx : ∀ n : ℕ, g n / (n : ℝ) ^ x ≤ g n / n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [Real.zero_rpow (by linarith : x ≠ 0)]
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have : (n : ℝ) ≤ (n : ℝ) ^ x := by
        calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ (n : ℝ) ^ x := Real.rpow_le_rpow_of_exponent_le hn1 hx1.le
      exact div_le_div_of_nonneg_left (hg0 n) (by linarith) this
  have hgxsum : Summable (fun n : ℕ => g n / (n : ℝ) ^ x) :=
    Summable.of_nonneg_of_le (fun n => div_nonneg (hg0 n) (by positivity)) hgx hgsum
  have hphi := summable_phiTerm (CL_subset_primes L) hx1 hx.2
  have h2 : ∑' n, ∑ a ∈ AL L, vonMangoldt.residueClass a n / (n : ℝ) ^ x ≤
      PhiS (CL L) x + ∑' n : ℕ, g n / n := by
    rw [tsum_congr hdec, Summable.tsum_add hphi hgxsum, PhiS]
    exact add_le_add le_rfl (Summable.tsum_le_tsum hgx hgxsum hgsum)
  have h3 : ∑ a ∈ AL L, (((ML L).totient : ℝ)⁻¹ / (x - 1) - C a) =
      deltaL L / (x - 1) - ∑ a ∈ AL L, C a := by
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul, deltaL]
    ring
  rw [h3] at h1
  linarith

end ZInQ.Density

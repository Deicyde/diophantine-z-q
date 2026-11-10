import Mathlib

/-!
# Local densities of `(ℓU)² + (b + ℓV)²` (pd-paper.md §4.3, Lemma 4.3)

`ZSet R ℓ b` is the zero set of `F(U, V) = (ℓU)² + (b + ℓV)²` in `R × R`.

* `card_zset_prime`: for a prime `q ≡ 1 (mod 4)` with `q ∤ ℓ`, `#ZSet (ZMod q) = 2q - 1`.
* `card_zset_prod`: for a finite set `t` of such primes, `#ZSet (ZMod (∏ t)) = ∏_{q ∈ t} (2q - 1)`
  (Chinese remainder theorem).
-/

open Finset

namespace ZInQ.Density.GaussSieve

noncomputable section

open scoped Classical

/-- The zero set of `(ℓU)² + (b + ℓV)²` in `R × R`. -/
def ZSet (R : Type*) [CommRing R] (ℓ b : ℤ) : Set (R × R) :=
  {z | ((ℓ : R) * z.1) ^ 2 + ((b : R) + (ℓ : R) * z.2) ^ 2 = 0}

theorem mem_zset {R : Type*} [CommRing R] {ℓ b : ℤ} {z : R × R} :
    z ∈ ZSet R ℓ b ↔ ((ℓ : R) * z.1) ^ 2 + ((b : R) + (ℓ : R) * z.2) ^ 2 = 0 := Iff.rfl

/-- A ring isomorphism maps zero sets to zero sets. -/
def zsetEquivOfRingEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) (ℓ b : ℤ) :
    ZSet R ℓ b ≃ ZSet S ℓ b :=
  Equiv.subtypeEquiv (e.toEquiv.prodCongr e.toEquiv) fun z => by
    simp only [mem_zset, Equiv.prodCongr_apply, RingEquiv.toEquiv_eq_coe, Prod.map_fst,
      Prod.map_snd, EquivLike.coe_coe]
    constructor
    · intro h
      have := congrArg e h
      simpa [map_add, map_mul, map_pow, map_intCast] using this
    · intro h
      have := congrArg e.symm h
      simpa [map_add, map_mul, map_pow, map_intCast] using this

/-- The zero set in a product ring is the product of the zero sets. -/
def zsetEquivProd (R S : Type*) [CommRing R] [CommRing S] (ℓ b : ℤ) :
    ZSet (R × S) ℓ b ≃ ZSet R ℓ b × ZSet S ℓ b :=
  (Equiv.subtypeEquiv (Equiv.prodProdProdComm R S R S)
    (q := fun c => c.1 ∈ ZSet R ℓ b ∧ c.2 ∈ ZSet S ℓ b) fun z => by
      simp only [mem_zset, Equiv.prodProdProdComm_apply, Prod.ext_iff]
      simp).trans
    (Equiv.subtypeProdEquivProd)

theorem card_zset_mul {m n : ℕ} (h : m.Coprime n) (ℓ b : ℤ) :
    Nat.card (ZSet (ZMod (m * n)) ℓ b) = Nat.card (ZSet (ZMod m) ℓ b) * Nat.card (ZSet (ZMod n) ℓ b) := by
  rw [Nat.card_congr ((zsetEquivOfRingEquiv (ZMod.chineseRemainder h) ℓ b).trans
    (zsetEquivProd _ _ ℓ b)), Nat.card_prod]

/-- **Lemma 4.3** at a prime. -/
theorem card_zset_prime {q : ℕ} [hq : Fact q.Prime] (h4 : q % 4 = 1) {ℓ : ℤ}
    (hℓ : (ℓ : ZMod q) ≠ 0) (b : ℤ) :
    Nat.card (ZSet (ZMod q) ℓ b) = 2 * q - 1 := by
  obtain ⟨i, hi⟩ : IsSquare (-1 : ZMod q) := ZMod.exists_sq_eq_neg_one_iff.2 (by omega)
  have hi2 : i ^ 2 = -1 := by rw [hi]; ring
  have hq2 : q ≠ 2 := by rintro rfl; norm_num at h4
  have h2 : (2 : ZMod q) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq.out Nat.prime_two).1 this)
  have hi0 : i ≠ 0 := by rintro rfl; simp at hi2
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [mem_zset]
  generalize (ℓ : ZMod q) = L at hℓ ⊢
  generalize (b : ZMod q) = B
  let f₁ : ZMod q → ZMod q × ZMod q := fun V => (i * (B + L * V) * L⁻¹, V)
  let f₂ : ZMod q → ZMod q × ZMod q := fun V => (-i * (B + L * V) * L⁻¹, V)
  have hinj₁ : Function.Injective f₁ := fun x y h => (Prod.ext_iff.1 h).2
  have hinj₂ : Function.Injective f₂ := fun x y h => (Prod.ext_iff.1 h).2
  have hUL : ∀ U : ZMod q, U = L * U * L⁻¹ := fun U => by
    rw [mul_comm L U, mul_inv_cancel_right₀ hℓ]
  have hset : univ.filter (fun z : ZMod q × ZMod q => (L * z.1) ^ 2 + (B + L * z.2) ^ 2 = 0) =
      univ.image f₁ ∪ univ.image f₂ := by
    ext ⟨U, V⟩
    simp only [mem_filter, mem_univ, true_and, mem_union, mem_image, f₁, f₂, Prod.mk.injEq]
    constructor
    · intro h
      have : (L * U) ^ 2 = (i * (B + L * V)) ^ 2 := by
        linear_combination h - (B + L * V) ^ 2 * hi2
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 this with h' | h'
      · left; exact ⟨V, by rw [hUL U, h'], rfl⟩
      · right; exact ⟨V, by rw [hUL U, h']; ring, rfl⟩
    · rintro (⟨V', hU, rfl⟩ | ⟨V', hU, rfl⟩)
      · rw [← hU]
        have : L * (i * (B + L * V') * L⁻¹) = i * (B + L * V') := by
          rw [mul_comm, mul_assoc, inv_mul_cancel₀ hℓ, mul_one]
        rw [this]; linear_combination (B + L * V') ^ 2 * hi2
      · rw [← hU]
        have : L * (-i * (B + L * V') * L⁻¹) = -i * (B + L * V') := by
          rw [mul_comm, mul_assoc, inv_mul_cancel₀ hℓ, mul_one]
        rw [this]; linear_combination (B + L * V') ^ 2 * hi2
  have hinter : univ.image f₁ ∩ univ.image f₂ = {(0, -B * L⁻¹)} := by
    ext ⟨U, V⟩
    simp only [mem_inter, mem_image, mem_univ, true_and, f₁, f₂, Prod.mk.injEq,
      mem_singleton]
    constructor
    · rintro ⟨⟨V₁, h₁, rfl⟩, ⟨V₂, h₂, rfl⟩⟩
      have ht : B + L * V₂ = 0 := by
        have : i * (B + L * V₂) * L⁻¹ * 2 = 0 := by linear_combination h₁ - h₂
        simpa [hi0, hℓ, h2] using this
      refine ⟨by rw [← h₁, ht]; ring, ?_⟩
      have : V₂ = L * V₂ * L⁻¹ := hUL V₂
      rw [this, show L * V₂ = -B by linear_combination ht]
    · rintro ⟨rfl, rfl⟩
      have : B + L * (-B * L⁻¹) = 0 := by
        rw [show L * (-B * L⁻¹) = -B * (L * L⁻¹) by ring, mul_inv_cancel₀ hℓ]; ring
      exact ⟨⟨_, by rw [this]; ring, rfl⟩, ⟨_, by rw [this]; ring, rfl⟩⟩
  rw [hset]
  have := card_union_add_card_inter (univ.image f₁) (univ.image f₂)
  rw [hinter, card_singleton, card_image_of_injective _ hinj₁,
    card_image_of_injective _ hinj₂, card_univ, ZMod.card] at this
  omega

/-- **Lemma 4.3**, CRT form: for a finite set `t` of primes `q ≡ 1 (mod 4)` not dividing `ℓ`,
`#ZSet (ZMod (∏ t)) = ∏_{q ∈ t} (2q - 1)`. -/
theorem card_zset_prod (t : Finset ℕ) (ht : ∀ q ∈ t, q.Prime ∧ q % 4 = 1 ∧ ¬ (q : ℤ) ∣ ℓ)
    (b : ℤ) : Nat.card (ZSet (ZMod (∏ q ∈ t, q)) ℓ b) = ∏ q ∈ t, (2 * q - 1) := by
  induction t using Finset.induction_on with
  | empty =>
    simp only [prod_empty]
    rw [Nat.card_eq_fintype_card, Fintype.card_eq_one_iff]
    exact ⟨⟨0, Subsingleton.elim _ _⟩, fun x => Subsingleton.elim _ _⟩
  | insert a t hat ih =>
    have hA := ht a (mem_insert_self a t)
    rw [prod_insert hat, prod_insert hat, card_zset_mul, ih fun q hq => ht q (mem_insert_of_mem hq)]
    · have : Fact a.Prime := ⟨hA.1⟩
      rw [card_zset_prime hA.2.1]
      rw [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact hA.2.2
    · refine Nat.Coprime.prod_right fun q hq => ?_
      have hQ := ht q (mem_insert_of_mem hq)
      rw [Nat.coprime_primes hA.1 hQ.1]
      rintro rfl; exact hat hq

end

end ZInQ.Density.GaussSieve

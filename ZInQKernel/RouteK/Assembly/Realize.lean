import ZInQKernel.RouteK.System
import ZInQKernel.RouteK.Slots

/-!
# Route K, L5: the configuration of an odd squarefree number

`docs/research/slot-k.md` §2.1: an odd squarefree `d > 0` with prime set `S` defines a
configuration by its Legendre symbols: the class of `p ∈ S` is `p mod 8` and the bit `[y/x]` is
`legBit x y`. Reciprocity is `legBit_reciprocity`.

We define the configuration of any injective family `f : κ → ℕ` of odd primes (`primeCfg`), so
that the configurations met in the proof of DL can be written on the abstract index types of
Lemmas 1 and 2, and the configuration of an odd number `d`, indexed by its prime factors
(`natConfig`). The class of a divisor `a` of `d` in the first Kummer coordinate is `natClass d a`:
`a₀ = [a < 0]`, `a₁ = 0` (`a` is odd), `u_p = [p ∣ a]`. `SelmerCertified d a` says that `Σ(𝒞_d)` has
exactly 8 solutions and that one of them has first coordinate `natClass d a`: this is the
certificate of Selmer type of slot-k §1.2, stated through the explicit system.

`selmerCertified_of_primeCfg` transports a certificate from `primeCfg f` to `natConfig (∏ f)`.
-/

namespace ZInQ.RouteK

open scoped BigOperators

/-! ### Classes mod 8 of odd primes -/

theorem natCast_zmod8_of_mod {p a : ℕ} (h : p % 8 = a) : (p : ZMod 8) = a := by
  rw [← ZMod.natCast_mod p 8, h]

theorem natCast_mem_oddClasses {p : ℕ} (hp : p % 2 = 1) : (p : ZMod 8) ∈ oddClasses := by
  have h : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
  rcases h with h | h | h | h <;> rw [natCast_zmod8_of_mod h] <;> decide

/-- `λ` of the class mod 8 of an odd prime is `λ_p = [-1/p]`. -/
theorem lam8_natCast_eq_lamBit {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    lam8 (p : ZMod 8) = lamBit p := by
  have := Fact.mk hp
  rw [lamBit_eq p]
  have hodd : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left hp2
  have h4 : p % 4 = p % 8 % 4 := (Nat.mod_mod_of_dvd p (by norm_num : 4 ∣ 8)).symm
  have h : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
  rcases h with h | h | h | h <;> rw [natCast_zmod8_of_mod h, h4, h] <;> decide

/-! ### The configuration of a family of odd primes -/

/-- The configuration of an injective family `f : κ → ℕ` of odd primes: classes `f k mod 8` and
bits `[f a/f b] = legBit (f b) (f a)`. -/
noncomputable def primeCfg {κ : Type*} (f : κ → ℕ) (hf : Function.Injective f)
    (hp : ∀ k, (f k).Prime ∧ f k ≠ 2) : Config κ where
  cls k := (f k : ZMod 8)
  cls_mem k := natCast_mem_oddClasses (((hp k).1.eq_two_or_odd).resolve_left (hp k).2)
  bit a b := legBit (f b) (f a)
  recip x y h := by
    show legBit (f y) (f x) + legBit (f x) (f y) = lam8 (f x : ZMod 8) * lam8 (f y : ZMod 8)
    rw [lam8_natCast_eq_lamBit (hp x).1 (hp x).2, lam8_natCast_eq_lamBit (hp y).1 (hp y).2,
      legBit_reciprocity (hp y).1 (hp x).1 (hp y).2 (hp x).2 (hf.ne h).symm, mul_comm]

section primeCfg

variable {κ : Type*} (f : κ → ℕ) (hf : Function.Injective f) (hp : ∀ k, (f k).Prime ∧ f k ≠ 2)

@[simp] theorem primeCfg_cls (k : κ) : (primeCfg f hf hp).cls k = (f k : ZMod 8) := rfl

@[simp] theorem primeCfg_bit (a b : κ) : (primeCfg f hf hp).bit a b = legBit (f b) (f a) := rfl

theorem primeCfg_lam (k : κ) : (primeCfg f hf hp).lam k = lamBit (f k) :=
  lam8_natCast_eq_lamBit (hp k).1 (hp k).2

include hf hp in
/-- A product of distinct primes is squarefree. -/
theorem squarefree_prod_primes [Fintype κ] : Squarefree (∏ k, f k) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun a _ b _ hab => ?_)
    fun k _ => (hp k).1.squarefree
  simp only [Function.onFun, ← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (hp a).1 (hp b).1).mpr (hf.ne hab)

include hf hp in
theorem primeFactors_prod_primes [Fintype κ] [DecidableEq κ] :
    (∏ k, f k).primeFactors = Finset.univ.image f := by
  have h : ∏ k, f k = ∏ p ∈ Finset.univ.image f, p :=
    (Finset.prod_image (f := fun p => p) fun a _ b _ h => hf h).symm
  rw [h, Nat.primeFactors_prod]
  intro p hp'
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hp'
  exact (hp k).1

include hp in
theorem odd_prod_primes [Fintype κ] : Odd (∏ k, f k) := by
  refine Finset.prod_induction f Odd (fun _ _ => Odd.mul) odd_one fun k _ => ?_
  exact Nat.odd_iff.mpr (((hp k).1.eq_two_or_odd).resolve_left (hp k).2)

end primeCfg

/-! ### The configuration of an odd number and the class of a divisor -/

theorem prime_ne_two_of_mem_primeFactors {d : ℕ} (hd : Odd d) {p : ℕ} (h : p ∈ d.primeFactors) :
    p.Prime ∧ p ≠ 2 := by
  refine ⟨Nat.prime_of_mem_primeFactors h, fun h2 => ?_⟩
  subst h2
  exact (Nat.not_even_iff_odd.mpr hd) (even_iff_two_dvd.mpr (Nat.dvd_of_mem_primeFactors h))

/-- The configuration `𝒞_d` of an odd number `d`, indexed by its prime factors: classes `p mod 8`
and bits `[y/x] = legBit x y` (slot-k §2.1). -/
noncomputable def natConfig (d : ℕ) (hd : Odd d) : Config d.primeFactors :=
  primeCfg (fun p => p.1) Subtype.val_injective fun p => prime_ne_two_of_mem_primeFactors hd p.2

/-- The first-coordinate class of an odd divisor `a` of `d`: `a = (−1)^{a₀} 2^{a₁} Π p^{u_p}` with
`a₀ = [a < 0]`, `a₁ = 0` and `u_p = [p ∣ a]`. -/
def natClass (d : ℕ) (a : ℤ) : ZMod 2 × ZMod 2 × (d.primeFactors → ZMod 2) :=
  (signBit a, 0, fun p => if (p.1 : ℤ) ∣ a then 1 else 0)

/-- **Certificate of Selmer type** (slot-k §1.2, through Proposition 0): `d` is odd, the system
`Σ(𝒞_d)` has exactly `8 = 2³` solutions, and one of them has first coordinate the class of `a`. -/
def SelmerCertified (d : ℕ) (a : ℤ) : Prop :=
  ∃ hd : Odd d, (natConfig d hd).sols.card = 8 ∧
    ∃ σ ∈ (natConfig d hd).sols, σ.first = natClass d a

theorem odd_of_mod_eight_eq_five {d : ℕ} (h : d % 8 = 5) : Odd d := Nat.odd_iff.mpr (by omega)

/-- Transport of a certificate from the configuration of a family of primes to that of their
product. -/
theorem selmerCertified_of_primeCfg {κ : Type*} [Fintype κ] [DecidableEq κ] (f : κ → ℕ)
    (hf : Function.Injective f) (hp : ∀ k, (f k).Prime ∧ f k ≠ 2) (a : ℤ)
    (hcard : (primeCfg f hf hp).sols.card = 8) {σ : Unknowns κ}
    (hσ : σ ∈ (primeCfg f hf hp).sols) (ha0 : σ.a0 = signBit a) (ha1 : σ.a1 = 0)
    (hu : ∀ k, σ.u k = if (f k : ℤ) ∣ a then 1 else 0) :
    SelmerCertified (∏ k, f k) a := by
  set d := ∏ k, f k
  have hd : Odd d := odd_prod_primes f hp
  have hmem : ∀ k, f k ∈ d.primeFactors := fun k => by
    rw [primeFactors_prod_primes f hf hp]; exact Finset.mem_image_of_mem f (Finset.mem_univ k)
  let e : κ ≃ d.primeFactors := Equiv.ofBijective (fun k => ⟨f k, hmem k⟩)
    ⟨fun a b h => hf (congrArg Subtype.val h), fun q => by
      have h : q.1 ∈ Finset.univ.image f := by
        rw [← primeFactors_prod_primes f hf hp]; exact q.2
      obtain ⟨k, -, hk⟩ := Finset.mem_image.mp h
      exact ⟨k, Subtype.ext hk⟩⟩
  have he : ∀ k, (e k).1 = f k := fun _ => rfl
  have hc : ∀ x, (primeCfg f hf hp).cls x = (natConfig d hd).cls (e x) := fun _ => rfl
  have hb : ∀ x y, x ≠ y → (primeCfg f hf hp).bit x y = (natConfig d hd).bit (e x) (e y) :=
    fun _ _ _ => rfl
  refine ⟨hd, ?_, ?_⟩
  · rw [← (natConfig d hd).card_sols_of_iso e hc hb, hcard]
  · refine ⟨((natConfig d hd).solsEquivOfIso e hc hb ⟨σ, hσ⟩).1,
      ((natConfig d hd).solsEquivOfIso e hc hb ⟨σ, hσ⟩).2, ?_⟩
    rw [Config.solsEquivOfIso_apply]
    simp only [Unknowns.first, Unknowns.comp, natClass, ha0, ha1, Prod.mk.injEq, true_and]
    funext q
    rw [Function.comp_apply, hu, ← he, Equiv.apply_symm_apply]

end ZInQ.RouteK

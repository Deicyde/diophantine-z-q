import Mathlib

/-!
# Lane RC4 (moving character): the finite algebra of the character `ξ` and of `Ψ_i = (1+t)^{ξ_i}`

Manuscript (11/5 version), Proposition `ex:arith-moving-character`, proof, tex lines 3530–3595,
3679–3684 and 3694–3701.

Everything in this file is `PROVED` (abstract finite algebra):

* `ringClass_generated` and `ringClass_extends_iff` — **(4.4b)** (tex 3566–3595): in an exact
  sequence `0 → A → P → C → 0` of abelian groups (`A = 𝐅_r^×`, `P = Pic(ℤ + r𝒪_K)`,
  `C = Cl(K)`, written additively), with classes `q_j ∈ P` whose images generate `C`, relation
  vectors `m^{(a)}` spanning `𝓡 = ker(ℤ^s → C)`, and elements `x_a ∈ A` with
  `∑_j m_j^{(a)} q_j + δ(x_a) = 0`: the kernel and the `q_j` generate `P`, these relations are a
  complete presentation, and the assignments `ξ(q_j) = w_j`, `ξ ∘ δ = κ` extend to a homomorphism
  `ξ : P → Z` **exactly when** `κ(x_a) = −∑_j m_j^{(a)} w_j` for every `a`;
* `kummer_prescription_respects` — the arithmetic half of (4.4a) (tex 3551–3559): if `2^n` divides
  `∑_a b_a m_j^{(a)}` at every nonzero-weight prime, the prescribed multipliers
  `ζ^{−∑_j m_j^{(a)} w_j}` respect the relation `∏ α_a^{b_a} ∈ F_∞^{×2^n}`;
* `conj_value` — conjugation negates the values (tex 3683–3684);
* `choose_two_pow_dvd`, `one_add_t_pow_two_pow` — `v₂ binom(2^{n}, j) ≥ n − v₂(j) ≥ i` for
  `1 ≤ j < i ≤ n/2`, hence `(1+t)^{2^{n}} = 1` in `A_i = (ℤ/2^i)[t]/(t^i)` (tex 3695–3697);
* `exists_psi` — `Ψ = (1+t)^{ξ}` is a well-defined character `ℤ/2^{n} → A_i^×`
  (tex 3698–3701).
-/

namespace ZInQ.Manuscript.RC.Moving

open scoped BigOperators

section Presentation

variable {A P C Z : Type*} [AddCommGroup A] [AddCommGroup P] [AddCommGroup C] [AddCommGroup Z]
variable {s t : ℕ}

/-- "The kernel and the `q_j` generate the ring-class group" (tex 3581, PROVED). -/
theorem ringClass_generated (δ : A →+ P) (π : P →+ C) (hexact : ∀ p, π p = 0 ↔ ∃ y, δ y = p)
    (q : Fin s → P) (hgen : ∀ c : C, ∃ n : Fin s → ℤ, ∑ j, n j • π (q j) = c) (p : P) :
    ∃ (n : Fin s → ℤ) (y : A), ∑ j, n j • q j + δ y = p := by
  obtain ⟨n, hn⟩ := hgen (π p)
  obtain ⟨y, hy⟩ := (hexact (p - ∑ j, n j • q j)).1 (by
    rw [map_sub, map_sum]
    simp only [map_zsmul]
    rw [hn, sub_self])
  exact ⟨n, y, by rw [hy]; abel⟩

/-- The presentation map `ℤ^s × A → P`, `(n, y) ↦ ∑ n_j q_j + δ y`. -/
def presMap (δ : A →+ P) (q : Fin s → P) : (Fin s → ℤ) × A →+ P :=
  AddMonoidHom.mk' (fun p => ∑ j, p.1 j • q j + δ p.2) (by
    intro a b
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul, Finset.sum_add_distrib,
      map_add]
    abel)

/-- The candidate character `ℤ^s × A → Z`, `(n, y) ↦ ∑ n_j w_j + κ y`. -/
def presChar (κ : A →+ Z) (w : Fin s → Z) : (Fin s → ℤ) × A →+ Z :=
  AddMonoidHom.mk' (fun p => ∑ j, p.1 j • w j + κ p.2) (by
    intro a b
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul, Finset.sum_add_distrib,
      map_add]
    abel)

/-- **The extension criterion (4.4b)** (tex 3566–3595, PROVED).
`δ : A → P` is the injective connecting map `𝐅_r^× → Pic(ℤ + r𝒪_K)`, `π : P → C` the surjection
onto `Cl(K)`, with exactness; `q_j` are the ideal-class lifts of the chosen primes, whose classes
generate `C`; the `m^{(a)}` span the relation module `𝓡 = ker(ℤ^s → C)` (Elliot takes a
`ℤ`-basis; spanning suffices); the principal relations are `∑_j m_j^{(a)} q_j + δ(x_a) = 0`.
Then for every `κ : A → Z` (the power-residue character) and weights `w`, the assignments
`ξ(q_j) = w_j`, `ξ ∘ δ = κ` extend to a homomorphism `ξ : P → Z` **exactly when**
`κ(x_a) = −∑_j m_j^{(a)} w_j` for all `a` — "a complete presentation, not merely necessary
relations".  No class number is divided out. -/
theorem ringClass_extends_iff (δ : A →+ P) (π : P →+ C) (hδ : Function.Injective δ)
    (hexact : ∀ p, π p = 0 ↔ ∃ y, δ y = p)
    (q : Fin s → P) (hgen : ∀ c : C, ∃ n : Fin s → ℤ, ∑ j, n j • π (q j) = c)
    (m : Fin t → Fin s → ℤ)
    (hR : ∀ n : Fin s → ℤ, ∑ j, n j • π (q j) = 0 → ∃ b : Fin t → ℤ, n = ∑ a, b a • m a)
    (x : Fin t → A) (hrel : ∀ a, ∑ j, m a j • q j + δ (x a) = 0)
    (κ : A →+ Z) (w : Fin s → Z) :
    (∃ ξ : P →+ Z, (∀ j, ξ (q j) = w j) ∧ ∀ y, ξ (δ y) = κ y) ↔
      ∀ a, κ (x a) = -∑ j, m a j • w j := by
  constructor
  · rintro ⟨ξ, hq, hδξ⟩ a
    have h := congrArg ξ (hrel a)
    rw [map_add, map_sum, map_zero, hδξ] at h
    simp only [map_zsmul, hq] at h
    exact eq_neg_of_add_eq_zero_right h
  · intro hcond
    have hsurj : Function.Surjective (presMap δ q) := by
      intro p
      obtain ⟨n, y, h⟩ := ringClass_generated δ π hexact q hgen p
      exact ⟨(n, y), h⟩
    have hker : (presMap δ q).ker ≤ (presChar κ w).ker := by
      rintro ⟨n, y⟩ hp
      rw [AddMonoidHom.mem_ker] at hp ⊢
      change ∑ j, n j • q j + δ y = 0 at hp
      change ∑ j, n j • w j + κ y = 0
      -- the relation projects to `𝓡`
      have hπδ : π (δ y) = 0 := (hexact (δ y)).2 ⟨y, rfl⟩
      have hn0 : ∑ j, n j • π (q j) = 0 := by
        have := congrArg π hp
        rw [map_add, map_sum, hπδ, add_zero, map_zero] at this
        simpa only [map_zsmul] using this
      obtain ⟨b, rfl⟩ := hR n hn0
      -- subtracting the basis relations leaves a relation within the kernel
      have hsum : ∀ (v : Fin s → P),
          ∑ j, (∑ a, b a • m a) j • v j = ∑ a, b a • ∑ j, m a j • v j := by
        intro v
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_smul, mul_smul,
          Finset.smul_sum]
        exact Finset.sum_comm
      have hsumZ : ∀ (v : Fin s → Z),
          ∑ j, (∑ a, b a • m a) j • v j = ∑ a, b a • ∑ j, m a j • v j := by
        intro v
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_smul, mul_smul,
          Finset.smul_sum]
        exact Finset.sum_comm
      have hqrel : ∀ a, ∑ j, m a j • q j = -δ (x a) := fun a => eq_neg_of_add_eq_zero_left (hrel a)
      rw [hsum q] at hp
      simp only [hqrel, smul_neg, Finset.sum_neg_distrib] at hp
      have hy : y = ∑ a, b a • x a := by
        apply hδ
        rw [map_sum]
        simp only [map_zsmul]
        exact (neg_add_eq_zero.1 hp).symm
      rw [hsumZ w, hy, map_sum]
      simp only [map_zsmul, hcond, smul_neg, Finset.sum_neg_distrib]
      exact add_neg_cancel _
    let g : {g : (Fin s → ℤ) × A →+ Z // (presMap δ q).ker ≤ g.ker} := ⟨presChar κ w, hker⟩
    let ξ := (presMap δ q).liftOfSurjective hsurj g
    have hcomp : ∀ p, ξ (presMap δ q p) = presChar κ w p := fun p =>
      (presMap δ q).liftOfRightInverse_comp_apply (Function.surjInv hsurj)
        (Function.rightInverse_surjInv hsurj) g p
    refine ⟨ξ, fun j => ?_, fun y => ?_⟩
    · have := hcomp (Pi.single j 1, 0)
      simp only [presMap, presChar, AddMonoidHom.mk'_apply, map_zero, add_zero] at this
      simpa [Pi.single_apply] using this
    · have := hcomp (0, y)
      simpa [presMap, presChar] using this

/-- Conjugation negates the values (tex 3683–3684): `𝔭𝔭̄` is rational principal, so the class of
`𝔭̄` is `−q`, and `ξ(𝔭̄) = −ξ(𝔭)`. -/
theorem conj_value (ξ : P →+ Z) (q qbar : P) (h : qbar = -q) : ξ qbar = -ξ q := by
  rw [h, map_neg]

end Presentation

/-! ### The Kummer relations (4.4a) -/

/-- **The prescriptions respect every Kummer relation** (tex 3551–3559, PROVED arithmetic half).
Weights `w_j = 1` at the active primes (`act j`) and `0` elsewhere.  If `∏ α_a^{b_a}` is a `2^n`-th
power, then (valuation at the odd nonzero-weight primes, unramified in the cyclotomic layer —
the `GLUE` input, see `Interface.lean`) `2^n ∣ ∑_a b_a m_j^{(a)}` at each active `j`; hence the
prescribed exponents `φ_a = −∑_j m_j^{(a)} w_j` satisfy `∑_a b_a φ_a = 0` in `ℤ/2^n`. -/
theorem kummer_prescription_respects {s t : ℕ} (n : ℕ) (m : Fin t → Fin s → ℤ)
    (act : Fin s → Prop) [DecidablePred act] (b : Fin t → ℤ)
    (hb : ∀ j, act j → (2 : ℤ) ^ n ∣ ∑ a, b a * m a j) :
    ∑ a, (b a : ZMod (2 ^ n)) * (-∑ j, (m a j : ZMod (2 ^ n)) * (if act j then 1 else 0)) = 0 := by
  have hint : (2 : ℤ) ^ n ∣ ∑ j, (if act j then 1 else 0) * ∑ a, b a * m a j := by
    refine Finset.dvd_sum fun j _ => ?_
    by_cases hj : act j
    · simp only [hj, ite_true, one_mul]; exact hb j hj
    · simp [hj]
  have hcast : ((∑ j, (if act j then (1 : ℤ) else 0) * ∑ a, b a * m a j : ℤ) : ZMod (2 ^ n)) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast hint
  have : ∑ a, (b a : ZMod (2 ^ n)) * (-∑ j, (m a j : ZMod (2 ^ n)) * (if act j then 1 else 0)) =
      -((∑ j, (if act j then (1 : ℤ) else 0) * ∑ a, b a * m a j : ℤ) : ZMod (2 ^ n)) := by
    push_cast
    simp only [Finset.mul_sum, Finset.sum_neg_distrib, mul_neg]
    rw [Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => ?_
    split_ifs <;> ring
  rw [this, hcast, neg_zero]

/-! ### `Ψ_i = (1+t)^{ξ_i}` (tex 3694–3701) -/

/-- The coefficient ring `A_i = (ℤ/2^i)[t]/(t^i)` (tex 2718–2741). -/
abbrev Acoef (i : ℕ) : Type :=
  Polynomial (ZMod (2 ^ i)) ⧸ Ideal.span {(Polynomial.X : Polynomial (ZMod (2 ^ i))) ^ i}

/-- The variable `t ∈ A_i`. -/
noncomputable def tA (i : ℕ) : Acoef i := Ideal.Quotient.mk _ Polynomial.X

/-- `t^i = 0` in `A_i` (helper). -/
theorem tA_pow_eq_zero (i : ℕ) : tA i ^ i = 0 := by
  rw [tA, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span rfl

/-- `t^k = 0` in `A_i` for `k ≥ i` (helper). -/
theorem tA_pow_eq_zero_of_le (i k : ℕ) (h : i ≤ k) : tA i ^ k = 0 := by
  rw [← Nat.add_sub_cancel' h, pow_add, tA_pow_eq_zero, zero_mul]

/-- A natural number divisible by `2^i` vanishes in `A_i` (helper). -/
theorem natCast_eq_zero_of_dvd (i k : ℕ) (h : 2 ^ i ∣ k) : (k : Acoef i) = 0 := by
  rw [← map_natCast (algebraMap (ZMod (2 ^ i)) (Acoef i)) k,
    (ZMod.natCast_eq_zero_iff k (2 ^ i)).2 h, map_zero]

/-- `v₂ binom(2^n, j) ≥ n − v₂(j) ≥ i` for `1 ≤ j < i`, `n ≥ 2i` (tex 3696–3697, PROVED). -/
theorem choose_two_pow_dvd (i n j : ℕ) (hn : 2 * i ≤ n) (hj : 1 ≤ j) (hji : j < i) :
    2 ^ i ∣ Nat.choose (2 ^ n) j := by
  have hC : Nat.choose (2 ^ n) j ≠ 0 :=
    (Nat.choose_pos (le_of_lt (lt_of_lt_of_le hji
      (le_trans (by omega) (Nat.lt_two_pow_self (n := n)).le)))).ne'
  -- `2^n · binom(2^n − 1, j − 1) = binom(2^n, j) · j`
  have hid : 2 ^ n * Nat.choose (2 ^ n - 1) (j - 1) = Nat.choose (2 ^ n) j * j := by
    obtain ⟨N, hN⟩ : ∃ N, 2 ^ n = N + 1 := ⟨2 ^ n - 1, by have := Nat.one_le_two_pow (n := n); omega⟩
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    rw [hN, Nat.add_sub_cancel, Nat.add_sub_cancel]
    exact Nat.add_one_mul_choose_eq N k
  have hC' : Nat.choose (2 ^ n - 1) (j - 1) ≠ 0 :=
    (Nat.choose_pos (by
      have := Nat.lt_two_pow_self (n := n)
      omega)).ne'
  have hv : padicValNat 2 (Nat.choose (2 ^ n) j) + padicValNat 2 j ≥ n := by
    have := congrArg (padicValNat 2) hid
    rw [padicValNat.mul (by positivity) hC', padicValNat.mul hC (by omega),
      padicValNat.prime_pow] at this
    omega
  have hvj : padicValNat 2 j < i := by
    refine lt_of_le_of_lt (padicValNat_le_nat_log j) ?_
    exact lt_of_lt_of_le (Nat.log_lt_of_lt_pow (by omega) Nat.lt_two_pow_self) hji.le
  exact (pow_dvd_pow 2 (by omega)).trans pow_padicValNat_dvd

/-- **`(1+t)^{2^{n}} = 1` in `A_i` for `n ≥ 2i`** (tex 3695–3697, PROVED). -/
theorem one_add_t_pow_two_pow (i n : ℕ) (hn : 2 * i ≤ n) : (1 + tA i) ^ (2 ^ n) = 1 := by
  rw [add_comm, add_pow]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k _ hk0
    by_cases hki : i ≤ k
    · rw [tA_pow_eq_zero_of_le i k hki]; simp
    · replace hki : k < i := not_le.1 hki
      rw [natCast_eq_zero_of_dvd i _ (choose_two_pow_dvd i n k hn (by omega) hki)]
      simp
  · intro h
    simp at h

/-- **`Ψ = (1+t)^{ξ}` is a well-defined character** (tex 3698–3701, PROVED): there is a
homomorphism `ψ : ℤ/2^{n} → A_i^×` (written additively on the target) with
`ψ(k) = (1+t)^k`; composing with `ξ` gives `Ψ_i`.  An inertia element with `ξ = 1` has
`Ψ = 1 + t`, and an active oriented Frobenius (`ξ = 1`) has odd exponent. -/
theorem exists_psi (i n : ℕ) (hn : 2 * i ≤ n) :
    ∃ ψ : ZMod (2 ^ n) →+ Additive (Acoef i)ˣ,
      ∀ k : ℕ, ((Additive.toMul (ψ (k : ZMod (2 ^ n))) : (Acoef i)ˣ) : Acoef i) = (1 + tA i) ^ k := by
  have hpow := one_add_t_pow_two_pow i n hn
  have hne : 2 ^ n ≠ 0 := by positivity
  let u : (Acoef i)ˣ :=
    { val := 1 + tA i
      inv := (1 + tA i) ^ (2 ^ n - 1)
      val_inv := by rw [← pow_succ', Nat.sub_add_cancel Nat.one_le_two_pow, hpow]
      inv_val := by rw [← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow, hpow] }
  have hu : u ^ (2 ^ n) = 1 := Units.ext (by simp [u, hpow])
  let f : ℤ →+ Additive (Acoef i)ˣ := zmultiplesHom _ (Additive.ofMul u)
  have hf : f ((2 ^ n : ℕ) : ℤ) = 0 := by
    simp only [f, zmultiplesHom_apply, natCast_zsmul]
    rw [← ofMul_pow, hu]
    rfl
  refine ⟨ZMod.lift (2 ^ n) ⟨f, hf⟩, fun k => ?_⟩
  have : (k : ZMod (2 ^ n)) = ((k : ℤ) : ZMod (2 ^ n)) := by push_cast; rfl
  rw [this, ZMod.lift_coe]
  simp only [f, zmultiplesHom_apply, natCast_zsmul]
  rw [← ofMul_pow, toMul_ofMul, Units.val_pow_eq_pow_val]

/-- **The local model (4.4) at the moving prime** (consumer check, tex 3471–3477 with
3670–3677 and 3695–3698; gap P-a of the host check of `ex:arith-paired-functional`, PROVED).
At the moving prime `r` the inertia generator acts as `g = 1 + t`, and
`DC − CA = −(N_r(g) − 1)(g − 1) = −((r−1)/2)·((1+t)² − 1)` for
`N_r(g) = (r+1)/2 + ((r−1)/2) g`.  This vanishes in `A_i` as soon as `r ≡ 1 (mod 2^{i+1})`, which
the moving character supplies by taking `B ≥ i + 1`. -/
theorem moving_prime_DC_CA (i r : ℕ) (hr : 2 ^ (i + 1) ∣ r - 1) :
    (((r - 1) / 2 : ℕ) : Acoef i) * ((1 + tA i) ^ 2 - 1) = 0 := by
  have h : 2 ^ i ∣ (r - 1) / 2 := by
    obtain ⟨c, hc⟩ := hr
    refine ⟨c, ?_⟩
    rw [hc, pow_succ, mul_assoc, mul_comm 2 c, ← mul_assoc, Nat.mul_div_cancel _ two_pos]
  rw [natCast_eq_zero_of_dvd i _ h, zero_mul]

end ZInQ.Manuscript.RC.Moving

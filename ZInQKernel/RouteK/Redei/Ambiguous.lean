import ZInQKernel.RouteK.Redei.Primes

/-!
# Rédei's formula, step 3: ambiguous classes (G1) (`docs/research/redei-plan.md` §3.2)

`K = QNeg n`, `O = 𝓞 K`, `σ` the nontrivial automorphism, `n` odd squarefree.

* Hilbert 90 at the integral level: `ambig_normZ_eq` (`x σI = y I` gives `N x = N y`) and
  `ambig_hilbert90` (then some `νI`, `ν ≠ 0`, is σ-invariant);
* `psi : 𝔽₂^{ramSet n} → Cl`, `ψ(e) = Π_p [𝔭_p]^{e_p}`; `psi_single`, `psi_ones` (`ψ` kills the
  vector of `(√−n)`);
* `mem_range_psi_of_conj_eq`: a σ-invariant ideal has its class in `im ψ` (strong induction on the
  norm: peel off `pO` for split and inert `p`, and `𝔭_p` for ramified `p`);
* `range_psi : im ψ = Cl[2]`, and `card_ker_sq_le : #Cl[2] ≤ 2^{t−1}`, `t = #ramSet n`.

`psi` is a homomorphism for every `n`: the class of `𝔭_p` is used only when its square is `1`
(always the case for `n` odd squarefree, `ambigClass_eq`), so `psi_single` needs `n` odd squarefree.
-/

noncomputable section

open NumberField Pointwise
open scoped nonZeroDivisors

namespace ZInQ.RouteK.Redei

open ZInQ.RouteK.Rank5b

section Ambiguous

variable (n : ℕ) [NeZero n]

local notation "K" => QNeg n
local notation "O" => 𝓞 (QNeg n)

variable {n}

/-! ### The action of `σ` on elements and principal ideals -/

theorem ambig_smul_smul (σ : K ≃ₐ[ℚ] K) (hσ : σ ≠ 1) (x : O) : σ • σ • x = x := by
  apply RingOfIntegers.ext
  simp only [RingOfIntegers.coe_eq_algebraMap, algebraMap_smul]
  exact conj_conj σ hσ _

theorem ambig_smul_span (σ : K ≃ₐ[ℚ] K) (x : O) :
    σ • Ideal.span {x} = Ideal.span {σ • x} := by
  rw [Ideal.pointwise_smul_def, Ideal.map_span, Set.image_singleton]
  rfl

theorem ambig_smul_ne_zero (σ : K ≃ₐ[ℚ] K) {x : O} (hx : x ≠ 0) : σ • x ≠ 0 := by
  intro h
  apply hx
  apply RingOfIntegers.ext
  have := congrArg (fun z : O => (z : K)) h
  simp only [RingOfIntegers.coe_eq_algebraMap, algebraMap_smul, map_zero] at this ⊢
  exact (map_eq_zero_iff σ σ.injective).1 this

/-! ### Hilbert 90 at the integral level -/

variable (n) in
/-- If `x σI = y I` then `N x = N y`: take ideal norms (`N σI = N I`, norms of elements are
`≥ 0`). -/
theorem ambig_normZ_eq (σ : K ≃ₐ[ℚ] K) {I : Ideal O} (hI : I ≠ ⊥) {x y : O}
    (h : Ideal.span {x} * (σ • I) = Ideal.span {y} * I) :
    Algebra.norm ℤ x = Algebra.norm ℤ y := by
  have hN := congrArg Ideal.absNorm h
  rw [map_mul, map_mul, absNorm_smul n σ, Ideal.absNorm_span_singleton,
    Ideal.absNorm_span_singleton] at hN
  have hI0 : Ideal.absNorm I ≠ 0 := by
    rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have h1 : (Algebra.norm ℤ x).natAbs = (Algebra.norm ℤ y).natAbs :=
    Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hI0) hN
  have hx := normZ_nonneg (n := n) x
  have hy := normZ_nonneg (n := n) y
  omega

variable (n) in
/-- **Hilbert 90** for ideals: if `x σI = y I` with `x ≠ 0`, then `νI` is σ-invariant for some
`ν ≠ 0` (`ν = σx (x + y)`, or `ν = 1` when `x + y = 0`). -/
theorem ambig_hilbert90 (σ : K ≃ₐ[ℚ] K) (hσ : σ ≠ 1) {I : Ideal O} (hI : I ≠ ⊥) {x y : O}
    (hx : x ≠ 0) (h : Ideal.span {x} * (σ • I) = Ideal.span {y} * I) :
    ∃ ν : O, ν ≠ 0 ∧ σ • (Ideal.span {ν} * I) = Ideal.span {ν} * I := by
  have hN := ambig_normZ_eq n σ hI h
  have hN' : x * σ • x = y * σ • y := by
    rw [← normZ_eq_mul_conj σ hσ, ← normZ_eq_mul_conj σ hσ, hN]
  have hx0 : Ideal.span {x} ≠ 0 := by
    rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  by_cases hxy : x + y = 0
  · refine ⟨1, one_ne_zero, ?_⟩
    rw [Ideal.span_singleton_one, Ideal.top_mul]
    have hy : y = -x := by linear_combination hxy
    rw [hy, Ideal.span_singleton_neg] at h
    exact mul_left_cancel₀ hx0 h
  · refine ⟨σ • x * (x + y), mul_ne_zero (ambig_smul_ne_zero σ hx) hxy, ?_⟩
    set ν := σ • x * (x + y) with hν
    have hσν : σ • ν = x * (σ • x + σ • y) := by
      rw [hν, smul_mul', ambig_smul_smul σ hσ, smul_add]
    have key : y * σ • ν = x * ν := by
      rw [hσν, hν]; linear_combination x * hN'.symm
    apply mul_left_cancel₀ hx0
    calc Ideal.span {x} * σ • (Ideal.span {ν} * I)
        = Ideal.span {σ • ν} * (Ideal.span {x} * σ • I) := by
          rw [smul_mul', ambig_smul_span]; ring
      _ = Ideal.span {σ • ν} * (Ideal.span {y} * I) := by rw [h]
      _ = Ideal.span {y * σ • ν} * I := by
          rw [← Ideal.span_singleton_mul_span_singleton]; ring
      _ = Ideal.span {x * ν} * I := by rw [key]
      _ = Ideal.span {x} * (Ideal.span {ν} * I) := by
          rw [← Ideal.span_singleton_mul_span_singleton]; ring

/-! ### The map `ψ` -/

open Classical in
variable (n) in
/-- The class of `𝔭_p`, when its square is trivial (always, for `n` odd squarefree). -/
def ambigClass (p : ramSet n) : ClassGroup O :=
  if ClassGroup.mk0 ⟨ramIdeal n p, ramIdeal_mem n p⟩ ^ 2 = 1 then
    ClassGroup.mk0 ⟨ramIdeal n p, ramIdeal_mem n p⟩ else 1

theorem ambigClass_sq (p : ramSet n) : ambigClass n p ^ 2 = 1 := by
  unfold ambigClass; split_ifs with h
  · exact h
  · exact one_pow 2

theorem ambigClass_eq (hn : Odd n) (hsq : Squarefree n) (p : ramSet n) :
    ambigClass n p = ClassGroup.mk0 ⟨ramIdeal n p, ramIdeal_mem n p⟩ := by
  unfold ambigClass
  split_ifs with hc
  · rfl
  exfalso; apply hc
  rw [← map_pow]
  have h2 : (⟨ramIdeal n p, ramIdeal_mem n p⟩ : (Ideal O)⁰) ^ 2 =
      ⟨Ideal.span {((p : ℕ) : O)}, by
        rw [← (ramIdeal_spec n hn hsq p.2).2.1]; exact pow_mem (ramIdeal_mem n p) 2⟩ := by
    ext1; exact (ramIdeal_spec n hn hsq p.2).2.1
  rw [h2, ClassGroup.mk0_eq_one_iff]
  exact ⟨⟨_, rfl⟩⟩

theorem ambig_pow_val_add {G : Type*} [Monoid G] {c : G} (hc : c ^ 2 = 1) (a b : ZMod 2) :
    c ^ (a + b).val = c ^ a.val * c ^ b.val := by
  have hmod : ∀ k : ℕ, c ^ k = c ^ (k % 2) := fun k => by
    conv_lhs => rw [← Nat.div_add_mod k 2, pow_add, pow_mul, hc, one_pow, one_mul]
  rw [← pow_add, ZMod.val_add, ← hmod]

variable (n) in
/-- **The ambiguous classes**: `ψ(e) = Π_p [𝔭_p]^{e_p}`. -/
def psi : Multiplicative (ramSet n → ZMod 2) →* ClassGroup O where
  toFun e := ∏ p, ambigClass n p ^ (Multiplicative.toAdd e p).val
  map_one' := by
    simp only [toAdd_one, Pi.zero_apply, ZMod.val_zero, pow_zero, Finset.prod_const_one]
  map_mul' e f := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [toAdd_mul, Pi.add_apply, ambig_pow_val_add (ambigClass_sq p)]

theorem psi_apply (e : Multiplicative (ramSet n → ZMod 2)) :
    psi n e = ∏ p, ambigClass n p ^ (Multiplicative.toAdd e p).val := rfl

theorem psi_sq (e : Multiplicative (ramSet n → ZMod 2)) : psi n e ^ 2 = 1 := by
  rw [← map_pow, ← map_one (psi n)]
  congr 1
  ext p
  simp only [toAdd_pow, Pi.smul_apply, toAdd_one, Pi.zero_apply, nsmul_eq_mul, Nat.cast_ofNat]
  exact (show (2 : ZMod 2) = 0 from rfl) ▸ zero_mul _

variable (n) in
theorem psi_single (hn : Odd n) (hsq : Squarefree n) (p : ramSet n) :
    psi n (Multiplicative.ofAdd (Pi.single p 1)) =
      ClassGroup.mk0 ⟨ramIdeal n p, ramIdeal_mem n p⟩ := by
  rw [psi_apply, ← ambigClass_eq hn hsq p, Finset.prod_eq_single p]
  · simp [show (1 : ZMod 2).val = 1 from rfl]
  · intro q _ hq
    simp [hq]
  · intro h; exact absurd (Finset.mem_univ p) h

theorem mk0_prod_ramIdeal (s : Finset ℕ) :
    ∏ p ∈ s, ClassGroup.mk0 (⟨ramIdeal n p, ramIdeal_mem n p⟩ : (Ideal O)⁰) =
      ClassGroup.mk0 (⟨∏ p ∈ s, ramIdeal n p,
        prod_mem fun p _ => ramIdeal_mem n p⟩ : (Ideal O)⁰) := by
  rw [← map_prod]
  congr 1
  ext1
  simp

variable (n) in
/-- The vector of `(√−n)` is in the kernel of `ψ`. -/
theorem psi_ones (hn : Odd n) (hsq : Squarefree n) :
    psi n (Multiplicative.ofAdd fun p : ramSet n =>
      if (p : ℕ) ∈ n.primeFactors then (1 : ZMod 2) else 0) = 1 := by
  rw [psi_apply]
  have h1 : ∀ p : ramSet n, ambigClass n p ^ (Multiplicative.toAdd (Multiplicative.ofAdd
      fun p : ramSet n => if (p : ℕ) ∈ n.primeFactors then (1 : ZMod 2) else 0) p).val =
      if (p : ℕ) ∈ n.primeFactors then
        ClassGroup.mk0 (⟨ramIdeal n p, ramIdeal_mem n p⟩ : (Ideal O)⁰) else 1 := by
    intro p
    rw [toAdd_ofAdd, ambigClass_eq hn hsq]
    split_ifs <;> simp [show (1 : ZMod 2).val = 1 from rfl]
  rw [Finset.prod_congr rfl fun p _ => h1 p]
  rw [Finset.prod_coe_sort (ramSet n) (fun q : ℕ => if q ∈ n.primeFactors then
    ClassGroup.mk0 (⟨ramIdeal n q, ramIdeal_mem n q⟩ : (Ideal O)⁰) else 1),
    Finset.prod_ite_mem, Finset.inter_eq_right.2 fun p hp => mem_ramSet_of_mem_primeFactors hp,
    mk0_prod_ramIdeal, ClassGroup.mk0_eq_one_iff]
  rw [← span_omega n hn hsq]
  exact ⟨⟨_, rfl⟩⟩

end Ambiguous

end ZInQ.RouteK.Redei

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

/-! ### σ-invariant ideals -/

omit [NeZero n] in
theorem ambig_two_mem_ramSet (h1 : n % 4 = 1) : 2 ∈ ramSet n := by
  unfold ramSet
  split_ifs with h3
  · omega
  · exact Finset.mem_insert_self _ _

variable (n) in
/-- A nonzero proper σ-invariant ideal `J` has a nonzero proper σ-invariant divisor `Q` with class
in `im ψ`: `pO` for `p` split or inert, `𝔭_p` for `p` ramified. -/
theorem ambig_exists_dvd (σ : K ≃ₐ[ℚ] K) (hσ : σ ≠ 1) (hn : Odd n) (hsq : Squarefree n)
    (J : Ideal O) (hJ : J ≠ ⊥) (hJt : J ≠ ⊤) (hs : σ • J = J) :
    ∃ Q : Ideal O, Q ∣ J ∧ Q ≠ ⊤ ∧ σ • Q = Q ∧ ∃ hQ : Q ∈ (Ideal O)⁰,
      ClassGroup.mk0 ⟨Q, hQ⟩ ∈ (psi n).range := by
  obtain ⟨P, hPmax, hJP⟩ := Ideal.exists_le_maximal J hJt
  have hP0 : P ≠ ⊥ := fun h => hJ (le_bot_iff.1 (h ▸ hJP))
  obtain ⟨p, hp, hlies⟩ := exists_prime_liesOver P hP0
  have hpO : Ideal.span {(p : O)} ∈ (Ideal O)⁰ := by
    refine mem_nonZeroDivisors_of_ne_zero ?_
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact natCast_ne_zero_O hp.ne_zero
  have hpO1 : ClassGroup.mk0 ⟨Ideal.span {(p : O)}, hpO⟩ ∈ (psi n).range := by
    rw [(ClassGroup.mk0_eq_one_iff hpO).2 ⟨⟨_, rfl⟩⟩]
    exact Subgroup.one_mem _
  have hpOt : Ideal.span {(p : O)} ≠ ⊤ := fun h =>
    Ideal.IsPrime.ne_top' (eq_top_iff.2 (h ▸ span_le_of_liesOver P))
  rcases prime_trichotomy n σ hσ hp P with ⟨hne, hmul, -⟩ | ⟨-, hP, -⟩ | ⟨hsP, h2, -⟩
  · refine ⟨_, ?_, hpOt, smul_span_natCast σ p, hpO, hpO1⟩
    have hJs : J ≤ σ • P := by
      rw [← hs]; exact Ideal.pointwise_smul_le_pointwise_smul_iff.2 hJP
    have hmax := smul_isMaximal σ P
    have hcop : P ⊔ σ • P = ⊤ := Ideal.IsMaximal.coprime_of_ne inferInstance hmax (Ne.symm hne)
    rw [← hmul, Ideal.dvd_iff_le, Ideal.mul_eq_inf_of_coprime hcop]
    exact le_inf hJP hJs
  · refine ⟨_, ?_, hpOt, smul_span_natCast σ p, hpO, hpO1⟩
    rw [← hP]; exact Ideal.dvd_iff_le.2 hJP
  · have hpr : p ∈ ramSet n := by
      rcases dvd_of_ramified n hp P h2 with hpn | ⟨rfl, h1⟩
      · exact mem_ramSet_of_mem_primeFactors
          (Nat.mem_primeFactors.2 ⟨hp, hpn, NeZero.ne n⟩)
      · exact ambig_two_mem_ramSet h1
    have hPe : P = ramIdeal n p := eq_ramIdeal_of_liesOver hn hsq hpr P
    refine ⟨P, Ideal.dvd_iff_le.2 hJP, Ideal.IsPrime.ne_top', hsP, hPe ▸ ramIdeal_mem n p, ?_⟩
    refine ⟨Multiplicative.ofAdd (Pi.single ⟨p, hpr⟩ 1), ?_⟩
    rw [psi_single n hn hsq]
    congr 2
    exact hPe.symm

variable (n) in
/-- A σ-invariant ideal has its class in the subgroup generated by the ramified primes. -/
theorem mem_range_psi_of_conj_eq (σ : K ≃ₐ[ℚ] K) (hσ : σ ≠ 1) (hn : Odd n) (hsq : Squarefree n)
    (I : (Ideal O)⁰) (hI : σ • (I : Ideal O) = I) : ClassGroup.mk0 I ∈ (psi n).range := by
  suffices H : ∀ k, ∀ J : Ideal O, ∀ hJ : J ∈ (Ideal O)⁰, σ • J = J → Ideal.absNorm J = k →
      ClassGroup.mk0 ⟨J, hJ⟩ ∈ (psi n).range from H _ I I.2 hI rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro J hJ hs hk
  by_cases hJt : J = ⊤
  · subst hJt
    rw [(ClassGroup.mk0_eq_one_iff hJ).2 ⟨⟨1, Ideal.span_singleton_one.symm⟩⟩]
    exact Subgroup.one_mem _
  have hJ0 : J ≠ ⊥ := nonZeroDivisors.ne_zero hJ
  obtain ⟨Q, ⟨J', rfl⟩, hQt, hQs, hQ, hQr⟩ := ambig_exists_dvd n σ hσ hn hsq J hJ0 hJt hs
  have hQ0 : Q ≠ 0 := nonZeroDivisors.ne_zero hQ
  have hJ'0 : J' ≠ 0 := right_ne_zero_of_mul (nonZeroDivisors.ne_zero hJ)
  have hJ' : J' ∈ (Ideal O)⁰ := mem_nonZeroDivisors_of_ne_zero hJ'0
  have hs' : σ • J' = J' := by
    rw [smul_mul', hQs] at hs
    exact mul_left_cancel₀ hQ0 hs
  have hlt : Ideal.absNorm J' < k := by
    rw [← hk, map_mul]
    have h1 : Ideal.absNorm Q ≠ 1 := by rwa [Ne, Ideal.absNorm_eq_one_iff]
    have h0 : Ideal.absNorm Q ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
    have h0' : Ideal.absNorm J' ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
    have : 2 ≤ Ideal.absNorm Q := by omega
    have : 0 < Ideal.absNorm J' := Nat.pos_of_ne_zero h0'
    nlinarith
  have e : (⟨Q * J', hJ⟩ : (Ideal O)⁰) = ⟨Q, hQ⟩ * ⟨J', hJ'⟩ := rfl
  rw [e, map_mul]
  exact Subgroup.mul_mem _ hQr (ih _ hlt J' hJ' hs' rfl)

/-! ### `Cl[2] = im ψ` -/

variable (n) in
/-- **(G1)** `Cl[2] = im ψ`. -/
theorem range_psi (hn : Odd n) (hsq : Squarefree n) :
    (psi n).range = (powMonoidHom 2 : ClassGroup O →* ClassGroup O).ker := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨e, rfl⟩
    rw [MonoidHom.mem_ker, powMonoidHom_apply]
    exact psi_sq e
  · intro c hc
    rw [MonoidHom.mem_ker, powMonoidHom_apply] at hc
    obtain ⟨σ, hσ⟩ := exists_conj_ne_one (n := n)
    obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
    have hI0 : (I : Ideal O) ≠ ⊥ := nonZeroDivisors.ne_zero I.2
    have hsI : σ • (I : Ideal O) ∈ (Ideal O)⁰ :=
      mem_nonZeroDivisors_of_ne_zero (smul_ne_bot σ hI0)
    have hmul : ClassGroup.mk0 I * ClassGroup.mk0 ⟨σ • (I : Ideal O), hsI⟩ = 1 := by
      rw [← map_mul]
      have hm : ((I * ⟨σ • (I : Ideal O), hsI⟩ : (Ideal O)⁰) : Ideal O).IsPrincipal := by
        change ((I : Ideal O) * σ • (I : Ideal O)).IsPrincipal
        rw [mul_conj_ideal n σ hσ]
        exact ⟨⟨_, rfl⟩⟩
      exact (ClassGroup.mk0_eq_one_iff _).2 hm
    have heq : ClassGroup.mk0 ⟨σ • (I : Ideal O), hsI⟩ = ClassGroup.mk0 I := by
      calc ClassGroup.mk0 ⟨σ • (I : Ideal O), hsI⟩
          = (ClassGroup.mk0 I * ClassGroup.mk0 I) * ClassGroup.mk0 ⟨σ • (I : Ideal O), hsI⟩ := by
            rw [← pow_two, hc, one_mul]
        _ = ClassGroup.mk0 I := by rw [mul_assoc, hmul, mul_one]
    obtain ⟨x, y, hx, -, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.1 heq
    obtain ⟨ν, hν, hνs⟩ := ambig_hilbert90 n σ hσ hI0 hx hxy
    have hνm : Ideal.span {ν} ∈ (Ideal O)⁰ := by
      refine mem_nonZeroDivisors_of_ne_zero ?_
      rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    let J : (Ideal O)⁰ := ⟨Ideal.span {ν}, hνm⟩ * I
    have hJs : σ • (J : Ideal O) = J := by
      rw [show (J : Ideal O) = Ideal.span {ν} * (I : Ideal O) from rfl]; exact hνs
    have hJ := mem_range_psi_of_conj_eq n σ hσ hn hsq J hJs
    rwa [map_mul, (ClassGroup.mk0_eq_one_iff hνm).2 ⟨⟨_, rfl⟩⟩, one_mul] at hJ

variable (n) in
/-- `#Cl[2] ≤ 2^{t−1}`, `t = #ramSet n` (`ψ` is onto `Cl[2]` and kills the nonzero vector of
`(√−n)`). -/
theorem card_ker_sq_le (hn : Odd n) (hsq : Squarefree n) (h1 : 1 < n) :
    Nat.card (powMonoidHom 2 : ClassGroup O →* ClassGroup O).ker ≤
      2 ^ ((ramSet n).card - 1) := by
  rw [← range_psi n hn hsq]
  have hcard := Subgroup.card_ker_mul_card_range (psi n)
  have hdom : Nat.card (Multiplicative (ramSet n → ZMod 2)) = 2 ^ (ramSet n).card := by
    rw [Nat.card_eq_fintype_card]; simp
  rw [hdom] at hcard
  have hker : 1 < Nat.card (psi n).ker := by
    rw [Subgroup.one_lt_card_iff_ne_bot]
    intro hbot
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (Nat.ne_of_gt h1)
    have hpf : p ∈ n.primeFactors := Nat.mem_primeFactors.2 ⟨hp, hpn, NeZero.ne n⟩
    have hmem := psi_ones n hn hsq
    rw [← MonoidHom.mem_ker, hbot, Subgroup.mem_bot] at hmem
    have := congrFun (congrArg Multiplicative.toAdd hmem) ⟨p, mem_ramSet_of_mem_primeFactors hpf⟩
    simp at this
    exact NeZero.ne n (this hp hpn)
  have ht : (ramSet n).card ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hcard
    have : 0 < Nat.card (psi n).range := Nat.card_pos
    nlinarith
  obtain ⟨t, ht'⟩ := Nat.exists_eq_succ_of_ne_zero ht
  rw [ht', pow_succ] at hcard
  rw [ht', Nat.succ_sub_one]
  nlinarith

end Ambiguous

end ZInQ.RouteK.Redei

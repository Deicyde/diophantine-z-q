import ZInQKernel.Model.Field

/-!
# The primes of `ℤ[√2]` above an odd prime

Blueprint: `multiplication/local/primes-above-p.md`.

Let `p` be an odd prime and `σ = star` the conjugation `s ↦ -s`.

1. If `r² ≡ 2 (mod p)`, the ideals `𝔭_r = (p, s - r)` and `𝔭_{-r} = (p, s + r)` are distinct
   primes, `a + b s ↦ a + b r` induces `ℤ[s]/𝔭_r ≅ 𝔽_p`, `(p) = 𝔭_r 𝔭_{-r}` and
   `σ(𝔭_r) = 𝔭_{-r}` (`primeR_split`); otherwise `(p)` is prime with `p²` residues and
   `σ(p) = (p)` (`primeP_inert`). In both cases these are all the primes containing `p`.
2. `p` is unramified: for a prime element `π ∣ p`, `v_π(q) = v_p(q)` for `q ∈ ℚ`
   (`vp_ratCast`).
3. `v_{σπ}(y) = v_π(σ y)` (`vp_star`).
4. If `v_π(y) ≥ m` and `v_{σπ}(y) ≥ m` then `v_p(Tr y) ≥ m` (`vp_trace_ge`).

Primes of `ℤ[s]` are given by prime elements `π` (`ℤ[s]` is a principal ideal domain), with the
model chapter's valuation `vp π`.
-/

namespace ZInQ.Mult

open QuadraticAlgebra

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Divisibility by rational integers in `ℤ[s]` -/

omit hp in
theorem natCast_dvd_iff (z : Zs) : (p : Zs) ∣ z ↔ (p : ℤ) ∣ z.re ∧ (p : ℤ) ∣ z.im := by
  rw [← Zs.intCast_dvd_iff]; push_cast; rfl

theorem two_ne_zero_zmod (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this)

/-! ### The residue maps at a split prime -/

/-- The residue map `ℤ[s] → 𝔽_p`, `a + b s ↦ a + b r`, for `r² = 2` in `𝔽_p`. -/
def residueAt (r : ZMod p) (hr : r ^ 2 = 2) : Zs →+* ZMod p :=
  (QuadraticAlgebra.lift ⟨r, by rw [← sq, hr]; simp⟩).toRingHom

@[simp] theorem residueAt_apply (r : ZMod p) (hr : r ^ 2 = 2) (z : Zs) :
    residueAt r hr z = (z.re : ZMod p) + (z.im : ZMod p) * r := by
  simp [residueAt, zsmul_eq_mul]

theorem residueAt_surjective (r : ZMod p) (hr : r ^ 2 = 2) :
    Function.Surjective (residueAt r hr) := by
  intro x; refine ⟨⟨x.val, 0⟩, ?_⟩; simp

/-- `𝔭_r = (p, s - r)`. -/
def primeR (p : ℕ) (r : ℤ) : Ideal Zs := Ideal.span {(p : Zs), sqrt2Z - (r : Zs)}

theorem ker_residueAt {r : ℤ} (hr : (r : ZMod p) ^ 2 = 2) :
    RingHom.ker (residueAt (r : ZMod p) hr) = primeR p r := by
  ext z
  rw [RingHom.mem_ker, residueAt_apply, primeR, Ideal.mem_span_pair]
  constructor
  · intro h
    have h' : ((z.re + z.im * r : ℤ) : ZMod p) = 0 := by push_cast; exact h
    obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h'
    refine ⟨(k : Zs), (z.im : Zs), ?_⟩
    ext <;> simp [sqrt2Z]
    linarith
  · rintro ⟨a, b, rfl⟩
    simp [sqrt2Z]
    linear_combination (-((b.im : ℤ) : ZMod p)) * hr

theorem primeR_isMaximal {r : ℤ} (hr : (r : ZMod p) ^ 2 = 2) : (primeR p r).IsMaximal := by
  rw [← ker_residueAt hr]
  exact RingHom.ker_isMaximal_of_surjective _ (residueAt_surjective _ hr)

/-- `ℤ[s]/𝔭_r ≅ 𝔽_p`, induced by `a + b s ↦ a + b r`. -/
noncomputable def quotPrimeREquiv {r : ℤ} (hr : (r : ZMod p) ^ 2 = 2) :
    Zs ⧸ primeR p r ≃+* ZMod p :=
  (Ideal.quotEquivOfEq (ker_residueAt hr).symm).trans
    (RingHom.quotientKerEquivOfSurjective (residueAt_surjective _ hr))

theorem quotPrimeREquiv_mk {r : ℤ} (hr : (r : ZMod p) ^ 2 = 2) (z : Zs) :
    quotPrimeREquiv hr (Ideal.Quotient.mk _ z) = (z.re : ZMod p) + (z.im : ZMod p) * r := by
  simp [quotPrimeREquiv]

theorem neg_sq_eq {r : ℤ} (hr : (r : ZMod p) ^ 2 = 2) : ((-r : ℤ) : ZMod p) ^ 2 = 2 := by
  push_cast; rw [neg_sq]; exact hr

/-- **Part 1, split case.** If `r² ≡ 2 (mod p)` with `p` odd, then `𝔭_r` and `𝔭_{-r}` are
distinct primes, `ℤ[s]/𝔭_r ≅ 𝔽_p` (by `quotPrimeREquiv`), `(p) = 𝔭_r 𝔭_{-r}`,
`σ(𝔭_r) = 𝔭_{-r}`, and every prime containing `p` is `𝔭_r` or `𝔭_{-r}`. -/
theorem primeR_split (hp2 : p ≠ 2) {r : ℤ} (hr : (r : ZMod p) ^ 2 = 2) :
    (primeR p r).IsPrime ∧ (primeR p (-r)).IsPrime ∧ primeR p r ≠ primeR p (-r) ∧
      Ideal.span {(p : Zs)} = primeR p r * primeR p (-r) ∧
      (primeR p r).map (starRingEnd Zs) = primeR p (-r) ∧
      ∀ P : Ideal Zs, P.IsPrime → (p : Zs) ∈ P → P = primeR p r ∨ P = primeR p (-r) := by
  have h2 := two_ne_zero_zmod hp2
  have hr0 : (r : ZMod p) ≠ 0 := by
    intro h; rw [h] at hr; simp at hr; exact h2 hr.symm
  have hmax := primeR_isMaximal hr
  have hmax' := primeR_isMaximal (neg_sq_eq hr)
  -- `p ∣ r² - 2`
  obtain ⟨c, hc⟩ : (p : ℤ) ∣ r ^ 2 - 2 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [hr, sub_self]
  have hprod : Ideal.span {(p : Zs)} = primeR p r * primeR p (-r) := by
    apply le_antisymm
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      -- `p = α p² + β (p (s + r) - (s - r) p)` with `α p + 2 β r = 1`
      have hcop : IsCoprime (p : ℤ) (2 * r) := by
        refine (Nat.prime_iff_prime_int.mp hp.out).irreducible.coprime_iff_not_dvd.mpr ?_
        intro hd
        have : ((2 * r : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hd
        push_cast at this
        exact mul_ne_zero h2 hr0 this
      obtain ⟨α, β, hαβ⟩ := hcop
      have hp1 : (p : Zs) ∈ primeR p r := Ideal.subset_span (by simp)
      have hp2' : (p : Zs) ∈ primeR p (-r) := Ideal.subset_span (by simp)
      have hs1 : sqrt2Z - (r : Zs) ∈ primeR p r := Ideal.subset_span (by simp)
      have hs2 : sqrt2Z - ((-r : ℤ) : Zs) ∈ primeR p (-r) := Ideal.subset_span (by simp)
      have key : (p : Zs) = (α : Zs) * ((p : Zs) * (p : Zs)) +
          (β : Zs) * ((p : Zs) * (sqrt2Z - ((-r : ℤ) : Zs)) - (sqrt2Z - (r : Zs)) * (p : Zs)) := by
        have : ((α * p + β * (2 * r) : ℤ) : Zs) = 1 := by rw [hαβ]; simp
        push_cast at this ⊢
        linear_combination (-(p : Zs)) * this
      rw [key]
      refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul hp1 hp2'))
        (Ideal.mul_mem_left _ _ (Ideal.sub_mem _ (Ideal.mul_mem_mul hp1 hs2)
          (Ideal.mul_mem_mul hs1 hp2')))
    · rw [Ideal.mul_le]
      intro x hx y hy
      obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.mp hx
      obtain ⟨a', b', rfl⟩ := Ideal.mem_span_pair.mp hy
      rw [Ideal.mem_span_singleton]
      have hs : sqrt2Z * sqrt2Z = 2 := by ext <;> simp [sqrt2Z]
      refine ⟨a * a' * p + a * b' * (sqrt2Z + r) + b * a' * (sqrt2Z - r) + b * b' * (-c), ?_⟩
      have hc' : ((r : Zs)) ^ 2 - 2 = (p : Zs) * c := by exact_mod_cast hc
      push_cast
      linear_combination (b * b') * hs + (-(b * b')) * hc'
  refine ⟨hmax.isPrime, hmax'.isPrime, ?_, hprod, ?_, ?_⟩
  · intro heq
    have hmem : sqrt2Z - ((-r : ℤ) : Zs) ∈ primeR p r := heq ▸ Ideal.subset_span (by simp)
    rw [← ker_residueAt hr, RingHom.mem_ker, residueAt_apply] at hmem
    simp [sqrt2Z] at hmem
    have : (2 : ZMod p) * r = 0 := by linear_combination hmem
    exact mul_ne_zero h2 hr0 this
  · rw [primeR, Ideal.map_span, Set.image_insert_eq, Set.image_singleton, map_natCast]
    ext z
    rw [Ideal.mem_span_pair, primeR, Ideal.mem_span_pair]
    have hst : (starRingEnd Zs) (sqrt2Z - (r : Zs)) = -(sqrt2Z - ((-r : ℤ) : Zs)) := by
      ext <;> simp [sqrt2Z, starRingEnd_apply]
    rw [hst]
    constructor
    · rintro ⟨a, b, rfl⟩; exact ⟨a, -b, by ring⟩
    · rintro ⟨a, b, rfl⟩; exact ⟨a, -b, by ring⟩
  · intro P hP hpP
    have hle : primeR p r * primeR p (-r) ≤ P := by
      rw [← hprod, Ideal.span_le, Set.singleton_subset_iff]; exact hpP
    have hPtop : P ≠ ⊤ := hP.ne_top
    rcases hP.mul_le.mp hle with h | h
    · exact Or.inl (hmax.eq_of_le hPtop h).symm
    · exact Or.inr (hmax'.eq_of_le hPtop h).symm

/-! ### The inert case -/

/-- If `2` is not a square mod `p`, then `p` is a prime element of `ℤ[s]`. -/
theorem prime_natCast_of_not_isSquare (hsq : ¬ IsSquare (2 : ZMod p)) : Prime (p : Zs) := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have := congrArg QuadraticAlgebra.re h
    simp at this; exact hp.out.ne_zero this
  · intro hu
    have h := Zs.isUnit_iff_norm.mp hu
    have hre : (p : Zs).re = p := by simp
    have him : (p : Zs).im = 0 := by simp
    rw [Zs.norm_eq, hre, him] at h
    have : (2 : ℤ) ≤ p := by exact_mod_cast hp.out.two_le
    rcases h with h | h <;> nlinarith
  · intro x y hxy
    by_contra hcon
    push Not at hcon
    obtain ⟨hx, hy⟩ := hcon
    -- the norm of `x` is prime to `p`
    have hN : ¬ (p : ℤ) ∣ QuadraticAlgebra.norm x := by
      intro hd
      rw [Zs.norm_eq] at hd
      have hd' : ((x.re : ZMod p)) ^ 2 - 2 * (x.im : ZMod p) ^ 2 = 0 := by
        have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hd; push_cast at this; exact this
      by_cases hb : (x.im : ZMod p) = 0
      · rw [hb] at hd'; simp at hd'
        apply hx
        rw [natCast_dvd_iff]
        exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hd',
          (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hb⟩
      · apply hsq
        refine ⟨x.re / x.im, ?_⟩
        field_simp
        linear_combination -hd'
    -- `x σ(x) = N(x)`
    have hxs : x * star x = ((QuadraticAlgebra.norm x : ℤ) : Zs) := by
      rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star]; rfl
    have hd : (p : Zs) ∣ ((QuadraticAlgebra.norm x : ℤ) : Zs) * y := by
      rw [← hxs, mul_comm x, mul_assoc]; exact dvd_mul_of_dvd_right hxy _
    apply hy
    rw [natCast_dvd_iff] at hd ⊢
    simp only [re_intCast, im_intCast, re_mul, im_mul, zero_mul, add_zero,
      mul_zero] at hd
    exact ⟨(hpZ.dvd_or_dvd hd.1).resolve_left hN, (hpZ.dvd_or_dvd hd.2).resolve_left hN⟩

/-- **Part 1, inert case.** If `2` is not a square mod `p`, then `(p)` is prime with residue
field of `p²` elements, `σ(p) = (p)`, and it is the only prime containing `p`. -/
theorem primeP_inert (hsq : ¬ IsSquare (2 : ZMod p)) :
    (Ideal.span {(p : Zs)}).IsPrime ∧ Nat.card (Zs ⧸ Ideal.span {(p : Zs)}) = p ^ 2 ∧
      (Ideal.span {(p : Zs)}).map (starRingEnd Zs) = Ideal.span {(p : Zs)} ∧
      ∀ P : Ideal Zs, P.IsPrime → (p : Zs) ∈ P → P = Ideal.span {(p : Zs)} := by
  have hprime := prime_natCast_of_not_isSquare hsq
  have hP : (Ideal.span {(p : Zs)}).IsPrime := (Ideal.span_singleton_prime hprime.ne_zero).mpr hprime
  refine ⟨hP, ?_, ?_, ?_⟩
  · rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton]
    have : (p : Zs) = algebraMap ℤ Zs (p : ℤ) := by simp
    rw [this, Algebra.norm_algebraMap, QuadraticAlgebra.finrank_eq_two]
    simp
  · rw [Ideal.map_span, Set.image_singleton, map_natCast]
  · intro P hP' hpP
    have hmax : (Ideal.span {(p : Zs)}).IsMaximal :=
      hP.isMaximal (by simpa using hprime.ne_zero)
    exact (hmax.eq_of_le hP'.ne_top (by rw [Ideal.span_le, Set.singleton_subset_iff]; exact hpP)).symm

/-! ### Unramifiedness -/

theorem norm_dvd_of_dvd {x y : Zs} (h : x ∣ y) : QuadraticAlgebra.norm x ∣ QuadraticAlgebra.norm y :=
  map_dvd QuadraticAlgebra.norm h

theorem norm_natCast_Zs (n : ℕ) : QuadraticAlgebra.norm (n : Zs) = (n : ℤ) ^ 2 := by
  rw [Zs.norm_eq]; simp

variable (p) in
/-- Every rational prime has a prime of `ℤ[s]` above it. -/
theorem exists_prime_dvd_natCast : ∃ π : Zs, Prime π ∧ π ∣ (p : Zs) := by
  have h0 : (p : Zs) ≠ 0 := by
    intro h; have := congrArg QuadraticAlgebra.re h; simp at this; exact hp.out.ne_zero this
  have hu : ¬ IsUnit (p : Zs) := by
    rw [Zs.isUnit_iff_natAbs_norm, norm_natCast_Zs]
    have := hp.out.one_lt
    rw [Int.natAbs_pow, Int.natAbs_natCast]
    intro h1
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) this
    omega
  obtain ⟨i, hi, hdvd⟩ := WfDvdMonoid.exists_irreducible_factor hu h0
  exact ⟨i, irreducible_iff_prime.mp hi, hdvd⟩

/-- A prime above `p` has norm `± p` or `± p²`; if `π² ∣ p` it has norm `± p`. -/
theorem natAbs_norm_eq_of_sq_dvd {π : Zs} (hπ : Prime π) (h : π ^ 2 ∣ (p : Zs)) :
    (QuadraticAlgebra.norm π).natAbs = p := by
  have hd := norm_dvd_of_dvd h
  rw [map_pow, norm_natCast_Zs] at hd
  have hd' : (QuadraticAlgebra.norm π).natAbs ∣ p := by
    have := Int.natAbs_dvd_natAbs.mpr ((Int.pow_dvd_pow_iff two_ne_zero).mp hd)
    simpa using this
  rcases (Nat.dvd_prime hp.out).mp hd' with h1 | h1
  · exact absurd (Zs.isUnit_iff_natAbs_norm.mpr h1) hπ.not_isUnit
  · exact h1

/-- **`p` is unramified**: no prime `π` has `π² ∣ p`, for `p` odd. -/
theorem not_sq_dvd_natCast (hp2 : p ≠ 2) {π : Zs} (hπ : Prime π) : ¬ π ^ 2 ∣ (p : Zs) := by
  intro h
  have hN := natAbs_norm_eq_of_sq_dvd hπ h
  obtain ⟨u, hu⟩ := h
  have hπ0 := hπ.ne_zero
  -- `π ∣ σ π`
  have hstar : π ∣ star π := by
    have hxs : π * star π = ((QuadraticAlgebra.norm π : ℤ) : Zs) := by
      rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star]; rfl
    rcases Int.natAbs_eq (QuadraticAlgebra.norm π) with h1 | h1
    · refine ⟨u, mul_left_cancel₀ hπ0 ?_⟩
      rw [hxs, h1, hN]; simp only [Int.cast_natCast, hu]; ring
    · refine ⟨-u, mul_left_cancel₀ hπ0 ?_⟩
      rw [hxs, h1, hN]; simp only [Int.cast_neg, Int.cast_natCast, hu]; ring
  -- `π ∤ 2` and `π ∤ s`
  have hπ2 : ¬ π ∣ (2 : Zs) := by
    intro h2
    have := norm_dvd_of_dvd h2
    rw [show (2 : Zs) = ((2 : ℕ) : Zs) by norm_num, norm_natCast_Zs] at this
    have := Int.natAbs_dvd_natAbs.mpr this
    rw [hN] at this
    norm_num at this
    have h4 : p ∣ 2 ^ 2 := this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp (hp.out.dvd_of_dvd_pow h4))
  have hπs : ¬ π ∣ sqrt2Z := by
    intro hs
    have := Int.natAbs_dvd_natAbs.mpr (norm_dvd_of_dvd hs)
    rw [hN, norm_sqrt2Z] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp (by simpa using this))
  -- `p ∣ a` and `p ∣ b` for `π = a + b s`
  have hpa : (p : ℤ) ∣ π.re := by
    have h1 : π ∣ (2 : Zs) * (π.re : Zs) := by
      have : (2 : Zs) * (π.re : Zs) = π + star π := by ext <;> simp; ring
      rw [this]; exact dvd_add dvd_rfl hstar
    have h2 := (hπ.dvd_or_dvd h1).resolve_left hπ2
    have := Int.natAbs_dvd_natAbs.mpr (norm_dvd_of_dvd h2)
    rw [hN, Zs.norm_eq] at this
    simp only [re_intCast, im_intCast] at this
    have h3 : (p : ℤ) ∣ π.re ^ 2 := by
      have := Int.natCast_dvd.mpr this; simpa using this
    exact (Nat.prime_iff_prime_int.mp hp.out).dvd_of_dvd_pow h3
  have hpb : (p : ℤ) ∣ π.im := by
    have h1 : π ∣ (2 : Zs) * ((π.im : Zs) * sqrt2Z) := by
      have : (2 : Zs) * ((π.im : Zs) * sqrt2Z) = π - star π := by
        ext <;> simp [sqrt2Z]; ring
      rw [this]; exact dvd_sub dvd_rfl hstar
    have h2 := (hπ.dvd_or_dvd h1).resolve_left hπ2
    have h3 := (hπ.dvd_or_dvd h2).resolve_right hπs
    have := Int.natAbs_dvd_natAbs.mpr (norm_dvd_of_dvd h3)
    rw [hN, Zs.norm_eq] at this
    simp only [re_intCast, im_intCast] at this
    have h4 : (p : ℤ) ∣ π.im ^ 2 := by
      have := Int.natCast_dvd.mpr this; simpa using this
    exact (Nat.prime_iff_prime_int.mp hp.out).dvd_of_dvd_pow h4
  -- then `p² ∣ N(π) = ± p`
  obtain ⟨a, ha⟩ := hpa
  obtain ⟨b, hb⟩ := hpb
  have hNπ : QuadraticAlgebra.norm π = (p : ℤ) ^ 2 * (a ^ 2 - 2 * b ^ 2) := by
    rw [Zs.norm_eq, ha, hb]; ring
  have := congrArg Int.natAbs hNπ
  rw [hN, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] at this
  have hp1 := hp.out.one_lt
  rcases Nat.eq_zero_or_pos (a ^ 2 - 2 * b ^ 2).natAbs with h0 | h0
  · rw [h0] at this; omega
  · nlinarith

/-- `v_π(p) = 1` for a prime `π ∣ p`, `p` odd. -/
theorem vp_natCast_self (hp2 : p ≠ 2) {π : Zs} (hπ : Prime π) (hπp : π ∣ (p : Zs)) :
    vp π (p : K0) = 1 := by
  have hp0 : (p : Zs) ≠ 0 := by
    intro h; have := congrArg QuadraticAlgebra.re h; simp at this; exact hp.out.ne_zero this
  rw [← toK0_natCast]
  exact_mod_cast (vp_eq_iff hπ hp0 1).mpr ⟨by simpa using hπp, not_sq_dvd_natCast hp2 hπ⟩

/-- `v_π(m) = 0` for `π ∣ p` and `p ∤ m`. -/
theorem vp_natCast_of_not_dvd {π : Zs} (hπ : Prime π) (hπp : π ∣ (p : Zs)) {m : ℕ}
    (hm : ¬ p ∣ m) : vp π (m : K0) = 0 := by
  have hm0 : (m : Zs) ≠ 0 := by
    intro h; have := congrArg QuadraticAlgebra.re h; simp at this; subst this; simp at hm
  rw [← toK0_natCast, vp_eq_zero_iff hπ hm0]
  intro hπm
  have hcop : IsCoprime (p : ℤ) (m : ℤ) :=
    (Nat.prime_iff_prime_int.mp hp.out).irreducible.coprime_iff_not_dvd.mpr
      (by exact_mod_cast hm)
  have hcop' : IsCoprime (p : Zs) (m : Zs) := by
    have := hcop.map (Int.castRingHom Zs); simpa using this
  exact hπ.not_isUnit (hcop'.isUnit_of_dvd' hπp hπm)

theorem vp_natCast (hp2 : p ≠ 2) {π : Zs} (hπ : Prime π) (hπp : π ∣ (p : Zs)) {n : ℕ}
    (hn : n ≠ 0) : vp π (n : K0) = padicValNat p n := by
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.out.ne_one
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hpk : (p : K0) ^ k ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  have hmK : (m : K0) ≠ 0 := Nat.cast_ne_zero.mpr hm0
  rw [Nat.cast_mul, Nat.cast_pow, vp_mul hπ hpk hmK, vp_pow hπ, vp_natCast_self hp2 hπ hπp,
    vp_natCast_of_not_dvd hπ hπp hm, padicValNat.mul (pow_ne_zero _ hp.out.ne_zero) hm0,
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hm]
  push_cast; ring

theorem vp_intCast (hp2 : p ≠ 2) {π : Zs} (hπ : Prime π) (hπp : π ∣ (p : Zs)) {n : ℤ}
    (hn : n ≠ 0) : vp π (n : K0) = padicValInt p n := by
  rcases Int.natAbs_eq n with h | h
  · rw [h, Int.cast_natCast, vp_natCast hp2 hπ hπp (Int.natAbs_ne_zero.mpr hn),
      padicValInt.of_nat]
  · rw [h, Int.cast_neg, Int.cast_natCast, vp_neg hπ,
      vp_natCast hp2 hπ hπp (Int.natAbs_ne_zero.mpr hn), padicValInt, Int.natAbs_neg,
      Int.natAbs_natCast]

/-- **Part 2.** `p` is unramified: `v_π(q) = v_p(q)` for every `q ∈ ℚ`, at every prime
`π ∣ p` (both sides are `0` at `q = 0` by convention). -/
theorem vp_ratCast (hp2 : p ≠ 2) {π : Zs} (hπ : Prime π) (hπp : π ∣ (p : Zs)) (q : ℚ) :
    vp π (q : K0) = padicValRat p q := by
  by_cases hq : q = 0
  · subst hq; simp
  have hnum : q.num ≠ 0 := Rat.num_ne_zero.mpr hq
  have hden : q.den ≠ 0 := q.den_nz
  have hq' : (q : K0) = (q.num : K0) / (q.den : K0) := by
    rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
  rw [hq', vp_div hπ (Int.cast_ne_zero.mpr hnum) (Nat.cast_ne_zero.mpr hden),
    vp_intCast hp2 hπ hπp hnum, vp_natCast hp2 hπ hπp hden, padicValRat_def]

/-! ### Conjugate primes -/

theorem star_toK0 (a : Zs) : star (Zs.toK0 a) = Zs.toK0 (star a) := by ext <;> simp

theorem prime_star {π : Zs} (hπ : Prime π) : Prime (star π) := by
  have : star π = (starRingAut : RingAut Zs) π := rfl
  rw [this, MulEquiv.prime_iff]; exact hπ

theorem star_pow_dvd_iff {π a : Zs} (n : ℕ) : star π ^ n ∣ a ↔ π ^ n ∣ star a := by
  constructor
  · rintro ⟨c, rfl⟩; exact ⟨star c, by simp [star_mul, star_pow, mul_comm]⟩
  · rintro ⟨c, hc⟩
    refine ⟨star c, ?_⟩
    have := congrArg star hc
    simpa [star_mul, star_pow, mul_comm] using this

theorem vp_star_toK0 {π : Zs} (hπ : Prime π) (a : Zs) :
    vp (star π) (Zs.toK0 a) = vp π (Zs.toK0 (star a)) := by
  by_cases ha : a = 0
  · subst ha; simp
  have ha' : star a ≠ 0 := by rwa [ne_eq, star_eq_zero]
  have h1 := vp_nonneg (prime_star hπ) a
  have h2 := vp_nonneg hπ (star a)
  have key : ∀ n : ℕ, (n : ℤ) ≤ vp (star π) (Zs.toK0 a) ↔ (n : ℤ) ≤ vp π (Zs.toK0 (star a)) := by
    intro n
    rw [le_vp_iff_pow_dvd (prime_star hπ) ha, le_vp_iff_pow_dvd hπ ha', star_pow_dvd_iff]
  have e1 := (key (vp (star π) (Zs.toK0 a)).toNat).mp (by rw [Int.toNat_of_nonneg h1])
  have e2 := (key (vp π (Zs.toK0 (star a))).toNat).mpr (by rw [Int.toNat_of_nonneg h2])
  rw [Int.toNat_of_nonneg h1] at e1
  rw [Int.toNat_of_nonneg h2] at e2
  omega

/-- **Part 3.** `v_{σπ}(y) = v_π(σ y)`. -/
theorem vp_star {π : Zs} (hπ : Prime π) (y : K0) : vp (star π) y = vp π (star y) := by
  by_cases hy : y = 0
  · subst hy; simp
  obtain ⟨a, b, hb, rfl⟩ := exists_eq_div_Zs y
  have ha : a ≠ 0 := by rintro rfl; simp at hy
  have hbK : Zs.toK0 b ≠ 0 := (map_ne_zero_iff _ Zs.toK0_injective).mpr hb
  have haK : Zs.toK0 a ≠ 0 := (map_ne_zero_iff _ Zs.toK0_injective).mpr ha
  have hstar : star (Zs.toK0 a / Zs.toK0 b) = Zs.toK0 (star a) / Zs.toK0 (star b) := by
    rw [← star_toK0, ← star_toK0]
    exact map_div₀ (starRingEnd K0) _ _
  have hb' : Zs.toK0 (star b) ≠ 0 :=
    (map_ne_zero_iff _ Zs.toK0_injective).mpr (by rwa [ne_eq, star_eq_zero])
  have ha' : Zs.toK0 (star a) ≠ 0 :=
    (map_ne_zero_iff _ Zs.toK0_injective).mpr (by rwa [ne_eq, star_eq_zero])
  rw [hstar, vp_div (prime_star hπ) haK hbK, vp_div hπ ha' hb', vp_star_toK0 hπ,
    vp_star_toK0 hπ]

/-- **Part 4.** If `v_π(y) ≥ m` and `v_{σπ}(y) ≥ m` at a prime `π ∣ p`, then
`v_p(Tr y) ≥ m` (`Tr y = y + σ y ∈ ℚ`; the case `Tr y = 0` is `v_p(Tr y) = ∞`). -/
theorem vp_trace_ge (hp2 : p ≠ 2) {π : Zs} (hπ : Prime π) (hπp : π ∣ (p : Zs)) {y : K0}
    {m : ℤ} (h1 : m ≤ vp π y) (h2 : m ≤ vp (star π) y) :
    QuadraticAlgebra.trace y = 0 ∨ m ≤ padicValRat p (QuadraticAlgebra.trace y) := by
  by_cases ht : QuadraticAlgebra.trace y = 0
  · exact Or.inl ht
  right
  have hy : y ≠ 0 := by rintro rfl; simp at ht
  have hsy : star y ≠ 0 := by rwa [ne_eq, star_eq_zero]
  have htK : ((QuadraticAlgebra.trace y : ℚ) : K0) = y + star y := by
    rw [K0.trace_eq]; ext <;> simp [K0.star_eq']; ring
  have hsum : y + star y ≠ 0 := by
    rw [← htK]; exact_mod_cast ht
  rw [← vp_ratCast hp2 hπ hπp, htK]
  have := min_le_vp_add hπ hy hsy hsum
  rw [← vp_star hπ] at this
  omega

/-! ### Elementary facts shared by the soundness and assembly chapters -/

theorem star_dvd_natCast {π : Zs} {p : ℕ} (h : π ∣ (p : Zs)) : star π ∣ (p : Zs) := by
  obtain ⟨c, hc⟩ := h
  exact ⟨star c, by rw [← star_mul', ← hc]; simp⟩

theorem star_ratCast (r : ℚ) : star (r : K0) = (r : K0) := by
  ext <;> simp

theorem vp_prod {π : Zs} (hπ : Prime π) {ι : Type*} (s : Finset ι) (f : ι → K0)
    (h : ∀ i ∈ s, f i ≠ 0) : vp π (∏ i ∈ s, f i) = ∑ i ∈ s, vp π (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using vp_isUnit hπ isUnit_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      vp_mul hπ (h a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => h i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

omit hp in
/-- A nonzero integer of absolute value less than `p` has `p`-adic valuation zero. -/
theorem padicValRat_intCast_eq_zero {m : ℤ} (hm : m ≠ 0) (hmp : m.natAbs < p) :
    padicValRat p (m : ℚ) = 0 := by
  rw [padicValRat.of_int]
  have : ¬ (p : ℤ) ∣ m := by
    intro hd
    exact hm (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd (by simpa using hmp))
  simp [padicValInt.eq_zero_of_not_dvd this]

end ZInQ.Mult

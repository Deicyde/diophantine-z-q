import ZInQKernel.Contrib.OneProof.RC.Even.EvenPhase

/-!
# Appendix E, Proposition `ex:app-even-phase`: the retained set and the phase `z_D`

The 11/5 manuscript (`diophantine_zq.tex`), Appendix E, tex 7812–7820 (the `S₀` filter),
8114–8138 (the phase). For the fields `retained`, `retained_spec`, `D₀_mem`, `z`, `z_root`,
`z_sq` of lane RC11's structure `EvenPhaseData` (`RC/Even/EvenPhase.lean`).

* `S0Filter S₀ D₀ D` — the retained parameters (tex 7812–7817): `D > 0` squarefree, prime to every
  prime of `S₀`, in the unit squareclass of `D₀` at every prime of `S₀` (`DD₀ ≡ 1 (mod 8)` at `2`,
  `DD₀` a square modulo odd `p`; by Hensel this is `D/D₀ ∈ (ℚ_p^×)²`);
* `S0Filter.spec` — at any level `N` with prime support in `S₀`, a retained `D` is prime to `N`
  and in the unit squareclasses of `D₀` at every prime of `N` (the field `retained_spec`);
  `S0Filter.self` — `D₀` is retained (the field `D₀_mem`);
* `isSquare_zmod_of_local` — Hensel's lemma and the Chinese remainder theorem: a unit that is a
  square modulo every odd prime of `N` and `≡ 1 (mod 8)` (if `2 ∣ N`) is a square in `ZMod N`;
* `sqrtRatio`, `phase` — **the phase** (tex 8116–8121): `z_D = η(w)` for a `w ∈ ZMod N` with
  `w² D₀ = D`. By the Chinese remainder theorem a global `w` is the same as a family of local
  square roots `u_p ∈ ℤ_p^×` of `D/D₀` modulo `p^{v_p(N)}`, and `η(w) = ∏_p η_p(u_p)` with
  `η_p` the prime-power factors of `η`; the factors at `p ∤ cond η` are trivial. So `phase` is the
  manuscript's `z_D = ∏_{p ∣ cond η} η_p(u_p)` for one choice of the local square roots;
  another choice changes `z_D` by a sign (`η(t) = ±1` for `t² = 1`), as the manuscript says
  (tex 8133–8134);
* `phase_sq_eta` — `z_D² = η(D)η(D₀)⁻¹` (tex 8124); `phase_sq` — `z_D² = ψ(D)ψ(D₀)⁻¹`, because
  `ψ/η = χ_{−σ}` is trivial on `D/D₀`: `χ_{−σ}` depends only on the class modulo `4` and
  `D ≡ D₀ (mod 8)` (tex 8136–8138); `phase_root` — `z_D` is a two-power root of unity when `ψ`
  has two-power order (tex 7944, 8123).

Everything here is PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.AppE

open ZInQ.Manuscript ZInQ.Manuscript.RC.PrintsAnalytic

/-! ## The `S₀` filter -/

/-- **The retained parameters** (tex 7812–7817, 7800–7801): `D > 0` squarefree, prime to every
prime of `S₀`, in the unit squareclass of `D₀` at every prime of `S₀`: `DD₀ ≡ 1 (mod 8)` at
`p = 2` and `DD₀` a nonzero square modulo an odd `p ∈ S₀` (by Hensel, `D/D₀ ∈ (ℚ_p^×)²`). -/
def S0Filter (S₀ : Finset ℕ) (D₀ D : ℕ) : Prop :=
  0 < D ∧ Squarefree D ∧ (∀ p ∈ S₀, ¬ p ∣ D) ∧
    ∀ p ∈ S₀, (p = 2 → (D * D₀) % 8 = 1) ∧ (p ≠ 2 → IsSquare ((D * D₀ : ℕ) : ZMod p))

/-- A natural number prime to every prime of a positive `N`'s prime support is prime to `N`. -/
theorem coprime_of_support {S₀ : Finset ℕ} {N D : ℕ}
    (hNS : ∀ p : ℕ, p.Prime → p ∣ N → p ∈ S₀) (hD : ∀ p ∈ S₀, ¬ p ∣ D) : D.Coprime N := by
  refine Nat.coprime_of_dvd fun p hp hpD hpN => hD p (hNS p hp hpN) hpD

/-- **The field `retained_spec`** (PROVED): at a level `N` with prime support in `S₀`, a retained
`D` is positive, squarefree, prime to `N`, and in the unit squareclasses of `D₀` at every prime of
`N`. -/
theorem S0Filter.spec {S₀ : Finset ℕ} {D₀ D N : ℕ} (hNS : ∀ p : ℕ, p.Prime → p ∣ N → p ∈ S₀)
    (h : S0Filter S₀ D₀ D) :
    0 < D ∧ Squarefree D ∧ D.Coprime N ∧ SameUnitClassesAtLevel N D D₀ :=
  ⟨h.1, h.2.1, coprime_of_support hNS h.2.2.1, fun p hp hpN => h.2.2.2 p (hNS p hp hpN)⟩

/-- An odd square is `1` modulo `8` (PROVED). -/
theorem odd_mul_self_mod_eight {D : ℕ} (hD : ¬ 2 ∣ D) : (D * D) % 8 = 1 := by
  have h8 : D % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have hodd : D % 2 = 1 := by omega
  rw [Nat.mul_mod]
  have : D % 8 = 1 ∨ D % 8 = 3 ∨ D % 8 = 5 ∨ D % 8 = 7 := by omega
  rcases this with h | h | h | h <;> rw [h]

/-- **The field `D₀_mem`** (PROVED): the reference `D₀` (positive, squarefree, prime to `S₀ ∋ 2`)
is retained. -/
theorem S0Filter.self {S₀ : Finset ℕ} (h2 : 2 ∈ S₀) {D₀ : ℕ} (hD₀ : 0 < D₀)
    (hsq : Squarefree D₀) (hS : ∀ p ∈ S₀, ¬ p ∣ D₀) : S0Filter S₀ D₀ D₀ := by
  refine ⟨hD₀, hsq, hS, fun p _ => ⟨fun _ => odd_mul_self_mod_eight (hS 2 h2), fun _ => ?_⟩⟩
  exact ⟨(D₀ : ZMod p), by push_cast; ring⟩

/-- The retained parameters at a level `N` are prime to `N` and in the unit classes of `D₀` at
every prime of every level `M` with the same prime support as `N` (PROVED). -/
theorem sameUnitClasses_of_support {N M D D₀ : ℕ}
    (hMN : ∀ p : ℕ, p.Prime → p ∣ M → p ∣ N) (h : SameUnitClassesAtLevel N D D₀) :
    SameUnitClassesAtLevel M D D₀ :=
  fun p hp hpM => h p hp (hMN p hp hpM)

/-! ## Square roots modulo `N` (Hensel and the Chinese remainder theorem) -/

/-- **Hensel at an odd prime** (PROVED): a unit square modulo an odd prime `p` is a square in
`ZMod (p^k)`. -/
theorem isSquare_zmod_prime_pow_odd {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {a : ℕ}
    (hpa : ¬ p ∣ a) (hsq : IsSquare (a : ZMod p)) (k : ℕ) : IsSquare (a : ZMod (p ^ k)) := by
  obtain ⟨c, hc⟩ := hsq
  -- an integer lift `b` of the square root
  set b : ℤ := (c.val : ℤ) with hb
  have hbc : ((b : ℤ) : ZMod p) = c := by simp [hb]
  have hdvd : (p : ℤ) ∣ b ^ 2 - a := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hbc, hc]
    ring
  have hpb : ¬ (p : ℤ) ∣ b := by
    intro h
    apply hpa
    have h1 : (p : ℤ) ∣ b ^ 2 := dvd_pow h two_ne_zero
    have h2 : (p : ℤ) ∣ (a : ℤ) := by
      have := dvd_sub h1 hdvd
      simpa using this
    exact_mod_cast h2
  have hp2' : ¬ (p : ℤ) ∣ 2 * b := by
    intro h
    rcases (Int.Prime.dvd_mul' hp.out h) with h | h
    · have : (p : ℤ) ∣ 2 := h
      have h2 : p ∣ 2 := by exact_mod_cast this
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h2)
    · exact hpb h
  -- Hensel's lemma for `X² − a` at `b`
  let F : Polynomial ℤ := Polynomial.X ^ 2 - Polynomial.C (a : ℤ)
  have hFa : F.aeval (b : ℤ_[p]) = ((b ^ 2 - a : ℤ) : ℤ_[p]) := by
    simp [F]
  have hF'a : F.derivative.aeval (b : ℤ_[p]) = ((2 * b : ℤ) : ℤ_[p]) := by
    simp [F, map_ofNat]
  have hnorm : ‖F.aeval (b : ℤ_[p])‖ < ‖F.derivative.aeval (b : ℤ_[p])‖ ^ 2 := by
    rw [hFa, hF'a]
    have h1 : ‖((b ^ 2 - a : ℤ) : ℤ_[p])‖ < 1 := (PadicInt.norm_int_lt_one_iff_dvd _).mpr hdvd
    have h2 : ‖((2 * b : ℤ) : ℤ_[p])‖ = 1 := by
      have hle : ‖((2 * b : ℤ) : ℤ_[p])‖ ≤ 1 := PadicInt.norm_le_one _
      have hnlt : ¬ ‖((2 * b : ℤ) : ℤ_[p])‖ < 1 := fun h =>
        hp2' ((PadicInt.norm_int_lt_one_iff_dvd _).mp h)
      linarith [not_lt.mp hnlt]
    rw [h2, one_pow]
    exact h1
  obtain ⟨z, hz, -⟩ := hensels_lemma hnorm
  have hz2 : z ^ 2 = (a : ℤ_[p]) := by
    have : F.aeval z = z ^ 2 - (a : ℤ_[p]) := by simp [F]
    rw [this] at hz
    exact sub_eq_zero.mp hz
  refine ⟨PadicInt.toZModPow k z, ?_⟩
  rw [← sq, ← map_pow, hz2, map_natCast]

/-- **Hensel at `2`** (PROVED): `a ≡ 1 (mod 8)` is a square in `ZMod (2^k)`. -/
theorem isSquare_zmod_two_pow {a : ℕ} (ha : a % 8 = 1) (k : ℕ) :
    IsSquare (a : ZMod (2 ^ k)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F : Polynomial ℤ := Polynomial.X ^ 2 - Polynomial.C (a : ℤ)
  have hFa : F.aeval (1 : ℤ_[2]) = ((1 - a : ℤ) : ℤ_[2]) := by
    simp [F]
  have hF'a : F.derivative.aeval (1 : ℤ_[2]) = ((2 : ℤ) : ℤ_[2]) := by
    simp [F, map_ofNat]
  have hnorm : ‖F.aeval (1 : ℤ_[2])‖ < ‖F.derivative.aeval (1 : ℤ_[2])‖ ^ 2 := by
    rw [hFa, hF'a]
    have h8 : ((2 : ℕ) ^ 3 : ℤ) ∣ (1 - a : ℤ) := by
      have : (8 : ℤ) ∣ (1 - a : ℤ) := by omega
      simpa using this
    have h1 : ‖((1 - a : ℤ) : ℤ_[2])‖ ≤ ((2 : ℕ) : ℝ) ^ (-(3 : ℕ) : ℤ) :=
      PadicInt.norm_int_le_pow_iff_dvd.mpr h8
    have h2 : ‖((2 : ℤ) : ℤ_[2])‖ = (2 : ℝ)⁻¹ := by
      have := PadicInt.norm_p (p := 2)
      simpa using this
    rw [h2]
    calc ‖((1 - a : ℤ) : ℤ_[2])‖ ≤ ((2 : ℕ) : ℝ) ^ (-(3 : ℕ) : ℤ) := h1
      _ < (2 : ℝ)⁻¹ ^ 2 := by norm_num
  obtain ⟨z, hz, -⟩ := hensels_lemma hnorm
  have hz2 : z ^ 2 = (a : ℤ_[2]) := by
    have : F.aeval z = z ^ 2 - (a : ℤ_[2]) := by simp [F]
    rw [this] at hz
    exact sub_eq_zero.mp hz
  refine ⟨PadicInt.toZModPow k z, ?_⟩
  rw [← sq, ← map_pow, hz2, map_natCast]

/-- The local conditions of `isSquare_zmod_of_local` at the primes of `N`. -/
def LocalSquare (N a : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ N → (p = 2 → a % 8 = 1) ∧ (p ≠ 2 → IsSquare (a : ZMod p))

/-- **Squares modulo `N`** (PROVED; Hensel at each prime power, then the Chinese remainder
theorem): if `a` is prime to `N ≠ 0`, `≡ 1 (mod 8)` when `2 ∣ N`, and a square modulo every odd
prime of `N`, then `a` is a square in `ZMod N`. -/
theorem isSquare_zmod_of_local (a : ℕ) :
    ∀ N : ℕ, N ≠ 0 → a.Coprime N → LocalSquare N a → IsSquare (a : ZMod N) := by
  intro N
  induction N using Nat.recOnPrimeCoprime with
  | zero => intro h; exact absurd rfl h
  | prime_pow p k hp =>
    intro _ hcop hloc
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have : Subsingleton (ZMod (p ^ 0)) := by
        rw [pow_zero]
        infer_instance
      exact ⟨0, Subsingleton.elim _ _⟩
    · have hpN : p ∣ p ^ k := dvd_pow_self p hk.ne'
      have hpa : ¬ p ∣ a := fun h => by
        have h1 := Nat.dvd_gcd h hpN
        rw [Nat.Coprime.gcd_eq_one hcop] at h1
        exact hp.not_dvd_one h1
      obtain ⟨h2, hodd⟩ := hloc p hp hpN
      by_cases hp2 : p = 2
      · subst hp2
        exact isSquare_zmod_two_pow (h2 rfl) k
      · have : Fact p.Prime := ⟨hp⟩
        exact isSquare_zmod_prime_pow_odd hp2 hpa (hodd hp2) k
  | coprime m n hm hn hmn ihm ihn =>
    intro hN hcop hloc
    have hm0 : m ≠ 0 := by omega
    have hn0 : n ≠ 0 := by omega
    obtain ⟨x, hx⟩ := ihm hm0 (Nat.Coprime.coprime_dvd_right (dvd_mul_right m n) hcop)
      (fun p hp hpm => hloc p hp (dvd_mul_of_dvd_left hpm n))
    obtain ⟨y, hy⟩ := ihn hn0 (Nat.Coprime.coprime_dvd_right (dvd_mul_left n m) hcop)
      (fun p hp hpn => hloc p hp (dvd_mul_of_dvd_right hpn m))
    let e := ZMod.chineseRemainder hmn
    refine ⟨e.symm (x, y), ?_⟩
    apply e.injective
    rw [map_mul, RingEquiv.apply_symm_apply, map_natCast]
    ext
    · simp [hx]
    · simp [hy]

/-! ## The phase `z_D` -/

/-- **A square root of `D/D₀` modulo `N`** (tex 8117–8118): some `w` with `w² D₀ = D` in
`ZMod N` (`1` if there is none; for retained `D` there is one, `exists_sqrtRatio`). -/
def sqrtRatio (N D₀ D : ℕ) : ZMod N :=
  open Classical in
  if h : ∃ w : ZMod N, w ^ 2 * (D₀ : ZMod N) = (D : ZMod N) then h.choose else 1

/-- **The phase `z_D`** (tex 8116–8121): `z_D = η(w)` with `w² = D/D₀` modulo the level; by the
Chinese remainder theorem this is `∏_{p ∣ cond η} η_p(u_p)` with `u_p² = D/D₀` in `ℤ_p^×` (see
the module docstring). -/
def phase (N : ℕ) (η : DirichletCharacter ℂ N) (D₀ D : ℕ) : ℂ := η (sqrtRatio N D₀ D)

/-- For `D, D₀` prime to `N ≠ 0` in the same unit classes at every prime of `N`, a square root
`w` of `D/D₀` exists in `ZMod N` (PROVED, `isSquare_zmod_of_local`). -/
theorem exists_sqrtRatio {N D₀ D : ℕ} (hN : N ≠ 0) (hc₀ : D₀.Coprime N) (hc : D.Coprime N)
    (hcl : SameUnitClassesAtLevel N D D₀) :
    ∃ w : ZMod N, w ^ 2 * (D₀ : ZMod N) = (D : ZMod N) := by
  obtain ⟨s, hs⟩ := isSquare_zmod_of_local (D * D₀) N hN
    (Nat.coprime_mul_iff_left.mpr ⟨hc, hc₀⟩) hcl
  have h1 : (D₀ : ZMod N) * (D₀ : ZMod N)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one D₀ hc₀
  refine ⟨s * (D₀ : ZMod N)⁻¹, ?_⟩
  push_cast at hs
  linear_combination (-((D₀ : ZMod N)⁻¹ ^ 2 * (D₀ : ZMod N))) * hs +
    ((D : ZMod N) * ((D₀ : ZMod N) * (D₀ : ZMod N)⁻¹ + 1)) * h1

/-- The chosen square root satisfies `w² D₀ = D` (PROVED). -/
theorem sqrtRatio_spec {N D₀ D : ℕ} (hN : N ≠ 0) (hc₀ : D₀.Coprime N) (hc : D.Coprime N)
    (hcl : SameUnitClassesAtLevel N D D₀) :
    sqrtRatio N D₀ D ^ 2 * (D₀ : ZMod N) = (D : ZMod N) := by
  have h := exists_sqrtRatio hN hc₀ hc hcl
  unfold sqrtRatio
  split_ifs with h'
  · exact h'.choose_spec
  · exact absurd h h'

/-- The chosen square root is a unit (PROVED). -/
theorem sqrtRatio_isUnit {N D₀ D : ℕ} (hN : N ≠ 0) (hc₀ : D₀.Coprime N) (hc : D.Coprime N)
    (hcl : SameUnitClassesAtLevel N D D₀) : IsUnit (sqrtRatio N D₀ D) := by
  have hD : IsUnit (D : ZMod N) := (ZMod.isUnit_iff_coprime D N).mpr hc
  rw [← sqrtRatio_spec hN hc₀ hc hcl] at hD
  exact (isUnit_pow_iff two_ne_zero).mp (isUnit_of_mul_isUnit_left hD)

/-- A multiplicative character takes nonzero values at units (PROVED). -/
theorem mulChar_ne_zero_of_isUnit {N : ℕ} (χ : DirichletCharacter ℂ N) {u : ZMod N}
    (hu : IsUnit u) : χ u ≠ 0 := by
  obtain ⟨v, rfl⟩ := hu
  have h : χ (v : ZMod N) * χ ((v⁻¹ : (ZMod N)ˣ) : ZMod N) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  exact left_ne_zero_of_mul_eq_one h

/-- **`z_D² = η(D) η(D₀)⁻¹`** (tex 8124; PROVED): `η(w)² η(D₀) = η(w² D₀) = η(D)`. -/
theorem phase_sq_eta {N D₀ D : ℕ} (hN : N ≠ 0) (η : DirichletCharacter ℂ N) (hc₀ : D₀.Coprime N)
    (hc : D.Coprime N) (hcl : SameUnitClassesAtLevel N D D₀) :
    phase N η D₀ D ^ 2 = η D * (η D₀)⁻¹ := by
  have hu₀ : IsUnit (D₀ : ZMod N) := (ZMod.isUnit_iff_coprime D₀ N).mpr hc₀
  have h0 := mulChar_ne_zero_of_isUnit η hu₀
  have hmul : η (sqrtRatio N D₀ D) ^ 2 * η D₀ = η D := by
    rw [← map_pow, ← map_mul, sqrtRatio_spec hN hc₀ hc hcl]
  unfold phase
  rw [← hmul]
  field_simp

/-- Odd `D, D₀` with `DD₀ ≡ 1 (mod 8)` are congruent modulo `8` (PROVED). -/
theorem mod_eight_eq_of_mul {D D₀ : ℕ} (h : (D * D₀) % 8 = 1) : D % 8 = D₀ % 8 := by
  have h1 : (D % 8) * (D₀ % 8) % 8 = 1 := by rw [← Nat.mul_mod]; exact h
  have hD : D % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have hD₀ : D₀ % 8 < 8 := Nat.mod_lt _ (by norm_num)
  interval_cases hx : D % 8 <;> interval_cases hy : D₀ % 8 <;> simp_all

/-- **`χ_{−σ}(D) = χ_{−σ}(D₀)`** (tex 8136–8137; PROVED): for odd `n`, `χ_{−σ}(n)` is the Jacobi
symbol `(−σ/n)`, which is `χ₄(n)` for `σ = 1` and `1` for `σ = −1`; `χ₄` depends only on `n mod 4`,
and `D ≡ D₀ (mod 8)`. -/
theorem kronecker_eq_of_mul_mod_eight {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) {D D₀ : ℕ}
    (h : (D * D₀) % 8 = 1) : kronecker (-σ) D = kronecker (-σ) D₀ := by
  have h8 := mod_eight_eq_of_mul h
  have hDo : Odd D := by
    rw [Nat.odd_iff]
    by_contra hne
    have h2 : 2 ∣ D * D₀ := Dvd.dvd.mul_right (by omega) D₀
    omega
  have hD₀o : Odd D₀ := by
    rw [Nat.odd_iff]
    by_contra hne
    have h2 : 2 ∣ D * D₀ := Dvd.dvd.mul_left (by omega) D
    omega
  have hf : ∀ n : ℕ, Odd n → kronecker (-σ) n = jacobiSym (-σ) n := by
    intro n hn
    have hfac : n.factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (fun h2 => by
        rcases hn with ⟨k, hk⟩; omega)
    unfold kronecker
    rw [hfac, pow_zero, pow_zero, one_mul, Nat.div_one]
  rw [hf D hDo, hf D₀ hD₀o]
  rcases hσ with rfl | rfl
  · rw [jacobiSym.at_neg_one hDo, jacobiSym.at_neg_one hD₀o, ZMod.χ₄_nat_mod_four D,
      ZMod.χ₄_nat_mod_four D₀]
    have : D % 4 = D₀ % 4 := by omega
    rw [this]
  · simp [jacobiSym.one_left]

/-- **`z_D² = ψ(D) ψ(D₀)⁻¹`** (tex 8136–8138; PROVED; the field `z_sq`): `ψ/η = χ_{−σ}` is
trivial on `D/D₀`, since its conductor is supported at `2` and `D/D₀` is a square there. -/
theorem phase_sq {N D₀ D : ℕ} (hN : N ≠ 0) (h4 : 4 ∣ N) (ψ η : DirichletCharacter ℂ N) {σ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) (hψη : ∀ n : ℕ, n.Coprime N → η n = ψ n * (kronecker (-σ) n : ℂ))
    (hc₀ : D₀.Coprime N) (hc : D.Coprime N) (hcl : SameUnitClassesAtLevel N D D₀) :
    phase N η D₀ D ^ 2 = ψ D * (ψ D₀)⁻¹ := by
  have h2N : 2 ∣ N := dvd_trans (by norm_num) h4
  have h8 : (D * D₀) % 8 = 1 := (hcl 2 Nat.prime_two h2N).1 rfl
  have hk := kronecker_eq_of_mul_mod_eight hσ h8
  have hk0 : (kronecker (-σ) D₀ : ℂ) ≠ 0 := by
    have hsq : kronecker (-σ) D₀ ^ 2 = 1 := by
      have hD₀o : ¬ 2 ∣ D₀ := fun h => by
        have := Nat.Coprime.coprime_dvd_left h hc₀
        have h22 : Nat.gcd 2 N = 2 := Nat.gcd_eq_left h2N
        rw [Nat.Coprime, h22] at this; omega
      have hfac : D₀.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd hD₀o
      unfold kronecker
      rw [hfac, pow_zero, pow_zero, one_mul, Nat.div_one]
      apply jacobiSym.sq_one
      rcases hσ with rfl | rfl <;> simp
    intro h0
    have : ((kronecker (-σ) D₀ : ℤ) : ℂ) ^ 2 = 1 := by exact_mod_cast hsq
    rw [h0] at this; simp at this
  rw [phase_sq_eta hN η hc₀ hc hcl, hψη D hc, hψη D₀ hc₀, hk, mul_inv]
  field_simp

/-- **`z_D` is a two-power root of unity** (tex 8123; PROVED; the field `z_root`) when `ψ` has
two-power order (tex 7944): `z_D^{2^{k+1}} = (ψ(D)ψ(D₀)⁻¹)^{2^k} = 1`. -/
theorem phase_root {N D₀ D : ℕ} (hN : N ≠ 0) (h4 : 4 ∣ N) (ψ η : DirichletCharacter ℂ N) {σ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) (hψη : ∀ n : ℕ, n.Coprime N → η n = ψ n * (kronecker (-σ) n : ℂ))
    {k : ℕ} (hψk : ψ ^ (2 ^ k) = 1)
    (hc₀ : D₀.Coprime N) (hc : D.Coprime N) (hcl : SameUnitClassesAtLevel N D D₀) :
    ∃ j : ℕ, phase N η D₀ D ^ (2 ^ j) = 1 := by
  refine ⟨k + 1, ?_⟩
  have hu₀ : IsUnit (D₀ : ZMod N) := (ZMod.isUnit_iff_coprime D₀ N).mpr hc₀
  have hu : IsUnit (D : ZMod N) := (ZMod.isUnit_iff_coprime D N).mpr hc
  have hpow : ∀ {u : ZMod N}, IsUnit u → ψ u ^ (2 ^ k) = 1 := by
    intro u hu'
    rw [← MulChar.pow_apply' ψ (pow_ne_zero k two_ne_zero), hψk, MulChar.one_apply hu']
  rw [pow_succ', pow_mul, phase_sq hN h4 ψ η hσ hψη hc₀ hc hcl, mul_pow, inv_pow, hpow hu,
    hpow hu₀, inv_one, mul_one]

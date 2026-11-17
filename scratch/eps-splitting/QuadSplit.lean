import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
import Mathlib.NumberTheory.FundamentalDiscriminant
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Tactic.ComputeDegree
import ZInQKernel.Contrib.OneProof.GrossZagierScheme.EpsD

/-!
# eps-splitting: `ε_D(p)` is the splitting character of `ℚ(√D)`

Task eps-splitting (2026-11-17). Report: `docs/research/eps-splitting.md`; scratch and log:
`scratch/eps-splitting/`.

Let `D < 0` be a fundamental discriminant (Mathlib's `Int.IsFundamentalDiscr`), `K` a number field
with `[K : ℚ] = 2` and `δ ∈ K` with `δ² = D`, so `K = ℚ(√D)`. Then:

* `exists_int_repr`, `adjoin_thetaO_eq_top`: `𝓞_K = ℤ[θ]`, `θ = (D + √D)/2`;
* `minpoly_thetaO`: `minpoly ℤ θ = X² − D X + (D² − D)/4`;
* `splitType_epsD` (via Mathlib's Kummer–Dedekind theorem
  `NumberField.Ideal.primesOverSpanEquivMonicFactorsMod`): for every prime `p`, the Kronecker symbol
  `ε_D(p) = (D/p)` (`ZInQ.HGZSteps.epsD`) is `1`, `−1` or `0` according as `p` splits, is inert or
  ramifies in `K` (`IsSplitIn`, `IsInertIn`, `IsRamifiedIn`, defined through prime ideals of `𝓞 K`);
* `quadChar_eq_epsD`: the quadratic character of `K` (`quadChar K`, completely multiplicative with
  the splitting values at primes) is `ε_D`.

No `sorry`, no `axiom`.
-/

open Polynomial NumberField

namespace ZInQ.EpsSplit


/-- `(D² − D)/4`, the constant term of the minimal polynomial of `(D + √D)/2`. -/
def cD (D : ℤ) : ℤ := (D ^ 2 - D) / 4

theorem four_mul_cD {D : ℤ} (h : D % 4 = 0 ∨ D % 4 = 1) : 4 * cD D = D ^ 2 - D := by
  unfold cD
  apply Int.mul_ediv_cancel'
  obtain ⟨k, hk⟩ : ∃ k, D = 4 * k + D % 4 := ⟨D / 4, by omega⟩
  rcases h with h | h <;> rw [h] at hk <;> subst hk
  · exact ⟨4 * k ^ 2 - k, by ring⟩
  · exact ⟨4 * k ^ 2 + k, by ring⟩

/-- The minimal polynomial `X² − D X + (D² − D)/4` of `(D + √D)/2`. -/
noncomputable def gD (D : ℤ) : ℤ[X] := X ^ 2 - C D * X + C (cD D)

theorem gD_monic (D : ℤ) : (gD D).Monic := by unfold gD; monicity!

theorem gD_natDegree (D : ℤ) : (gD D).natDegree = 2 := by unfold gD; compute_degree!

variable {K : Type*} [Field K]

/-- `θ = (D + δ)/2`. -/
noncomputable def thetaK (D : ℤ) (δ : K) : K := ((D : K) + δ) / 2

/-! ## Splitting of primes in a quadratic field -/

variable (K) in
/-- **`p` splits in `K`**: two distinct prime ideals of `𝓞 K` lie over `p` (for a quadratic field,
`p 𝓞_K = 𝔭 𝔭'` with `𝔭 ≠ 𝔭'`). -/
def IsSplitIn (p : ℕ) : Prop :=
  ∃ P ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K), ∃ Q ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K),
    P ≠ Q

variable (K) in
/-- **`p` is inert in `K`**: `p 𝓞_K` is a prime ideal. -/
def IsInertIn (p : ℕ) : Prop := (Ideal.span {(p : 𝓞 K)}).IsPrime

variable (K) in
/-- **`p` ramifies in `K`**: some prime of `𝓞 K` over `p` has ramification index `> 1`. -/
def IsRamifiedIn (p : ℕ) : Prop :=
  ∃ P ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K), 1 < Ideal.ramificationIdx P ℤ

variable (K) in
/-- `v ∈ {1, -1, 0}` records whether `p` splits, is inert or ramifies in `K`. -/
def SplitType (p : ℕ) (v : ℤ) : Prop :=
  (IsSplitIn K p ↔ v = 1) ∧ (IsInertIn K p ↔ v = -1) ∧ (IsRamifiedIn K p ↔ v = 0)

variable (K) in
open Classical in
/-- **The quadratic character of `K` at a prime `p`**: `1` if `p` splits in `K`, `−1` if `p` is
inert, `0` otherwise (`p` ramifies). -/
noncomputable def quadCharPrime (p : ℕ) : ℤ :=
  if IsSplitIn K p then 1 else if IsInertIn K p then -1 else 0

variable (K) in
/-- **The quadratic character `ε_K` of a quadratic field `K`** as a function on `ℕ`: completely
multiplicative, `quadCharPrime K p` at a prime `p`, and `0` at `0` (the Dirichlet character of
`K/ℚ`). -/
noncomputable def quadChar (n : ℕ) : ℤ :=
  if n = 0 then 0 else n.factorization.prod fun p e => quadCharPrime K p ^ e

section RingOfIntegers

variable [CharZero K] {D : ℤ} {δ : K}

theorem aeval_thetaK (h4 : D % 4 = 0 ∨ D % 4 = 1) (hδ : δ ^ 2 = (D : K)) :
    aeval (thetaK D δ) (gD D) = 0 := by
  have h' := congrArg (Int.cast : ℤ → K) (four_mul_cD h4)
  push_cast at h'
  simp only [gD, thetaK, map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C,
    algebraMap_int_eq, Int.coe_castRingHom]
  linear_combination (1 / 4 : K) * hδ + (1 / 4 : K) * h'

theorem isIntegral_thetaK (h4 : D % 4 = 0 ∨ D % 4 = 1) (hδ : δ ^ 2 = (D : K)) :
    IsIntegral ℤ (thetaK D δ) :=
  ⟨gD D, gD_monic D, by rw [← aeval_def]; exact aeval_thetaK h4 hδ⟩

theorem thetaK_ne (hneg : D < 0) (hδ : δ ^ 2 = (D : K)) (q : ℚ) : thetaK D δ ≠ (q : K) := by
  intro h
  have h1 : δ = ((2 * q - D : ℚ) : K) := by
    simp only [thetaK] at h
    push_cast
    linear_combination 2 * h
  have h2 : (((2 * q - D) ^ 2 : ℚ) : K) = ((D : ℚ) : K) := by
    push_cast at h1 ⊢; rw [← h1, hδ]
  have h3 : ((2 * q - D) ^ 2 : ℚ) = D := Rat.cast_injective h2
  have : (0 : ℚ) ≤ (2 * q - D) ^ 2 := sq_nonneg _
  have : (D : ℚ) < 0 := by exact_mod_cast hneg
  linarith

/-- Every element of `K` is `s + t θ` with `s, t ∈ ℚ`. -/
theorem exists_repr (hK : Module.finrank ℚ K = 2) (hneg : D < 0)
    (hδ : δ ^ 2 = (D : K)) (x : K) : ∃ s t : ℚ, x = (s : K) + (t : K) * thetaK D δ := by
  have hli : LinearIndependent ℚ ![(1 : K), thetaK D δ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rw [Rat.smul_def, Rat.smul_def, mul_one] at hst
    by_cases ht : t = 0
    · subst ht
      simp only [Rat.cast_zero, zero_mul, add_zero, Rat.cast_eq_zero] at hst
      exact ⟨hst, rfl⟩
    · exfalso
      apply thetaK_ne hneg hδ (-s / t)
      have ht' : (t : K) ≠ 0 := by exact_mod_cast ht
      push_cast
      field_simp
      linear_combination hst
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hK])
  refine ⟨b.repr x 0, b.repr x 1, ?_⟩
  have := b.sum_repr x
  rw [Fin.sum_univ_two] at this
  simp only [b, coe_basisOfLinearIndependentOfCardEqFinrank, Matrix.cons_val_zero,
    Matrix.cons_val_one, Rat.smul_def, mul_one] at this
  exact this.symm


/-! ## The ring of integers is `ℤ[θ]` -/

theorem coeff_minpoly_int {x : K} (hx : IsIntegral ℤ x) (i : ℕ) :
    ∃ n : ℤ, (minpoly ℚ x).coeff i = n := by
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hx, coeff_map]
  exact ⟨(minpoly ℤ x).coeff i, by simp⟩

theorem rat_int_of_sq_mul {q : ℚ} {m k : ℤ} (hm : Squarefree m) (h : q ^ 2 * m = k) :
    ∃ n : ℤ, q = n := by
  refine ⟨q.num, ?_⟩
  have hden : q.den = 1 := by
    have h1 : (q.num : ℚ) ^ 2 * m = k * (q.den : ℚ) ^ 2 := by
      rw [← h]; nth_rw 2 [← Rat.num_div_den q]; field_simp
    have h2 : q.num ^ 2 * m = k * (q.den : ℤ) ^ 2 := by exact_mod_cast h1
    have hcop : IsCoprime ((q.den : ℤ) ^ 2) (q.num ^ 2) := by
      apply IsCoprime.pow
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
      exact q.reduced
    have h3 : (q.den : ℤ) ^ 2 ∣ m := hcop.dvd_of_dvd_mul_left ⟨k, by rw [h2]; ring⟩
    have h4 : IsUnit (q.den : ℤ) := hm _ (by rw [← sq]; exact h3)
    have := Int.isUnit_iff.mp h4
    omega
  exact (Rat.coe_int_num_of_den_eq_one hden).symm

theorem int_of_coeffs (hD : Int.IsFundamentalDiscr D) {s t : ℚ} {A B : ℤ}
    (hA : 2 * s + t * D = A) (hB : s ^ 2 + s * D * t + t ^ 2 * cD D = B) :
    ∃ a b : ℤ, s = a ∧ t = b := by
  have h4 := four_mul_cD hD.1
  have hc : (4 : ℚ) * (cD D : ℚ) = (D : ℚ) ^ 2 - D := by exact_mod_cast h4
  have hk : t ^ 2 * D = ((A ^ 2 - 4 * B : ℤ) : ℚ) := by
    push_cast; rw [← hA, ← hB]; linear_combination t ^ 2 * hc
  obtain ⟨n, hn⟩ : ∃ n : ℤ, t = n := by
    rcases Int.isFundamentalDiscr_iff_squarefree.mp hD with ⟨_, hsq⟩ | ⟨h0, hsq, hm⟩
    · exact rat_int_of_sq_mul hsq hk
    · obtain ⟨m, rfl⟩ : 4 ∣ D := Int.dvd_of_emod_eq_zero h0
      rw [Int.mul_ediv_cancel_left m four_ne_zero] at hsq hm
      obtain ⟨T, hT⟩ := rat_int_of_sq_mul (q := 2 * t) (k := A ^ 2 - 4 * B) hsq
        (by push_cast at hk ⊢; linear_combination hk)
      have h5 : A ^ 2 - T ^ 2 * m = 4 * B := by
        have : ((A ^ 2 - T ^ 2 * m : ℤ) : ℚ) = ((4 * B : ℤ) : ℚ) := by
          push_cast at hk ⊢; rw [← hT]; linear_combination -hk
        exact_mod_cast this
      have hTe : Even T := by
        by_contra hodd
        rw [Int.not_even_iff_odd] at hodd
        obtain ⟨u, rfl⟩ := hodd
        rcases Int.even_or_odd A with ⟨v, rfl⟩ | ⟨v, rfl⟩ <;> ring_nf at h5 <;> omega
      obtain ⟨u, rfl⟩ := hTe
      exact ⟨u, by push_cast at hT; linarith⟩
  subst hn
  have h6 : 4 * B = (A - n * D) ^ 2 + 2 * (A - n * D) * n * D + n ^ 2 * (D ^ 2 - D) := by
    have : ((4 * B : ℤ) : ℚ) = (((A - n * D) ^ 2 + 2 * (A - n * D) * n * D +
        n ^ 2 * (D ^ 2 - D) : ℤ) : ℚ) := by
      push_cast; rw [← hA, ← hB]; linear_combination (n : ℚ) ^ 2 * hc
    exact_mod_cast this
  have hSe : Even (A - n * D) := by
    by_contra hodd
    rw [Int.not_even_iff_odd] at hodd
    obtain ⟨u, hu⟩ := hodd
    obtain ⟨w, hw⟩ : Even (D ^ 2 - D) := by
      have : D ^ 2 - D = D * (D - 1) := by ring
      rw [this]; exact Int.even_mul_pred_self D
    rw [hu, hw] at h6
    ring_nf at h6
    omega
  obtain ⟨a, ha⟩ := hSe
  refine ⟨a, n, ?_, rfl⟩
  have : ((A - n * D : ℤ) : ℚ) = ((a + a : ℤ) : ℚ) := by rw [ha]
  push_cast at this
  linarith

/-- **Every algebraic integer of `K = ℚ(√D)` is `a + b θ`, `θ = (D + √D)/2`**, for a negative
fundamental discriminant `D`. -/
theorem exists_int_repr (hD : Int.IsFundamentalDiscr D) (hneg : D < 0)
    (hK : Module.finrank ℚ K = 2) (hδ : δ ^ 2 = (D : K)) {x : K} (hx : IsIntegral ℤ x) :
    ∃ a b : ℤ, x = (a : K) + (b : K) * thetaK D δ := by
  have : FiniteDimensional ℚ K := Module.finite_of_finrank_pos (by rw [hK]; norm_num)
  obtain ⟨s, t, rfl⟩ := exists_repr hK hneg hδ x
  have hxQ : IsIntegral ℚ ((s : K) + t * thetaK D δ) := Algebra.IsIntegral.isIntegral _
  by_cases ht : t = 0
  · subst ht
    simp only [Rat.cast_zero, zero_mul, add_zero] at hx ⊢
    obtain ⟨n, hn⟩ := coeff_minpoly_int hx 0
    rw [← eq_ratCast (algebraMap ℚ K), minpoly.eq_X_sub_C] at hn
    simp only [coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub] at hn
    refine ⟨-n, 0, ?_⟩
    have hs : s = ((-n : ℤ) : ℚ) := by push_cast; linarith
    rw [hs]; push_cast; ring
  · have hθ : thetaK D δ ^ 2 - (D : K) * thetaK D δ + (cD D : K) = 0 := by
      have := aeval_thetaK hD.1 hδ
      simpa [gD] using this
    set x := (s : K) + t * thetaK D δ with hxdef
    set P : ℚ[X] := X ^ 2 - C (2 * s + t * D) * X + C (s ^ 2 + s * D * t + t ^ 2 * cD D)
      with hPdef
    have hP : aeval x P = 0 := by
      simp only [hPdef, map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, eq_ratCast]
      push_cast
      linear_combination (t : K) ^ 2 * hθ
    have hPm : P.Monic := by rw [hPdef]; monicity!
    have hPd : P.natDegree = 2 := by rw [hPdef]; compute_degree!
    have hnr : x ∉ (algebraMap ℚ K).range := by
      rintro ⟨q, hq⟩
      apply thetaK_ne hneg hδ ((q - s) / t)
      rw [eq_ratCast] at hq
      have ht' : (t : K) ≠ 0 := by exact_mod_cast ht
      push_cast
      field_simp
      linear_combination -hq
    have heq : P = minpoly ℚ x := eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hxQ) hPm
      (minpoly.dvd ℚ x hP) (by rw [hPd]; exact (minpoly.two_le_natDegree_iff hxQ).mpr hnr)
    obtain ⟨A, hA⟩ := coeff_minpoly_int hx 1
    obtain ⟨B, hB⟩ := coeff_minpoly_int hx 0
    rw [← heq, hPdef] at hA hB
    simp only [coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C] at hA hB
    norm_num at hA hB
    obtain ⟨a, b, rfl, rfl⟩ := int_of_coeffs hD (A := -A) (B := B) (by push_cast; linarith) hB
    exact ⟨a, b, by rw [hxdef]; push_cast; ring⟩

/-- `θ` as an element of `𝓞 K`. -/
noncomputable def thetaO (hD : Int.IsFundamentalDiscr D) (hδ : δ ^ 2 = (D : K)) : 𝓞 K :=
  ⟨thetaK D δ, isIntegral_thetaK hD.1 hδ⟩

theorem coe_thetaO (hD : Int.IsFundamentalDiscr D) (hδ : δ ^ 2 = (D : K)) :
    ((thetaO hD hδ : 𝓞 K) : K) = thetaK D δ := rfl

/-- **`𝓞_K = ℤ[θ]`.** -/
theorem adjoin_thetaO_eq_top (hD : Int.IsFundamentalDiscr D) (hneg : D < 0)
    (hK : Module.finrank ℚ K = 2) (hδ : δ ^ 2 = (D : K)) :
    Algebra.adjoin ℤ {thetaO hD hδ} = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨a, b, hab⟩ := exists_int_repr hD hneg hK hδ (RingOfIntegers.isIntegral_coe x)
  have : x = (a : 𝓞 K) + (b : 𝓞 K) * thetaO hD hδ := by
    ext; push_cast; exact hab
  rw [this]
  exact add_mem (Subalgebra.intCast_mem _ _)
    (mul_mem (Subalgebra.intCast_mem _ _) (Algebra.self_mem_adjoin_singleton ℤ _))

theorem minpoly_thetaO (hD : Int.IsFundamentalDiscr D) (hneg : D < 0) (hδ : δ ^ 2 = (D : K)) :
    minpoly ℤ (thetaO hD hδ) = gD D := by
  have hint := RingOfIntegers.isIntegral (thetaO hD hδ)
  refine (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (gD_monic D)
    (minpoly.isIntegrallyClosed_dvd hint ?_) ?_).symm
  · apply RingOfIntegers.ext
    show (algebraMap (𝓞 K) K) (aeval (thetaO hD hδ) (gD D)) = algebraMap (𝓞 K) K 0
    rw [← Polynomial.aeval_algebraMap_apply, map_zero]
    exact aeval_thetaK hD.1 hδ
  · rw [gD_natDegree]
    refine (minpoly.two_le_natDegree_iff hint).mpr ?_
    rintro ⟨n, hn⟩
    apply thetaK_ne hneg hδ n
    have := congrArg (fun y : 𝓞 K => (y : K)) hn
    simp only [algebraMap_int_eq, eq_intCast] at this
    rw [← coe_thetaO hD hδ, ← this]
    push_cast; rfl


end RingOfIntegers

section KD

open RingOfIntegers NumberField.Ideal UniqueFactorizationMonoid

variable [NumberField K] {θ : 𝓞 K} {p : ℕ} [Fact p.Prime]

theorem isInertIn_iff (hp : ¬ p ∣ exponent θ) :
    IsInertIn K p ↔ Irreducible ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))) := by
  have hg0 : (minpoly ℤ θ).map (Int.castRingHom (ZMod p)) ≠ 0 :=
    map_monic_ne_zero (minpoly.monic θ.isIntegral)
  let e := ZModXQuotSpanEquivQuotSpan hp
  unfold IsInertIn
  rw [← Ideal.Quotient.isDomain_iff_prime]
  constructor
  · intro h
    have : IsDomain ((ZMod p)[X] ⧸ Ideal.span {(minpoly ℤ θ).map (Int.castRingHom (ZMod p))}) :=
      MulEquiv.isDomain _ e.toMulEquiv
    rw [Ideal.Quotient.isDomain_iff_prime, Ideal.span_singleton_prime hg0] at this
    exact this.irreducible
  · intro h
    have : IsDomain ((ZMod p)[X] ⧸ Ideal.span {(minpoly ℤ θ).map (Int.castRingHom (ZMod p))}) := by
      rw [Ideal.Quotient.isDomain_iff_prime, Ideal.span_singleton_prime hg0]; exact h.prime
    exact MulEquiv.isDomain _ e.symm.toMulEquiv

theorem isSplitIn_iff (hp : ¬ p ∣ exponent θ) :
    IsSplitIn K p ↔ ∃ Q₁ ∈ monicFactorsMod θ p, ∃ Q₂ ∈ monicFactorsMod θ p, Q₁ ≠ Q₂ := by
  let e := primesOverSpanEquivMonicFactorsMod (θ := θ) hp
  constructor
  · rintro ⟨P, hP, Q, hQ, hne⟩
    refine ⟨e ⟨P, hP⟩, (e ⟨P, hP⟩).2, e ⟨Q, hQ⟩, (e ⟨Q, hQ⟩).2, fun h => hne ?_⟩
    exact congrArg Subtype.val (e.injective (Subtype.ext h))
  · rintro ⟨Q₁, h₁, Q₂, h₂, hne⟩
    refine ⟨e.symm ⟨Q₁, h₁⟩, (e.symm ⟨Q₁, h₁⟩).2, e.symm ⟨Q₂, h₂⟩, (e.symm ⟨Q₂, h₂⟩).2,
      fun h => hne ?_⟩
    exact congrArg Subtype.val (e.symm.injective (Subtype.ext h))

theorem isRamifiedIn_iff (hp : ¬ p ∣ exponent θ) :
    IsRamifiedIn K p ↔ ∃ Q ∈ monicFactorsMod θ p,
      1 < multiplicity Q ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))) := by
  let e := primesOverSpanEquivMonicFactorsMod (θ := θ) hp
  constructor
  · rintro ⟨P, hP, h⟩
    refine ⟨e ⟨P, hP⟩, (e ⟨P, hP⟩).2, ?_⟩
    have := ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply' hp (e ⟨P, hP⟩).2
    rw [Subtype.coe_eta, Equiv.symm_apply_apply] at this
    rw [← this]; exact h
  · rintro ⟨Q, hQ, h⟩
    exact ⟨_, (e.symm ⟨Q, hQ⟩).2,
      by rwa [ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply' hp]⟩

end KD

/-! ## Factorization types of a monic quadratic -/

section Poly

open UniqueFactorizationMonoid

variable {F : Type*} [Field F] [DecidableEq F]

theorem multiplicity_eq_count {Q g : F[X]} (hQ : Q ∈ normalizedFactors g) (hg : g ≠ 0) :
    multiplicity Q g = (normalizedFactors g).count Q :=
  multiplicity_eq_of_emultiplicity_eq_some (by
    rw [emultiplicity_eq_count_normalizedFactors (irreducible_of_normalized_factor Q hQ) hg,
      normalize_normalized_factor Q hQ])

theorem normalizedFactors_of_irreducible {g : F[X]} (hg : Irreducible g) (hm : g.Monic) :
    normalizedFactors g = {g} := by
  rw [normalizedFactors_irreducible hg, hm.normalize_eq_self]

theorem normalizedFactors_X_sub_C_mul (a b : F) :
    normalizedFactors ((X - C a) * (X - C b)) = {X - C a, X - C b} := by
  rw [normalizedFactors_mul (X_sub_C_ne_zero a) (X_sub_C_ne_zero b),
    normalizedFactors_irreducible (irreducible_X_sub_C a),
    normalizedFactors_irreducible (irreducible_X_sub_C b),
    (monic_X_sub_C a).normalize_eq_self, (monic_X_sub_C b).normalize_eq_self]
  rfl

omit [DecidableEq F] in
theorem not_irreducible_X_sub_C_mul (a b : F) : ¬ Irreducible ((X - C a) * (X - C b)) := by
  intro h
  rcases h.isUnit_or_isUnit rfl with h | h <;> exact not_isUnit_X_sub_C _ h

omit [DecidableEq F] in
theorem quadratic_eq_mul {A c r₁ r₂ : F} (h1 : r₁ + r₂ = A) (h2 : r₁ * r₂ = c) :
    X ^ 2 - C A * X + C c = (X - C r₁) * (X - C r₂) := by
  rw [← h1, ← h2, C_add, C_mul]; ring

omit [DecidableEq F] in
theorem natDegree_quad (A c : F) : (X ^ 2 - C A * X + C c).natDegree = 2 := by compute_degree!

end Poly

/-! ## The three splitting types -/

section Types

open RingOfIntegers NumberField.Ideal UniqueFactorizationMonoid
variable [NumberField K] {θ : 𝓞 K} {p : ℕ} [Fact p.Prime]

theorem splitType_of_irreducible (hp : ¬ p ∣ exponent θ)
    (h : Irreducible ((minpoly ℤ θ).map (Int.castRingHom (ZMod p)))) : SplitType K p (-1) := by
  have hm : ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))).Monic :=
    (minpoly.monic θ.isIntegral).map _
  have hg0 : (minpoly ℤ θ).map (Int.castRingHom (ZMod p)) ≠ 0 := hm.ne_zero
  have hnf := normalizedFactors_of_irreducible h hm
  refine ⟨?_, ?_, ?_⟩
  · rw [isSplitIn_iff hp]
    simp only [monicFactorsMod, hnf, Multiset.toFinset_singleton, Finset.mem_singleton]
    simp
  · rw [isInertIn_iff hp]; simp [h]
  · rw [isRamifiedIn_iff hp]
    simp only [monicFactorsMod, hnf, Multiset.toFinset_singleton, Finset.mem_singleton,
      exists_eq_left]
    rw [multiplicity_eq_count (by rw [hnf]; exact Multiset.mem_singleton_self _) hg0, hnf]
    simp

theorem splitType_of_eq_mul (hp : ¬ p ∣ exponent θ) {a b : ZMod p} (hab : a ≠ b)
    (h : (minpoly ℤ θ).map (Int.castRingHom (ZMod p)) = (X - C a) * (X - C b)) :
    SplitType K p 1 := by
  have hg0 : (minpoly ℤ θ).map (Int.castRingHom (ZMod p)) ≠ 0 := by
    rw [h]; exact mul_ne_zero (X_sub_C_ne_zero a) (X_sub_C_ne_zero b)
  have hnf : normalizedFactors ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))) =
      {X - C a, X - C b} := by rw [h, normalizedFactors_X_sub_C_mul]
  have hne : X - C a ≠ X - C b := fun h' => hab (C_inj.mp (sub_right_injective h'))
  refine ⟨?_, ?_, ?_⟩
  · rw [isSplitIn_iff hp]
    simp only [iff_true]
    refine ⟨X - C a, ?_, X - C b, ?_, hne⟩ <;> simp [monicFactorsMod, hnf]
  · rw [isInertIn_iff hp, h]; simp [not_irreducible_X_sub_C_mul]
  · rw [isRamifiedIn_iff hp]
    simp only [show (1 : ℤ) ≠ 0 from one_ne_zero, iff_false, not_exists, not_and, not_lt]
    intro Q hQ
    have hQ' : Q ∈ normalizedFactors ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))) :=
      Multiset.mem_toFinset.mp hQ
    rw [multiplicity_eq_count hQ' hg0, hnf]
    rw [hnf] at hQ'
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hQ'
    rcases hQ' with rfl | rfl <;> simp [hne, hne.symm]

theorem splitType_of_eq_mul_self (hp : ¬ p ∣ exponent θ) {a : ZMod p}
    (h : (minpoly ℤ θ).map (Int.castRingHom (ZMod p)) = (X - C a) * (X - C a)) :
    SplitType K p 0 := by
  have hg0 : (minpoly ℤ θ).map (Int.castRingHom (ZMod p)) ≠ 0 := by
    rw [h]; exact mul_ne_zero (X_sub_C_ne_zero a) (X_sub_C_ne_zero a)
  have hnf : normalizedFactors ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))) =
      {X - C a, X - C a} := by rw [h, normalizedFactors_X_sub_C_mul]
  refine ⟨?_, ?_, ?_⟩
  · rw [isSplitIn_iff hp]
    simp only [show (0 : ℤ) ≠ 1 from zero_ne_one, iff_false, not_exists, not_and, not_not]
    intro Q₁ h₁ Q₂ h₂
    simp only [monicFactorsMod, hnf, Multiset.insert_eq_cons, Multiset.toFinset_cons,
      Multiset.toFinset_singleton, Finset.mem_insert, Finset.mem_singleton, or_self] at h₁ h₂
    rw [h₁, h₂]
  · rw [isInertIn_iff hp, h]; simp [not_irreducible_X_sub_C_mul]
  · rw [isRamifiedIn_iff hp]
    simp only [iff_true]
    refine ⟨X - C a, by simp [monicFactorsMod, hnf], ?_⟩
    rw [multiplicity_eq_count (by rw [hnf]; simp) hg0, hnf]
    simp

end Types

/-! ## `ε_D(p)` is the splitting character -/

section Main

open RingOfIntegers ZMod

variable [NumberField K]

variable {D : ℤ} {δ : K}

theorem ite_eq_of_pos {α : Type*} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]

theorem ite_eq_of_neg {α : Type*} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) :
    (if c then a else b) = b := by simp [h]

theorem two_ne_zero_zmod {p : ℕ} [hp : Fact p.Prime] (h2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  exact h2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this)

theorem zmod2_no_root : ∀ r : ZMod 2, r ^ 2 - 1 * r + 1 ≠ 0 := by decide

theorem intCast_zmod_two (z : ℤ) : (z : ZMod 2) = ((z % 2 : ℤ) : ZMod 2) :=
  (ZMod.intCast_mod z 2).symm

/-- **`ε_D(p)` is `1`, `-1` or `0` according as `p` splits, is inert or ramifies in
`K = ℚ(√D)`**, for a negative fundamental discriminant `D` and every prime `p`. -/
theorem splitType_epsD (hD : Int.IsFundamentalDiscr D) (hneg : D < 0)
    (hK : Module.finrank ℚ K = 2) (hδ : δ ^ 2 = (D : K)) {p : ℕ} (hpp : p.Prime) :
    SplitType K p (ZInQ.HGZSteps.epsD D p) := by
  have := Fact.mk hpp
  have hexp : ¬ p ∣ exponent (thetaO hD hδ) := by
    rw [exponent_eq_one_iff.mpr (adjoin_thetaO_eq_top hD hneg hK hδ)]
    exact hpp.not_dvd_one
  have hg : (minpoly ℤ (thetaO hD hδ)).map (Int.castRingHom (ZMod p)) =
      X ^ 2 - C (D : ZMod p) * X + C ((cD D : ℤ) : ZMod p) := by
    rw [minpoly_thetaO hD hneg hδ]; simp [gD]
  have h4 : (4 : ZMod p) * (cD D : ZMod p) = (D : ZMod p) ^ 2 - D := by
    have := congrArg (Int.cast : ℤ → ZMod p) (four_mul_cD hD.1); push_cast at this; exact this
  rw [ZInQ.HGZSteps.epsD_prime D hpp, ZInQ.HGZSteps.kronPrime]
  by_cases h2 : p = 2
  · subst h2
    rw [ite_eq_of_pos rfl, χ₈_int_eq_if_mod_eight]
    have h4' := four_mul_cD hD.1
    rcases Int.isFundamentalDiscr_iff_squarefree.mp hD with ⟨h1, _⟩ | ⟨h0, _, hm⟩
    · have hodd : D % 2 ≠ 0 := by omega
      rw [ite_eq_of_neg hodd]
      have hD1 : (D : ZMod 2) = 1 := by rw [intCast_zmod_two, show D % 2 = 1 by omega]; rfl
      obtain ⟨k, hk⟩ : ∃ k, D = 8 * k + D % 8 := ⟨D / 8, by omega⟩
      by_cases h8 : D % 8 = 1
      · rw [ite_eq_of_pos (Or.inl h8)]
        have hc2 : cD D % 2 = 0 := by
          generalize cD D = c at h4'
          rw [h8] at hk; subst hk; ring_nf at h4'; omega
        have hc : (cD D : ZMod 2) = 0 := by rw [intCast_zmod_two, hc2]; rfl
        apply splitType_of_eq_mul hexp (a := 0) (b := 1) zero_ne_one
        rw [hg, hD1, hc]; exact quadratic_eq_mul (by rfl) (by rfl)
      · have h5 : D % 8 = 5 := by omega
        rw [ite_eq_of_neg (by omega)]
        have hc2 : cD D % 2 = 1 := by
          generalize cD D = c at h4'
          rw [h5] at hk; subst hk; ring_nf at h4'; omega
        have hc : (cD D : ZMod 2) = 1 := by rw [intCast_zmod_two, hc2]; rfl
        apply splitType_of_irreducible hexp
        rw [hg, hD1, hc]
        apply irreducible_of_degree_le_three_of_not_isRoot
        · rw [Finset.mem_Icc, natDegree_quad]; norm_num
        · intro r hr
          simp only [IsRoot, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at hr
          exact zmod2_no_root r hr
    · rw [ite_eq_of_pos (by omega)]
      obtain ⟨m, rfl⟩ : 4 ∣ D := Int.dvd_of_emod_eq_zero h0
      rw [Int.mul_ediv_cancel_left m four_ne_zero] at hm
      have hcm : cD (4 * m) = 4 * m ^ 2 - m := by
        have : 4 * cD (4 * m) = 4 * (4 * m ^ 2 - m) := by rw [h4']; ring
        omega
      have hD0 : ((4 * m : ℤ) : ZMod 2) = 0 := by
        rw [intCast_zmod_two, show 4 * m % 2 = 0 by omega]; rfl
      rcases hm with hm | hm
      · have hc : (cD (4 * m) : ZMod 2) = 0 := by
          rw [intCast_zmod_two, hcm]
          obtain ⟨j, hj⟩ : ∃ j, m = 4 * j + 2 := ⟨m / 4, by omega⟩
          subst hj; rw [show (4 * (4 * j + 2) ^ 2 - (4 * j + 2)) % 2 = 0 by ring_nf; omega]; rfl
        apply splitType_of_eq_mul_self hexp (a := 0)
        rw [hg, hD0, hc]; exact quadratic_eq_mul (by rfl) (by rfl)
      · have hc : (cD (4 * m) : ZMod 2) = 1 := by
          rw [intCast_zmod_two, hcm]
          obtain ⟨j, hj⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
          subst hj; rw [show (4 * (4 * j + 3) ^ 2 - (4 * j + 3)) % 2 = 1 by ring_nf; omega]; rfl
        apply splitType_of_eq_mul_self hexp (a := 1)
        rw [hg, hD0, hc]; exact quadratic_eq_mul (by rfl) (by rfl)
  · rw [ite_eq_of_neg h2, ← jacobiSym.legendreSym.to_jacobiSym]
    have h2' := two_ne_zero_zmod h2
    have h4ne : (4 : ZMod p) ≠ 0 := by
      rw [show (4 : ZMod p) = 2 * 2 by norm_num]; exact mul_ne_zero h2' h2'
    by_cases hD0 : (D : ZMod p) = 0
    · rw [(legendreSym.eq_zero_iff p D).mpr hD0]
      have hc : ((cD D : ℤ) : ZMod p) = 0 := by
        rw [hD0] at h4
        simpa [h4ne] using h4
      apply splitType_of_eq_mul_self hexp (a := 0)
      rw [hg, hD0, hc]; exact quadratic_eq_mul (by simp) (by simp)
    · by_cases hsq : IsSquare (D : ZMod p)
      · rw [(legendreSym.eq_one_iff p hD0).mpr hsq]
        obtain ⟨s, hs⟩ := hsq
        apply splitType_of_eq_mul hexp (a := (D + s) / 2) (b := (D - s) / 2)
        · intro h
          apply hD0
          have hs0 : s = 0 := by
            field_simp at h
            have : (2 : ZMod p) * s = 0 := by linear_combination h
            exact (mul_eq_zero.mp this).resolve_left h2'
          rw [hs, hs0, mul_zero]
        · rw [hg]
          apply quadratic_eq_mul
          · field_simp; ring
          · field_simp
            linear_combination hs - h4
      · rw [(legendreSym.eq_neg_one_iff p).mpr hsq]
        apply splitType_of_irreducible hexp
        rw [hg]
        apply irreducible_of_degree_le_three_of_not_isRoot
        · rw [Finset.mem_Icc, natDegree_quad]; norm_num
        · intro r hr
          simp only [IsRoot, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at hr
          exact hsq ⟨2 * r - D, by linear_combination (-4) * hr + h4⟩

/-- The three statements of `splitType_epsD`, separately. -/
theorem epsD_eq_one_iff_isSplitIn (hD : Int.IsFundamentalDiscr D) (hneg : D < 0)
    (hK : Module.finrank ℚ K = 2) (hδ : δ ^ 2 = (D : K)) {p : ℕ} (hp : p.Prime) :
    ZInQ.HGZSteps.epsD D p = 1 ↔ IsSplitIn K p :=
  (splitType_epsD hD hneg hK hδ hp).1.symm

theorem epsD_eq_neg_one_iff_isInertIn (hD : Int.IsFundamentalDiscr D) (hneg : D < 0)
    (hK : Module.finrank ℚ K = 2) (hδ : δ ^ 2 = (D : K)) {p : ℕ} (hp : p.Prime) :
    ZInQ.HGZSteps.epsD D p = -1 ↔ IsInertIn K p :=
  (splitType_epsD hD hneg hK hδ hp).2.1.symm

theorem epsD_eq_zero_iff_isRamifiedIn (hD : Int.IsFundamentalDiscr D) (hneg : D < 0)
    (hK : Module.finrank ℚ K = 2) (hδ : δ ^ 2 = (D : K)) {p : ℕ} (hp : p.Prime) :
    ZInQ.HGZSteps.epsD D p = 0 ↔ IsRamifiedIn K p :=
  (splitType_epsD hD hneg hK hδ hp).2.2.symm

theorem epsD_prime_trichotomy (D : ℤ) {p : ℕ} (hp : p.Prime) :
    ZInQ.HGZSteps.epsD D p = 0 ∨ ZInQ.HGZSteps.epsD D p = 1 ∨ ZInQ.HGZSteps.epsD D p = -1 := by
  rw [ZInQ.HGZSteps.epsD_prime D hp, ZInQ.HGZSteps.kronPrime]
  split_ifs
  · rw [χ₈_int_eq_if_mod_eight]; split_ifs <;> simp
  · exact jacobiSym.trichotomy D p

end Main

/-! ## `ε_K = ε_D` -/

section Char

variable [NumberField K] {D : ℤ} {δ : K}

theorem quadCharPrime_eq_epsD (hD : Int.IsFundamentalDiscr D) (hneg : D < 0)
    (hK : Module.finrank ℚ K = 2) (hδ : δ ^ 2 = (D : K)) {p : ℕ} (hp : p.Prime) :
    quadCharPrime K p = ZInQ.HGZSteps.epsD D p := by
  obtain ⟨hs, hi, hr⟩ := splitType_epsD hD hneg hK hδ hp
  unfold quadCharPrime
  split_ifs with h1 h2
  · exact (hs.mp h1).symm
  · exact (hi.mp h2).symm
  · rcases epsD_prime_trichotomy D hp with h | h | h
    · exact h.symm
    · exact absurd (hs.mpr h) h1
    · exact absurd (hi.mpr h) h2

/-- **`ε_K = ε_D`**: the quadratic character of `K = ℚ(√D)` is the Kronecker symbol `(D/·)`. -/
theorem quadChar_eq_epsD (hD : Int.IsFundamentalDiscr D) (hneg : D < 0)
    (hK : Module.finrank ℚ K = 2) (hδ : δ ^ 2 = (D : K)) (n : ℕ) :
    quadChar K n = ZInQ.HGZSteps.epsD D n := by
  unfold quadChar ZInQ.HGZSteps.epsD
  split_ifs with hn h1
  · exfalso
    have := hD.1
    omega
  · rfl
  · refine Finsupp.prod_congr fun p hp => ?_
    rw [Nat.support_factorization] at hp
    rw [quadCharPrime_eq_epsD hD hneg hK hδ (Nat.prime_of_mem_primeFactors hp),
      ZInQ.HGZSteps.epsD_prime D (Nat.prime_of_mem_primeFactors hp)]

end Char

end ZInQ.EpsSplit

import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.LocalCommon
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.SqrtDiscr
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.EulerJacobi
import ZInQKernel.Contrib.CloudB3RC53.Companion.Disc
import ZInQKernel.Contrib.OneProof.RC.TwistDictionary.Unramified
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.NumberField.Norm

/-!
# GenusOdd: the decomposition law in a quadratic field of odd discriminant (PROVED)

For a quadratic field `K` with odd discriminant `D`:

* `discr_mod_four_of_odd`, `squarefree_discr_of_odd`: `D ≡ 1 (mod 4)` (`D = T² − 4N` from an
  integral basis) and `D` is squarefree (`K = ℚ(√m)`, `4m = D i²`);
* `chiD_eq_kronecker`: GenusOdd's `χ_d(p) = (p/|d|)` is the Kronecker symbol `(d/p)` for
  `d ≡ 1 (mod 4)`;
* `decomposition`: every prime `p` splits (two primes of norm `p`, `(D/p) = 1`), is inert (one prime
  of norm `p²`, `(D/p) = −1`) or ramifies (one prime of norm `p` with `𝔭² ∣ p`, `p ∣ D`).

Route: Mathlib's `Σ e f = [K : ℚ]` (`sum_ramification_inertia_eq_finrank`), `N𝔭 = p^f`
(`natAbs_pow_inertiaDeg`), Dedekind's criterion (`not_dvd_discr_iff_forall_liesOver`); a split prime
has residue field `𝔽_p`, where `√D` (or `(1 + √D)/2` at `p = 2`) forces `(D/p) = 1`; at an inert
prime `(D/p) = 1` is excluded by the splitting criterion (`splittingCriterion_proof`). Helper lemmas
live in the namespace `Decomp`. All results are PROVED.
-/

noncomputable section

open NumberField IsDedekindDomain

namespace ZInQ.Contrib.CloudB3RC53.GenusOdd

open ZInQ.Contrib.CloudB3RC53.CST ZInQ.Manuscript.RC.PrintsAnalytic ZInQ.Manuscript.RC.TwistDictionary

variable {K : Type} [Field K] [NumberField K]

/-! ### The discriminant -/

namespace Decomp



/-- `disc K = (b₀ τb₁ − b₁ τb₀)²` for an integral basis `b₀, b₁` and the nontrivial automorphism `τ`
(PROVED; the explicit form of `exists_sq_eq_discr`). -/
theorem discr_eq_sq_basis (hK2 : Module.finrank ℚ K = 2) :
    ∃ (b₀ b₁ : 𝓞 K) (τ : K ≃ₐ[ℚ] K), τ ≠ 1 ∧
      (discr K : K) = ((b₀ : K) * τ b₁ - (b₁ : K) * τ b₀) ^ 2 := by
  classical
  have : Algebra.IsQuadraticExtension ℚ K := ⟨hK2⟩
  have hcardN : Nat.card (K ≃ₐ[ℚ] K) = 2 := by rw [IsGalois.card_aut_eq_finrank, hK2]
  have hcard : Fintype.card (K ≃ₐ[ℚ] K) = 2 := by rw [← Nat.card_eq_fintype_card, hcardN]
  obtain ⟨τ, hτ⟩ : ∃ τ : K ≃ₐ[ℚ] K, τ ≠ 1 := by
    by_contra h
    push Not at h
    have : Fintype.card (K ≃ₐ[ℚ] K) ≤ 1 := Fintype.card_le_one_iff.mpr fun a b => by
      rw [h a, h b]
    omega
  set b0 := integralBasis K
  have hι : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = 2 := by
    rw [← Module.finrank_eq_card_basis b0, hK2]
  set e := Fintype.equivFinOfCardEq hι
  set b : Fin 2 → K := b0 ∘ e.symm
  have hd : (discr K : ℚ) = Algebra.discr ℚ b := by
    rw [coe_discr]
    exact (Algebra.discr_reindex ℚ b0 e).symm
  have htr : ∀ x : K, algebraMap ℚ K (Algebra.trace ℚ K x) = x + τ x := fun x => by
    rw [trace_eq_sum_automorphisms, sum_aut_eq_of_card_two hτ hcard]
  refine ⟨RingOfIntegers.basis K (e.symm 0), RingOfIntegers.basis K (e.symm 1), τ, hτ, ?_⟩
  have hb : ∀ i, b i = (RingOfIntegers.basis K (e.symm i) : K) := fun i => by
    simp only [b, b0, Function.comp_apply, integralBasis_apply]
  rw [← hb, ← hb]
  have : ((discr K : ℚ) : K) = (discr K : K) := by push_cast; rfl
  rw [← this, hd, Algebra.discr_def, Matrix.det_fin_two]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply]
  rw [← eq_ratCast (algebraMap ℚ K)]
  simp only [map_sub, map_mul, htr, map_mul]
  ring

/-- The nontrivial automorphism of a quadratic field is an involution (PROVED). -/
theorem aut_sq_eq_one (hK2 : Module.finrank ℚ K = 2) {τ : K ≃ₐ[ℚ] K} (hτ : τ ≠ 1) :
    τ * τ = 1 := by
  classical
  have : Algebra.IsQuadraticExtension ℚ K := ⟨hK2⟩
  have hcardN : Nat.card (K ≃ₐ[ℚ] K) = 2 := by rw [IsGalois.card_aut_eq_finrank, hK2]
  have := orderOf_dvd_natCard τ
  rw [hcardN] at this
  have h2 : orderOf τ = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp this with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hτ
    · exact h
  rw [← sq, ← h2, pow_orderOf_eq_one]

/-- `N(x) = x τx` in a quadratic field: the product over the two automorphisms (PROVED). -/
theorem prod_aut_eq_of_card_two {τ : K ≃ₐ[ℚ] K} (hτ : τ ≠ 1)
    [Fintype (K ≃ₐ[ℚ] K)] (hcard : Fintype.card (K ≃ₐ[ℚ] K) = 2) (x : K) :
    ∏ σ : K ≃ₐ[ℚ] K, σ x = x * τ x := by
  classical
  have huniv : (Finset.univ : Finset (K ≃ₐ[ℚ] K)) = {1, τ} := by
    symm
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair (Ne.symm hτ), hcard]
  rw [huniv, Finset.prod_pair (Ne.symm hτ)]
  rfl

/-- **`disc K = T² − 4N` with integers `T, N`** (PROVED): `T = Tr(b₀ τb₁)`, `N = N(b₀ τb₁)`. -/
theorem discr_eq_sq_sub (hK2 : Module.finrank ℚ K = 2) :
    ∃ T N : ℤ, discr K = T ^ 2 - 4 * N := by
  classical
  have : Algebra.IsQuadraticExtension ℚ K := ⟨hK2⟩
  have hcardN : Nat.card (K ≃ₐ[ℚ] K) = 2 := by rw [IsGalois.card_aut_eq_finrank, hK2]
  have hcard : Fintype.card (K ≃ₐ[ℚ] K) = 2 := by rw [← Nat.card_eq_fintype_card, hcardN]
  obtain ⟨b₀, b₁, τ, hτ, hD⟩ := discr_eq_sq_basis hK2
  have hττ : ∀ z, τ (τ z) = z := fun z => by
    have := congrArg (fun σ : K ≃ₐ[ℚ] K => σ z) (aut_sq_eq_one hK2 hτ)
    simpa using this
  have hint : IsIntegral ℤ ((b₀ : K) * τ b₁) :=
    b₀.2.mul (map_isIntegral_int τ b₁.2)
  set x : 𝓞 K := ⟨(b₀ : K) * τ b₁, hint⟩
  have hx : (x : K) = (b₀ : K) * τ b₁ := rfl
  have hτx : τ (x : K) = (b₁ : K) * τ b₀ := by rw [hx, map_mul, hττ]; ring
  refine ⟨Algebra.trace ℤ (𝓞 K) x, Algebra.norm ℤ x, ?_⟩
  have htr : ((Algebra.trace ℤ (𝓞 K) x : ℤ) : K) = (x : K) + τ x := by
    have h1 := Algebra.coe_trace_int (K := K) x
    have h2 : (((Algebra.trace ℤ (𝓞 K) x : ℤ) : ℚ) : K) = ((Algebra.trace ℤ (𝓞 K) x : ℤ) : K) := by
      push_cast; rfl
    rw [← h2, h1, ← eq_ratCast (algebraMap ℚ K), trace_eq_sum_automorphisms,
      sum_aut_eq_of_card_two hτ hcard]
  have hnm : ((Algebra.norm ℤ x : ℤ) : K) = (x : K) * τ x := by
    have h1 := Algebra.coe_norm_int (K := K) x
    have h2 : (((Algebra.norm ℤ x : ℤ) : ℚ) : K) = ((Algebra.norm ℤ x : ℤ) : K) := by
      push_cast; rfl
    rw [← h2, h1, ← eq_ratCast (algebraMap ℚ K), Algebra.norm_eq_prod_automorphisms,
      prod_aut_eq_of_card_two hτ hcard]
  have : ((discr K : ℤ) : K) = (((Algebra.trace ℤ (𝓞 K) x) ^ 2 - 4 * Algebra.norm ℤ x : ℤ) : K) := by
    push_cast
    rw [htr, hnm, hD, hτx, hx]
    ring
  exact_mod_cast this

end Decomp

open Decomp in
/-- **An odd discriminant of a quadratic field is `≡ 1 (mod 4)`** (PROVED). -/
theorem discr_mod_four_of_odd (hK2 : Module.finrank ℚ K = 2) (hodd : Odd (discr K)) :
    discr K % 4 = 1 := by
  obtain ⟨T, N, h⟩ := discr_eq_sq_sub hK2
  obtain ⟨k, hk⟩ := hodd
  rw [h] at hk ⊢
  rcases Int.even_or_odd T with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · exfalso
    have : (t + t) ^ 2 - 4 * N = 2 * (2 * t ^ 2 - 2 * N) := by ring
    rw [this] at hk
    generalize t ^ 2 = u at hk
    omega
  · have : (2 * t + 1) ^ 2 - 4 * N = 4 * (t ^ 2 + t - N) + 1 := by ring
    rw [this]
    generalize t ^ 2 = u
    omega

/-- **An odd discriminant of a quadratic field is squarefree** (PROVED). -/
theorem squarefree_discr_of_odd (hK2 : Module.finrank ℚ K = 2) (hodd : Odd (discr K)) :
    Squarefree (discr K) := by
  obtain ⟨θ, m, hm, hθ2, hθr⟩ := Splitting.exists_sqrt_gen hK2
  have hmin : minpoly ℚ (θ : K) = Polynomial.X ^ 2 + Polynomial.C ((0 : ℤ) : ℚ) * Polynomial.X +
      Polynomial.C ((-m : ℤ) : ℚ) :=
    Splitting.minpoly_eq_of_aeval hK2 hθr 0 (-m) (by rw [hθ2]; push_cast; ring)
  obtain ⟨i, hi⟩ := Companion.discr_mul_sq_int hK2 hmin
  have hi' : 4 * m = discr K * i ^ 2 := by linear_combination hi
  have hev : Even (discr K * i ^ 2) := ⟨2 * m, by rw [← hi']; ring⟩
  have hiev : Even i := by
    rcases Int.even_mul.mp hev with h | h
    · exact absurd h (Int.not_even_iff_odd.mpr hodd)
    · exact (Int.even_pow.mp h).1
  obtain ⟨j, rfl⟩ := hiev
  have hmj : m = discr K * j ^ 2 := by
    have h4 : 4 * m = 4 * (discr K * j ^ 2) := by rw [hi']; ring
    linarith
  have hj : IsUnit j := hm j ⟨discr K, by rw [hmj]; ring⟩
  have hj2 : j ^ 2 = 1 := by rcases Int.isUnit_iff.mp hj with rfl | rfl <;> norm_num
  rw [hj2, mul_one] at hmj
  rw [← hmj]; exact hm


/-! ### The Kronecker symbol -/



/-- **`χ_d(p)` is the Kronecker symbol `(d/p)`** for `d ≡ 1 (mod 4)` and every prime `p` (PROVED):
`(p/|d|) = (d/p)` by reciprocity for odd `p`; at `p = 2`, `(2/|d|) = χ₈(|d|)` matches
`kroneckerTwo d` via `d mod 8`. -/
theorem chiD_eq_kronecker {d : ℤ} (hd : d % 4 = 1) {p : ℕ} (hp : p.Prime) :
    chiD d p = kronecker d p := by
  unfold chiD
  by_cases hp2 : p = 2
  · subst hp2
    rw [kronecker_two]
    have hodd : Odd d.natAbs := by
      rw [Int.natAbs_odd]; exact Int.odd_iff.mpr (by omega)
    rw [show ((2 : ℕ) : ℤ) = 2 from rfl, jacobiSym.at_two hodd, ZMod.χ₈_nat_eq_if_mod_eight]
    unfold kroneckerTwo
    have h1 : d.natAbs % 2 ≠ 0 := by omega
    rcases le_or_gt 0 d with h0 | h0
    · have : (d.natAbs : ℤ) = d := Int.natAbs_of_nonneg h0
      split_ifs <;> omega
    · have : (d.natAbs : ℤ) = -d := by omega
      split_ifs <;> omega
  · rw [kronecker_prime_of_ne_two hp hp2,
      jacobiSym_one_mod_four_swap hd (hp.odd_of_ne_two hp2)]


/-! ### Primes above `p` -/

namespace Decomp



/-- `pℤ` is maximal (PROVED). -/
theorem spanP_isMaximal {p : ℕ} (hp : p.Prime) : (Ideal.span {(p : ℤ)}).IsMaximal :=
  ((Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
    (Nat.prime_iff_prime_int.mp hp)).isMaximal (by simpa using hp.ne_zero)

omit [NumberField K] in
/-- A prime of `𝓞_K` containing `p` lies over `pℤ` (PROVED). -/
theorem liesOver_of_mem {p : ℕ} (hp : p.Prime) {Q : Ideal (𝓞 K)} [hQ : Q.IsPrime]
    (h : ((p : ℤ) : 𝓞 K) ∈ Q) : Q.LiesOver (Ideal.span {(p : ℤ)}) := by
  refine ⟨((spanP_isMaximal hp).eq_of_le (Ideal.IsPrime.under ℤ Q).ne_top ?_)⟩
  rw [Ideal.span_le, Set.singleton_subset_iff]
  show ((p : ℤ)) ∈ Ideal.comap (algebraMap ℤ (𝓞 K)) Q
  rw [Ideal.mem_comap, eq_intCast]
  exact h

omit [NumberField K] in
/-- A prime of `𝓞_K` over `pℤ` contains `p` (PROVED). -/
theorem mem_of_liesOver {p : ℕ} {Q : Ideal (𝓞 K)} [hQ : Q.LiesOver (Ideal.span {(p : ℤ)})] :
    ((p : ℤ) : 𝓞 K) ∈ Q := by
  have h1 : (p : ℤ) ∈ Q.under ℤ := by
    rw [← hQ.over]; exact Ideal.mem_span_singleton_self _
  rw [Ideal.under, Ideal.mem_comap, eq_intCast] at h1
  exact h1

/-- An ideal of `𝓞_K` containing a prime `p` is nonzero (PROVED). -/
theorem ne_bot_of_mem {p : ℕ} (hp : p.Prime) {Q : Ideal (𝓞 K)} (h : ((p : ℤ) : 𝓞 K) ∈ Q) :
    Q ≠ ⊥ := by
  rintro rfl
  rw [Ideal.mem_bot] at h
  have : ((p : ℤ) : 𝓞 K) ≠ 0 := by exact_mod_cast hp.ne_zero
  exact this h

/-- Finitely many primes of `K` lie above `p` (PROVED). -/
theorem primesAbove_finite (p : ℕ) (hp : p.Prime) : (primesAbove K p).Finite := by
  have := spanP_isMaximal hp
  have hfin : (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) |>.Finite := Set.toFinite _
  refine Set.Finite.of_finite_image (f := fun 𝔭 : HeightOneSpectrum (𝓞 K) => 𝔭.asIdeal) ?_
    (fun a _ b _ h => HeightOneSpectrum.ext h)
  refine hfin.subset ?_
  rintro _ ⟨𝔭, h𝔭, rfl⟩
  exact ⟨𝔭.isPrime, liesOver_of_mem hp h𝔭⟩

/-- `e(𝔭) f(𝔭)`, ramification index times inertia degree of `𝔭` over `ℤ`. -/
def efAt (𝔭 : HeightOneSpectrum (𝓞 K)) : ℕ :=
  𝔭.asIdeal.ramificationIdx ℤ * 𝔭.asIdeal.inertiaDeg ℤ

/-- The equivalence between Mathlib's `primesOver` and `primesAbove`. -/
def primesOverEquiv (p : ℕ) (hp : p.Prime) :
    (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) ≃ primesAbove K p where
  toFun Q := ⟨⟨Q.1, Q.2.1, ne_bot_of_mem hp (by have := Q.2.2; exact mem_of_liesOver)⟩,
    by have := Q.2.2; exact mem_of_liesOver⟩
  invFun 𝔭 := ⟨𝔭.1.asIdeal, 𝔭.1.isPrime, liesOver_of_mem hp 𝔭.2⟩
  left_inv Q := rfl
  right_inv 𝔭 := rfl

/-- **`Σ_{𝔭 | p} e(𝔭) f(𝔭) = 2`** in a quadratic field (PROVED; Mathlib's
`sum_ramification_inertia_eq_finrank`). -/
theorem sum_efAt (hK2 : Module.finrank ℚ K = 2) {p : ℕ} (hp : p.Prime) :
    ∑ 𝔭 ∈ (primesAbove_finite (K := K) p hp).toFinset, efAt 𝔭 = 2 := by
  classical
  have := spanP_isMaximal hp
  let _ : Fintype ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K)) := Fintype.ofFinite _
  have h := Ideal.sum_ramification_inertia_eq_finrank (Ideal.span {(p : ℤ)}) (𝓞 K)
  rw [RingOfIntegers.rank, hK2] at h
  let _ : Fintype (primesAbove K p) := (primesAbove_finite p hp).fintype
  rw [← h, Finset.sum_subtype _ (fun x => (primesAbove_finite (K := K) p hp).mem_toFinset)]
  exact Fintype.sum_equiv (primesOverEquiv p hp).symm _ _ (fun _ => rfl)

omit [NumberField K] in
/-- `pℤ · 𝓞_K = p 𝓞_K` (PROVED). -/
theorem span_map_eq (p : ℕ) :
    (Ideal.span {(p : ℤ)}).map (algebraMap ℤ (𝓞 K)) = Ideal.span {((p : ℤ) : 𝓞 K)} := by
  rw [Ideal.map_span, Set.image_singleton, eq_intCast]

/-- `e(𝔭)` is the multiplicity of `𝔭` in `p 𝓞_K` (PROVED). -/
theorem ramificationIdx_eq_mult {p : ℕ} (hp : p.Prime) {𝔭 : HeightOneSpectrum (𝓞 K)}
    (h𝔭 : 𝔭 ∈ primesAbove K p) :
    𝔭.asIdeal.ramificationIdx ℤ = multiplicity 𝔭.asIdeal (Ideal.span {((p : ℤ) : 𝓞 K)}) := by
  have := liesOver_of_mem hp h𝔭
  have hne : (Ideal.span {(p : ℤ)}).map (algebraMap ℤ (𝓞 K)) ≠ ⊥ := by
    rw [span_map_eq, Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hp.ne_zero
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity (Ideal.span {(p : ℤ)}) _ hne,
    span_map_eq]

/-- The multiplicity of `𝔭` in `p 𝓞_K` is finite (PROVED). -/
theorem finiteMult {p : ℕ} (hp : p.Prime) (𝔭 : HeightOneSpectrum (𝓞 K)) :
    FiniteMultiplicity 𝔭.asIdeal (Ideal.span {((p : ℤ) : 𝓞 K)}) :=
  Ideal.finiteMultiplicity 𝔭.isPrime.ne_top (by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hp.ne_zero)

/-- `e(𝔭) ≥ 1` for `𝔭 ∣ p` (PROVED). -/
theorem one_le_ramificationIdx {p : ℕ} (hp : p.Prime) {𝔭 : HeightOneSpectrum (𝓞 K)}
    (h𝔭 : 𝔭 ∈ primesAbove K p) : 1 ≤ 𝔭.asIdeal.ramificationIdx ℤ := by
  rw [ramificationIdx_eq_mult hp h𝔭]
  exact multiplicity_pos_of_dvd (Ideal.dvd_span_singleton.mpr h𝔭) (finiteMult hp 𝔭)

/-- `UnramifiedOver 𝔭 p` (`𝔭² ∤ p𝓞_K`) is `e(𝔭) = 1` (PROVED). -/
theorem unramifiedOver_iff {p : ℕ} (hp : p.Prime) {𝔭 : HeightOneSpectrum (𝓞 K)}
    (h𝔭 : 𝔭 ∈ primesAbove K p) : UnramifiedOver 𝔭 p ↔ 𝔭.asIdeal.ramificationIdx ℤ = 1 := by
  have h1 := one_le_ramificationIdx hp h𝔭
  unfold UnramifiedOver
  rw [← (finiteMult hp 𝔭).multiplicity_lt_iff_not_dvd, ← ramificationIdx_eq_mult hp h𝔭]
  omega

/-- **`N𝔭 = p^{f(𝔭)}`** for `𝔭 ∣ p` (PROVED). -/
theorem absNorm_eq_pow {p : ℕ} (hp : p.Prime) {𝔭 : HeightOneSpectrum (𝓞 K)}
    (h𝔭 : 𝔭 ∈ primesAbove K p) : Ideal.absNorm 𝔭.asIdeal = p ^ 𝔭.asIdeal.inertiaDeg ℤ := by
  have := liesOver_of_mem hp h𝔭
  rw [← Ideal.natAbs_pow_inertiaDeg (p : ℤ) 𝔭.asIdeal, Int.natAbs_natCast]

/-- `f(𝔭) ≥ 1` (PROVED). -/
theorem one_le_inertiaDeg (𝔭 : HeightOneSpectrum (𝓞 K)) : 1 ≤ 𝔭.asIdeal.inertiaDeg ℤ :=
  Ideal.inertiaDeg_pos _ _

/-- **Dedekind**: `p ∣ disc K` iff some prime above `p` has `e ≠ 1` (PROVED from Mathlib's
`not_dvd_discr_iff_forall_liesOver`). -/
theorem dvd_discr_iff {p : ℕ} (hp : p.Prime) :
    (p : ℤ) ∣ discr K ↔ ∃ 𝔭 ∈ primesAbove K p, 𝔭.asIdeal.ramificationIdx ℤ ≠ 1 := by
  rw [← not_iff_not, NumberField.not_dvd_discr_iff_forall_liesOver K (𝓞 K)
    (Nat.prime_iff_prime_int.mp hp)]
  push Not
  constructor
  · intro H 𝔭 h𝔭
    have := liesOver_of_mem hp h𝔭
    have hm := 𝔭.isMaximal
    exact Ideal.ramificationIdx_eq_one_iff.mpr (H _ hm this)
  · intro H P hP hlo
    have hne := ne_bot_of_mem hp (mem_of_liesOver (Q := P))
    exact Ideal.ramificationIdx_eq_one_iff.mp (H ⟨P, hP.isPrime, hne⟩ (mem_of_liesOver (Q := P)))

/-- `e f = 1` forces `e = f = 1` (PROVED). -/
theorem eq_one_of_mul_eq_one {e f : ℕ} (h : e * f = 1) : e = 1 ∧ f = 1 :=
  ⟨Nat.eq_one_of_mul_eq_one_right h, Nat.eq_one_of_mul_eq_one_left h⟩

/-- `e f = 2` with `e, f ≥ 1`: `(e, f) = (1, 2)` or `(2, 1)` (PROVED). -/
theorem cases_of_mul_eq_two {e f : ℕ} (he : 1 ≤ e) (hf : 1 ≤ f) (h : e * f = 2) :
    (e = 1 ∧ f = 2) ∨ (e = 2 ∧ f = 1) := by
  rcases Nat.lt_or_ge e 2 with h1 | h1
  · left; have : e = 1 := by omega
    subst this; omega
  · right
    rcases Nat.lt_or_ge f 2 with h2 | h2
    · have : f = 1 := by omega
      subst this; omega
    · nlinarith

/-- **The shape of the primes above `p`** in a quadratic field: two primes with `e = f = 1`, or one
prime with `(e, f) = (1, 2)` or `(2, 1)`. -/
theorem primesAbove_cases (hK2 : Module.finrank ℚ K = 2) {p : ℕ} (hp : p.Prime) :
    (∃ 𝔭 𝔮 : HeightOneSpectrum (𝓞 K), 𝔭 ≠ 𝔮 ∧ primesAbove K p = {𝔭, 𝔮} ∧
      𝔭.asIdeal.ramificationIdx ℤ = 1 ∧ 𝔭.asIdeal.inertiaDeg ℤ = 1 ∧
      𝔮.asIdeal.ramificationIdx ℤ = 1 ∧ 𝔮.asIdeal.inertiaDeg ℤ = 1) ∨
    (∃ 𝔭 : HeightOneSpectrum (𝓞 K), primesAbove K p = {𝔭} ∧
      𝔭.asIdeal.ramificationIdx ℤ = 1 ∧ 𝔭.asIdeal.inertiaDeg ℤ = 2) ∨
    (∃ 𝔭 : HeightOneSpectrum (𝓞 K), primesAbove K p = {𝔭} ∧
      𝔭.asIdeal.ramificationIdx ℤ = 2 ∧ 𝔭.asIdeal.inertiaDeg ℤ = 1) := by
  classical
  set T := (primesAbove_finite (K := K) p hp).toFinset with hT
  have hsum : ∑ 𝔭 ∈ T, efAt 𝔭 = 2 := sum_efAt hK2 hp
  have hmem : ∀ 𝔭, 𝔭 ∈ T ↔ 𝔭 ∈ primesAbove K p := fun 𝔭 => Set.Finite.mem_toFinset _
  have hpos : ∀ 𝔭 ∈ T, 1 ≤ efAt 𝔭 := fun 𝔭 h𝔭 =>
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
      (Nat.one_le_iff_ne_zero.mp (one_le_ramificationIdx hp ((hmem 𝔭).mp h𝔭)))
      (Nat.one_le_iff_ne_zero.mp (one_le_inertiaDeg 𝔭)))
  have hsub : ∀ S ⊆ T, ∑ 𝔭 ∈ S, efAt 𝔭 ≤ 2 := fun S hS => hsum ▸
    Finset.sum_le_sum_of_subset hS
  obtain ⟨𝔭, h𝔭⟩ : T.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; rintro h; rw [h, Finset.sum_empty] at hsum; omega
  have he𝔭 := one_le_ramificationIdx hp ((hmem 𝔭).mp h𝔭)
  have hf𝔭 := one_le_inertiaDeg 𝔭
  have hset : ∀ S : Finset (HeightOneSpectrum (𝓞 K)), T = S → primesAbove K p = ↑S := by
    intro S hS; ext 𝔮; rw [← hmem, hS]; rfl
  by_cases hone : T = {𝔭}
  · rw [hone, Finset.sum_singleton] at hsum
    rcases cases_of_mul_eq_two he𝔭 hf𝔭 hsum with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr (Or.inl ⟨𝔭, by rw [hset _ hone]; simp, h1, h2⟩)
    · exact Or.inr (Or.inr ⟨𝔭, by rw [hset _ hone]; simp, h1, h2⟩)
  · obtain ⟨𝔮, h𝔮, hne⟩ : ∃ 𝔮 ∈ T, 𝔮 ≠ 𝔭 := by
      by_contra h
      push Not at h
      exact hone (Finset.eq_singleton_iff_unique_mem.mpr ⟨h𝔭, h⟩)
    have h2 := hsub {𝔭, 𝔮} (Finset.insert_subset h𝔭 (Finset.singleton_subset_iff.mpr h𝔮))
    rw [Finset.sum_pair (Ne.symm hne)] at h2
    have hp1 := hpos 𝔭 h𝔭
    have hq1 := hpos 𝔮 h𝔮
    have hTeq : T = {𝔭, 𝔮} := by
      apply Finset.Subset.antisymm _ (Finset.insert_subset h𝔭 (Finset.singleton_subset_iff.mpr h𝔮))
      intro 𝔯 h𝔯
      by_contra h
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h
      have h3 := hsub {𝔭, 𝔮, 𝔯} (Finset.insert_subset h𝔭
        (Finset.insert_subset h𝔮 (Finset.singleton_subset_iff.mpr h𝔯)))
      rw [Finset.sum_insert (by simp [Ne.symm hne, Ne.symm h.1]),
        Finset.sum_pair (Ne.symm h.2)] at h3
      have := hpos 𝔯 h𝔯
      omega
    obtain ⟨a1, a2⟩ := eq_one_of_mul_eq_one (show efAt 𝔭 = 1 by omega)
    obtain ⟨b1, b2⟩ := eq_one_of_mul_eq_one (show efAt 𝔮 = 1 by omega)
    exact Or.inl ⟨𝔭, 𝔮, Ne.symm hne, by rw [hset _ hTeq]; simp, a1, a2, b1, b2⟩

/-! ### Values of the Kronecker symbol -/

/-- At a prime `p ∤ D` with `D ≡ 1 (mod 4)`: `(D/p) = 1` and `D` is a unit square at `p`, or
`(D/p) = −1`. -/
theorem kronecker_cases_of_not_dvd {D : ℤ} (hD : D % 4 = 1) {p : ℕ} (hp : p.Prime)
    (hpD : ¬ (p : ℤ) ∣ D) : (kronecker D p = 1 ∧ SquareAt p D) ∨ kronecker D p = -1 := by
  by_cases hp2 : p = 2
  · subst hp2
    rw [kronecker_two]
    unfold kroneckerTwo
    by_cases h8 : D % 8 = 1
    · left
      refine ⟨by split_ifs <;> omega, hpD, fun _ => h8, fun h => absurd rfl h⟩
    · right
      split_ifs <;> omega
  · have : Fact p.Prime := ⟨hp⟩
    have ha : (D : ZMod p) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    rw [kronecker_prime_of_ne_two hp hp2, ← jacobiSym.legendreSym.to_jacobiSym]
    rcases legendreSym.eq_one_or_neg_one p ha with h | h
    · exact Or.inl ⟨h, hpD, fun h' => absurd h' hp2, fun _ => (legendreSym.eq_one_iff p ha).mp h⟩
    · exact Or.inr h

/-- If `disc K` is a unit square at `p`, there are two distinct primes above `p`
(`splittingCriterion_proof`). -/
theorem two_primes_of_squareAt (hK2 : Module.finrank ℚ K = 2) {p : ℕ} (hp : p.Prime)
    (hsq : SquareAt p (discr K)) :
    ∃ 𝔞 ∈ primesAbove K p, ∃ 𝔟 ∈ primesAbove K p, 𝔞 ≠ 𝔟 := by
  have hs : SplitsIn K p := Splitting.splittingCriterion_proof K hK2 p hp hsq
  obtain ⟨𝔞, 𝔟, ha, hb, hne, hprod⟩ := hs
  have hpmem : ((p : ℤ) : 𝓞 K) ∈ 𝔞 * 𝔟 := by
    rw [← hprod, Int.cast_natCast]; exact Ideal.mem_span_singleton_self _
  have ha' : ((p : ℤ) : 𝓞 K) ∈ 𝔞 := Ideal.mul_le_left (I := 𝔞) (J := 𝔟) hpmem
  have hb' : ((p : ℤ) : 𝓞 K) ∈ 𝔟 := Ideal.mul_le_right (I := 𝔞) (J := 𝔟) hpmem
  refine ⟨⟨𝔞, ha.isPrime, ne_bot_of_mem hp ha'⟩, ha', ⟨𝔟, hb.isPrime, ne_bot_of_mem hp hb'⟩, hb',
    fun h => hne (congrArg HeightOneSpectrum.asIdeal h)⟩

/-- **At a prime of degree one over `p ∤ disc K`, `(disc K / p) = 1`** (PROVED): the residue field
`𝓞_K/𝔭` has `p` elements; for odd `p`, the image of `√(disc K) ∈ 𝓞_K` makes `disc K` a nonzero
square there (Euler's criterion, `pow_half_eq_jacobiSym`); for `p = 2`, the image of
`ω = (1 + √D)/2` satisfies `ω² = ω`, so `(D − 1)/4` is even. -/
theorem kronecker_eq_one_of_absNorm (hK2 : Module.finrank ℚ K = 2) (hodd : Odd (discr K))
    {p : ℕ} (hp : p.Prime) {𝔭 : HeightOneSpectrum (𝓞 K)} (h𝔭 : 𝔭 ∈ primesAbove K p)
    (hN : Ideal.absNorm 𝔭.asIdeal = p) (hpD : ¬ (p : ℤ) ∣ discr K) :
    kronecker (discr K) p = 1 := by
  classical
  have hD4 := discr_mod_four_of_odd hK2 hodd
  have : Fact p.Prime := ⟨hp⟩
  let _ : Field (𝓞 K ⧸ 𝔭.asIdeal) := Ideal.Quotient.field _
  have : Finite (𝓞 K ⧸ 𝔭.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient 𝔭.ne_bot
  let _ : Fintype (𝓞 K ⧸ 𝔭.asIdeal) := Fintype.ofFinite _
  have hcard : Fintype.card (𝓞 K ⧸ 𝔭.asIdeal) = p := by
    rw [Fintype.card_eq_nat_card, ← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have : CharP (𝓞 K ⧸ 𝔭.asIdeal) p := charP_of_card_eq_prime hcard
  have hmk : ∀ n : ℤ, (Ideal.Quotient.mk 𝔭.asIdeal (n : 𝓞 K) = 0 ↔ (p : ℤ) ∣ n) := fun n => by
    rw [map_intCast, CharP.intCast_eq_zero_iff (𝓞 K ⧸ 𝔭.asIdeal) p]
  obtain ⟨r, hr⟩ := exists_sq_eq_discr hK2
  have hrint : IsIntegral ℤ r := IsIntegral.of_pow (n := 2) (by norm_num)
    (by rw [hr, ← eq_intCast (algebraMap ℤ K)]; exact isIntegral_algebraMap)
  set r' : 𝓞 K := ⟨r, hrint⟩
  have hr' : r' ^ 2 = (discr K : 𝓞 K) := by
    apply RingOfIntegers.ext; push_cast; exact hr
  by_cases hp2 : p = 2
  · subst hp2
    rw [kronecker_two]
    unfold kroneckerTwo
    -- `ω = (1 + r)/2`
    set t := discr K / 4
    have hDt : discr K = 4 * t + 1 := by omega
    set ω : K := (1 + r) / 2
    have hω : ω ^ 2 - ω - (t : K) = 0 := by
      simp only [ω]
      have : r ^ 2 = 4 * (t : K) + 1 := by rw [hr, hDt]; push_cast; ring
      field_simp
      linear_combination this
    have hωint : IsIntegral ℤ ω := by
      refine ⟨Polynomial.X ^ 2 - Polynomial.X - Polynomial.C t, by monicity!, ?_⟩
      rw [← Polynomial.aeval_def]
      simp only [map_sub, map_pow, Polynomial.aeval_X,
        eq_intCast, map_intCast]
      exact hω
    set ω' : 𝓞 K := ⟨ω, hωint⟩
    have hω' : ω' ^ 2 - ω' - (t : 𝓞 K) = 0 := by
      apply RingOfIntegers.ext; push_cast; exact hω
    have hsq := FiniteField.pow_card (Ideal.Quotient.mk 𝔭.asIdeal ω')
    rw [hcard] at hsq
    have ht0 : Ideal.Quotient.mk 𝔭.asIdeal (t : 𝓞 K) = 0 := by
      have := congrArg (Ideal.Quotient.mk 𝔭.asIdeal) hω'
      rw [map_sub, map_sub, map_pow, hsq, map_zero] at this
      linear_combination -this
    have h2t := (hmk t).mp ht0
    have h8 : discr K % 8 = 1 := by push_cast at h2t; omega
    split_ifs <;> omega
  · obtain ⟨m, hm, hpow⟩ := pow_half_eq_jacobiSym (F := 𝓞 K ⧸ 𝔭.asIdeal) hp2 hD4
    rw [hcard] at hm hpow
    set x := Ideal.Quotient.mk 𝔭.asIdeal r'
    have hx2 : x ^ 2 = ((discr K : ℤ) : 𝓞 K ⧸ 𝔭.asIdeal) := by
      rw [← map_pow, hr', map_intCast]
    have hx0 : x ≠ 0 := by
      intro h0
      rw [h0, zero_pow two_ne_zero, eq_comm, ← map_intCast (Ideal.Quotient.mk 𝔭.asIdeal)] at hx2
      exact hpD ((hmk _).mp hx2)
    have h1 : ((discr K : ℤ) : 𝓞 K ⧸ 𝔭.asIdeal) ^ m = 1 := by
      rw [← hx2, ← pow_mul]
      have := FiniteField.pow_card_sub_one_eq_one x hx0
      rwa [hcard, show p - 1 = 2 * m by omega] at this
    rw [h1] at hpow
    have hk : jacobiSym p (discr K).natAbs = kronecker (discr K) p := chiD_eq_kronecker hD4 hp
    rw [hk] at hpow
    rcases jacobiSym.trichotomy (discr K) p with h | h | h
    · rw [← kronecker_prime_of_ne_two hp hp2] at h
      rw [h] at hpow; simp at hpow
    · exact (kronecker_prime_of_ne_two hp hp2 _).trans h
    · rw [← kronecker_prime_of_ne_two hp hp2] at h
      rw [h] at hpow
      have h2 : ((2 : ℕ) : 𝓞 K ⧸ 𝔭.asIdeal) = 0 := by
        push_cast at hpow ⊢; linear_combination hpow
      rw [CharP.cast_eq_zero_iff (𝓞 K ⧸ 𝔭.asIdeal) p] at h2
      exact (hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)).elim

end Decomp

/-! ### The decomposition law -/

open Decomp in

/-- **The decomposition law in a quadratic field of odd discriminant** (PROVED). For a prime `p`,
exactly one of: `p` splits (two primes of norm `p`, unramified, `(D/p) = 1`); `p` is inert (one
prime of norm `p²`, unramified, `(D/p) = −1`); `p` ramifies (one prime of norm `p`, ramified,
`p ∣ D`), with `D = disc K` and `(D/p)` the Kronecker symbol. -/
theorem decomposition (hK2 : Module.finrank ℚ K = 2) (hodd : Odd (discr K)) {p : ℕ}
    (hp : p.Prime) :
    (∃ 𝔭 𝔮 : HeightOneSpectrum (𝓞 K), 𝔭 ≠ 𝔮 ∧ primesAbove K p = {𝔭, 𝔮} ∧
        Ideal.absNorm 𝔭.asIdeal = p ∧ Ideal.absNorm 𝔮.asIdeal = p ∧ UnramifiedOver 𝔭 p ∧
        UnramifiedOver 𝔮 p ∧ kronecker (discr K) p = 1) ∨
    (∃ 𝔭 : HeightOneSpectrum (𝓞 K), primesAbove K p = {𝔭} ∧ Ideal.absNorm 𝔭.asIdeal = p ^ 2 ∧
        UnramifiedOver 𝔭 p ∧ kronecker (discr K) p = -1) ∨
    (∃ 𝔭 : HeightOneSpectrum (𝓞 K), primesAbove K p = {𝔭} ∧ Ideal.absNorm 𝔭.asIdeal = p ∧
        ¬ UnramifiedOver 𝔭 p ∧ (p : ℤ) ∣ discr K) := by
  have hD4 := discr_mod_four_of_odd hK2 hodd
  rcases primesAbove_cases hK2 hp with
    ⟨𝔭, 𝔮, hne, hset, he𝔭, hf𝔭, he𝔮, hf𝔮⟩ | ⟨𝔭, hset, he, hf⟩ | ⟨𝔭, hset, he, hf⟩
  · have h𝔭 : 𝔭 ∈ primesAbove K p := by rw [hset]; simp
    have h𝔮 : 𝔮 ∈ primesAbove K p := by rw [hset]; simp
    have hpD : ¬ (p : ℤ) ∣ discr K := by
      rw [dvd_discr_iff hp, hset]
      rintro ⟨𝔯, h𝔯, h1⟩
      rcases h𝔯 with rfl | rfl
      · exact h1 he𝔭
      · exact h1 he𝔮
    have hN𝔭 : Ideal.absNorm 𝔭.asIdeal = p := by rw [absNorm_eq_pow hp h𝔭, hf𝔭, pow_one]
    exact Or.inl ⟨𝔭, 𝔮, hne, hset, hN𝔭, by rw [absNorm_eq_pow hp h𝔮, hf𝔮, pow_one],
      (unramifiedOver_iff hp h𝔭).mpr he𝔭, (unramifiedOver_iff hp h𝔮).mpr he𝔮,
      kronecker_eq_one_of_absNorm hK2 hodd hp h𝔭 hN𝔭 hpD⟩
  · have h𝔭 : 𝔭 ∈ primesAbove K p := by rw [hset]; simp
    have hpD : ¬ (p : ℤ) ∣ discr K := by
      rw [dvd_discr_iff hp, hset]
      rintro ⟨𝔯, h𝔯, h1⟩
      rw [Set.mem_singleton_iff] at h𝔯
      subst h𝔯
      exact h1 he
    refine Or.inr (Or.inl ⟨𝔭, hset, by rw [absNorm_eq_pow hp h𝔭, hf],
      (unramifiedOver_iff hp h𝔭).mpr he, ?_⟩)
    rcases kronecker_cases_of_not_dvd hD4 hp hpD with ⟨-, hsq⟩ | h
    · exfalso
      obtain ⟨𝔞, ha, 𝔟, hb, hab⟩ := two_primes_of_squareAt hK2 hp hsq
      rw [hset, Set.mem_singleton_iff] at ha hb
      exact hab (ha.trans hb.symm)
    · exact h
  · have h𝔭 : 𝔭 ∈ primesAbove K p := by rw [hset]; simp
    refine Or.inr (Or.inr ⟨𝔭, hset, by rw [absNorm_eq_pow hp h𝔭, hf, pow_one],
      fun h => by rw [unramifiedOver_iff hp h𝔭, he] at h; omega, ?_⟩)
    exact (dvd_discr_iff hp).mpr ⟨𝔭, h𝔭, by rw [he]; omega⟩

end ZInQ.Contrib.CloudB3RC53.GenusOdd

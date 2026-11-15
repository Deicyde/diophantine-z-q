import Base
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.ClassFields.RayClassField

/-! # Part R1: verbatim copy of `scratch/x6-glue/X6Glue.lean` lines 6587-6747 (x6-glue's copy of shimura-glue's
`parts/RayClassNew.lean`): the leaf `ShimuraGlue.Ray.RayClassCM` and what it depends on. The last theorem
of that section (`reciprocityCanonical_of_rayClass`) is omitted: its target is not in this import closure. -/

set_option linter.all false

noncomputable section

namespace ShimuraGlue.Ray

open TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields NumberField IsDedekindDomain
open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-- The modulus `3·𝒪_K` (no infinite part; `K` imaginary quadratic has no real places). -/
noncomputable def mod3 (K : Type) [Field K] [NumberField K] : Modulus K :=
  ⟨Ideal.span {3}, by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (show ((3 : ℕ) : 𝓞 K) ≠ 0 from Nat.cast_ne_zero.2 (by norm_num)), ∅⟩

/-- A prime of `𝒪_K` above `p ≥ 5` is outside the support of `3·𝒪_K`. -/
theorem not_mem_support_mod3 {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hpv : (p : 𝓞 K) ∈ v.asIdeal) : v ∉ (mod3 K).support := by
  rw [Modulus.mem_support_iff]
  intro hdvd
  have h3 : (3 : 𝓞 K) ∈ v.asIdeal := Ideal.le_of_dvd hdvd (Ideal.mem_span_singleton_self 3)
  have hcop : IsCoprime (3 : ℤ) p := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have : Nat.Coprime 3 p := (Nat.coprime_primes Nat.prime_three hp).2 (by omega)
    simpa [Int.gcd] using this
  obtain ⟨a, b, hab⟩ := hcop
  have h1 : (1 : 𝓞 K) ∈ v.asIdeal := by
    have := v.asIdeal.add_mem (v.asIdeal.mul_mem_left (a : 𝓞 K) h3)
      (v.asIdeal.mul_mem_left (b : 𝓞 K) hpv)
    have e : ((a : 𝓞 K) * 3 + (b : 𝓞 K) * (p : 𝓞 K)) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 K) hab
    rwa [e] at this
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

/-- **Glue: a subfield of `ℚ̄` embedding into the ray class field of conductor 3 of a number field `K`
unramified above every `p ≥ 5` is unramified above every `p ≥ 5`.** (Tau Ceti:
`IsAdmissibleModulus.isUnramifiedAway`; Mathlib: `Algebra.IsUnramifiedAt.comp`,
`NumberField.not_dvd_discr_iff_forall_mem`, `NumberField.discr_dvd_discr`.) -/
theorem unramifiedAbove5_of_embed (K : Type) [Field K] [NumberField K]
    (hK : ∀ p : ℕ, p.Prime → 5 ≤ p → ¬ (p : ℤ) ∣ discr K)
    (F : IntermediateField ℚ Qbar) (τ : F →+* rayClassField (mod3 K)) : UnramifiedAbove5 F := by
  let L := rayClassField (mod3 K)
  have hfd : FiniteDimensional ℚ F :=
    FiniteDimensional.of_injective τ.toRatAlgHom.toLinearMap τ.injective
  refine ⟨hfd, fun p hp h5 hdvd => ?_⟩
  letI : NumberField F := @NumberField.mk F _ _ hfd
  letI : Algebra F L := τ.toAlgebra
  have h1 : discr F ∣ discr L := NumberField.discr_dvd_discr F L
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have h2 : ¬ (p : ℤ) ∣ discr L := by
    rw [NumberField.not_dvd_discr_iff_forall_mem L (𝓞 L) hpZ]
    intro P hP hpP
    let Q := P.comap (algebraMap (𝓞 K) (𝓞 L))
    haveI : Q.IsPrime := Ideal.comap_isPrime _ _
    haveI : P.LiesOver Q := ⟨rfl⟩
    have hpQ : ((p : ℤ) : 𝓞 K) ∈ Q := by
      rw [Ideal.mem_comap, map_intCast]; exact hpP
    haveI : Algebra.IsUnramifiedAt ℤ Q :=
      (NumberField.not_dvd_discr_iff_forall_mem K (𝓞 K) hpZ).1 (hK p hp h5) Q inferInstance hpQ
    have hQ0 : Q ≠ ⊥ := by
      intro h0
      rw [h0, Ideal.mem_bot] at hpQ
      exact hp.ne_zero (by exact_mod_cast hpQ)
    let v : HeightOneSpectrum (𝓞 K) := ⟨Q, inferInstance, hQ0⟩
    have hpv : (p : 𝓞 K) ∈ v.asIdeal := by exact_mod_cast hpQ
    haveI : P.LiesOver v.asIdeal := ‹P.LiesOver Q›
    haveI : Algebra.IsUnramifiedAt (𝓞 K) P :=
      (isAdmissibleModulus_rayClassField (mod3 K)).isUnramifiedAway v
        (not_mem_support_mod3 v hp h5 hpv) P
    exact Algebra.IsUnramifiedAt.comp Q P
  exact h2 (dvd_trans hdvd h1)

instance instNeZero24 : NeZero ((24 : ℕ) : ℚ) := ⟨by norm_num⟩
instance instNeZero4 : NeZero ((4 : ℕ) : ℚ) := ⟨by norm_num⟩
instance instNeZero3 : NeZero ((3 : ℕ) : ℚ) := ⟨by norm_num⟩
instance instCyc24 : IsCyclotomicExtension {24} ℚ (CyclotomicField 24 ℚ) :=
  CyclotomicField.isCyclotomicExtension 24 ℚ
instance instCyc4 : IsCyclotomicExtension {4} ℚ (CyclotomicField 4 ℚ) :=
  CyclotomicField.isCyclotomicExtension 4 ℚ
instance instCyc3 : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) :=
  CyclotomicField.isCyclotomicExtension 3 ℚ

/-- A cyclotomic field `ℚ(ζ_m)` is unramified above every prime not dividing `m` (Tau Ceti). -/
theorem cyclotomic_unram (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} ℚ (CyclotomicField m ℚ)] {p : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m) :
    ¬ (p : ℤ) ∣ discr (CyclotomicField m ℚ) := by
  intro h
  rcases IsCyclotomicExtension.prime_dvd_natAbs_discr_or_dvd_of_dvd_natAbs_discr ℚ
      (CyclotomicField m ℚ) m hp (Int.natCast_dvd.1 h) with h' | h'
  · rw [NumberField.discr_rat] at h'; simp at h'; exact hp.one_lt.ne' h'
  · exact hpm h'

/-- `ℚ(i) = ℚ(ζ₄)`. -/
abbrev K4 : Type := CyclotomicField 4 ℚ
/-- `ℚ(ζ₃)`. -/
abbrev K3 : Type := CyclotomicField 3 ℚ

/-- `ζ₂₄`. -/
noncomputable abbrev z24 : CyclotomicField 24 ℚ := IsCyclotomicExtension.zeta 24 ℚ (CyclotomicField 24 ℚ)

/-- `√−6 = (2ζ₃ + 1)(ζ₈ + ζ₈⁷)` in `ℚ(ζ₂₄)`, with `ζ₃ = ζ₂₄⁸`, `ζ₈ = ζ₂₄³`. -/
noncomputable def s6 : CyclotomicField 24 ℚ := (2 * z24 ^ 8 + 1) * (z24 ^ 3 + z24 ^ 21)

theorem s6_sq : s6 ^ 2 = -6 := by
  have hz := IsCyclotomicExtension.zeta_spec 24 ℚ (CyclotomicField 24 ℚ)
  have h3 : IsPrimitiveRoot (z24 ^ 8) 3 := hz.pow_of_dvd (by norm_num) (by norm_num)
  have h8 : IsPrimitiveRoot (z24 ^ 3) 8 := hz.pow_of_dvd (by norm_num) (by norm_num)
  -- `ζ₃² + ζ₃ + 1 = 0`
  have e3 : (z24 ^ 8) ^ 2 + z24 ^ 8 + 1 = 0 := by
    have := h3.isRoot_cyclotomic (by norm_num)
    simpa [Polynomial.cyclotomic_three, Polynomial.eval_add, Polynomial.eval_pow] using this
  -- `ζ₈⁴ = −1`
  have e8 : (z24 ^ 3) ^ 4 = -1 := by
    have h2 : ((z24 ^ 3) ^ 4) ^ 2 = 1 := by rw [← pow_mul]; exact h8.pow_eq_one
    have hne : (z24 ^ 3) ^ 4 ≠ 1 := h8.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
    rcases sq_eq_one_iff.1 h2 with h | h
    · exact absurd h hne
    · exact h
  have e24 : z24 ^ 24 = 1 := hz.pow_eq_one
  simp only [s6]
  linear_combination (4 * (z24 ^ 3 + z24 ^ 21) ^ 2) * e3 -
    3 * (2 * ((z24 ^ 3) ^ 4 - 1) + (z24 ^ 3) ^ 2 * ((z24 ^ 3) ^ 8 - (z24 ^ 3) ^ 4 + 1)) * e8

/-- `ℚ(√−6) = ℚ(s6) ⊆ ℚ(ζ₂₄)`. -/
abbrev K24 : IntermediateField ℚ (CyclotomicField 24 ℚ) := IntermediateField.adjoin ℚ {s6}

theorem hK4 : ∀ p : ℕ, p.Prime → 5 ≤ p → ¬ (p : ℤ) ∣ discr K4 := fun p hp h5 =>
  cyclotomic_unram 4 hp (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)

theorem hK3 : ∀ p : ℕ, p.Prime → 5 ≤ p → ¬ (p : ℤ) ∣ discr K3 := fun p hp h5 =>
  cyclotomic_unram 3 hp (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)

theorem hK24 : ∀ p : ℕ, p.Prime → 5 ≤ p → ¬ (p : ℤ) ∣ discr K24 := by
  intro p hp h5 h
  have h24 : ¬ p ∣ 24 := by
    intro hd
    have h24' : (24 : ℕ) = 2 ^ 3 * 3 := by norm_num
    rw [h24'] at hd
    rcases (Nat.Prime.dvd_mul hp).1 hd with h2 | h3
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2); omega
    · have := Nat.le_of_dvd (by norm_num) h3; omega
  exact cyclotomic_unram 24 hp h24 (dvd_trans h (NumberField.discr_dvd_discr K24 _))

/-- **LEAF (Shimura's reciprocity at CM points, in ray-class form; a consequence).** Some fine witness
`(Y, Φ)` of the moduli clause lists (the canonical model `Y₃ = Sh_{K₃}`) has: for every `ℚ̄`-point `y`
whose object has CM by the maximal order of `k = ℚ(i)`, `ℚ(ζ₃)`, `ℚ(√−6)`, the residue field `ℚ(y) ⊆ ℚ̄`
embeds into the ray class field of `k` of conductor `3·𝒪_k` (Tau Ceti's `rayClassField`).

*Published statement*: Shimura reciprocity at CM points of the canonical model (Shimura, Ann. of Math. 85
(1967), Main Thm I; Deligne, Sém. Bourbaki 389 (1971), §3; Milne, *Introduction to Shimura varieties*
(2005), §12-13; locators UNVERIFIED): for a CM point `x = [h_k, g]` of `Sh_K`, `k(x)` is the class field of
`k` attached to `k^× k_∞^× · {s ∈ 𝔸_{k,f}^× : ι(s) ∈ gKg⁻¹}`. For `K = K₃` and an optimal embedding of the
maximal order (`HasCM*` means `End` contains `𝒪_k`, which is maximal), `ι(1 + 3𝒪̂_k) ⊆ g(1 + 3𝒪̂)g⁻¹` (at 2
and 3, where `B` ramifies, `𝒪_p` is the unique maximal order of the division algebra and `K₃` at 3 is
`1 + 3𝒪₃`), so this subgroup contains the ray subgroup of conductor 3 and
`k(x) ⊆` the ray class field of conductor 3; `ℚ(x) ⊆ k(x)`. *Form*: a **consequence** (the class field is
bounded by the ray class field, and only the embedding of `ℚ(x)` is kept). Lemma QP as for `R1fp`. -/
def RayClassCM : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpProps Y Φ ∧
    ∀ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar), Φ Qbar y = M3.mk P →
      (HasCM4 P.q → Nonempty (residueImage (X := Y.left) y.left →+* rayClassField (mod3 K4))) ∧
      (HasCM3 P.q → Nonempty (residueImage (X := Y.left) y.left →+* rayClassField (mod3 K3))) ∧
      (HasCM24 P.q → Nonempty (residueImage (X := Y.left) y.left →+* rayClassField (mod3 K24)))


end ShimuraGlue.Ray

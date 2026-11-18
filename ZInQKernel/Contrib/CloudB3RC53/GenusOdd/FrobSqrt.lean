import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.EulerJacobi
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Global.FrobeniusGeneration

/-!
# GenusOdd: the Frobenius at a prime of norm `q` acts on `√d` by `(q / |d|)` (PROVED)

`frob_smul_sqrt`: for number fields `L/K` with `L/K` Galois, `s ∈ 𝓞_L` with `s² = d`
(`d ≡ 1 mod 4`), and an arithmetic Frobenius `σ` at a prime `Q` of `𝓞_L` over a prime `v` of `𝓞_K`
with `2d ∉ v`: `σ s = (N v / |d|) s` (Euler's criterion in `𝓞_K / v`, `EulerJacobi.lean`).
-/

noncomputable section

open NumberField IsDedekindDomain

namespace ZInQ.Contrib.CloudB3RC53.GenusOdd

/-- The ring-level congruence argument (PROVED). -/
theorem eq_sign_mul_of_frob {A : Type*} [CommRing A] [IsDomain A] {Q : Ideal A} [Q.IsPrime]
    {s : A} {d : ℤ} (hs : s ^ 2 = (d : A)) {t : A} (ht : t ^ 2 = (d : A)) {m : ℕ}
    (hfrob : t - s ^ (2 * m + 1) ∈ Q) {ε : ℤ} (hε : (d : A) ^ m - (ε : A) ∈ Q)
    (hε2 : ε = 1 ∨ ε = -1) (h2d : ((2 * d : ℤ) : A) ∉ Q) : t = (ε : A) * s := by
  have hpow : s ^ (2 * m + 1) = s * (d : A) ^ m := by rw [pow_succ, pow_mul, hs, mul_comm]
  have h1 : t - (ε : A) * s ∈ Q := by
    have : t - (ε : A) * s = (t - s ^ (2 * m + 1)) + s * ((d : A) ^ m - (ε : A)) := by
      rw [hpow]; ring
    rw [this]; exact Q.add_mem hfrob (Q.mul_mem_left _ hε)
  have hts : t = s ∨ t = -s := by
    have : (t - s) * (t + s) = 0 := by linear_combination ht - hs
    rcases mul_eq_zero.mp this with h | h
    · left; linear_combination h
    · right; linear_combination h
  -- if `t = -ε s`, then `2 s ∈ Q`, hence `4 d ∈ Q`
  by_contra hne
  have h2s : (2 : A) * s ∈ Q := by
    rcases hts with h | h <;> rcases hε2 with he | he <;> rw [h, he] at h1 hne <;> push_cast at h1 hne
    · exact absurd (one_mul s).symm hne
    · rw [show (2 : A) * s = s - -1 * s by ring]; exact h1
    · rw [show (2 : A) * s = -(-s - 1 * s) by ring]; exact Q.neg_mem_iff.mpr h1
    · exact absurd (by ring) hne
  have h4d : ((2 : A) * s) * ((2 : A) * s) ∈ Q := Q.mul_mem_left _ h2s
  have : ((2 : A) * s) * ((2 : A) * s) = 2 * ((2 * d : ℤ) : A) := by
    rw [show ((2 : A) * s) * ((2 : A) * s) = 4 * s ^ 2 by ring, hs]; push_cast; ring
  rw [this] at h4d
  rcases Ideal.IsPrime.mem_or_mem ‹_› h4d with h2 | h2
  · apply h2d
    have : ((2 * d : ℤ) : A) = 2 * (d : A) := by push_cast; ring
    rw [this]; exact Q.mul_mem_right _ h2
  · exact h2d h2

/-- **The Frobenius on `√d`** (PROVED): an arithmetic Frobenius `σ` at a prime `Q` of `𝓞_L` over a
maximal ideal `v` of `𝓞_K` with `2d ∉ v` multiplies a square root `s ∈ 𝓞_L` of `d ≡ 1 (mod 4)` by
the Jacobi symbol `(N v / |d|)`. -/
theorem frob_smul_sqrt {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] {d : ℤ} (hd : d % 4 = 1) (s : 𝓞 L) (hs : s ^ 2 = (d : 𝓞 L)) (σ : L ≃ₐ[K] L)
    (Q : Ideal (𝓞 L)) [Q.IsPrime] (v : Ideal (𝓞 K)) [v.IsMaximal] [Q.LiesOver v]
    (h2d : ((2 * d : ℤ) : 𝓞 K) ∉ v) (hfrob : IsArithFrobAt (𝓞 K) σ Q) :
    σ • s = ((jacobiSym (Ideal.absNorm v) d.natAbs : ℤ) : 𝓞 L) * s := by
  have hv : v = Q.under (𝓞 K) := Ideal.LiesOver.over
  have hfin : Finite (𝓞 K ⧸ Q.under (𝓞 K)) := hfrob.finite_quotient
  rw [← hv] at hfin
  let _ : Field (𝓞 K ⧸ v) := Ideal.Quotient.field v
  let _ : Fintype (𝓞 K ⧸ v) := Fintype.ofFinite _
  obtain ⟨p, hchar⟩ := CharP.exists (𝓞 K ⧸ v)
  have hpp : p.Prime := CharP.char_is_prime (𝓞 K ⧸ v) p
  have : Fact p.Prime := ⟨hpp⟩
  have hmemv : ∀ x : 𝓞 K, Ideal.Quotient.mk v x = 0 ↔ x ∈ v := fun x => Ideal.Quotient.eq_zero_iff_mem
  have hp2 : p ≠ 2 := by
    rintro rfl
    apply h2d
    have h20 : ((2 : ℕ) : 𝓞 K ⧸ v) = 0 := CharP.cast_eq_zero (𝓞 K ⧸ v) 2
    rw [← hmemv, map_intCast]
    push_cast at h20 ⊢
    rw [h20, zero_mul]
  obtain ⟨m, hcard, heul⟩ := pow_half_eq_jacobiSym (F := 𝓞 K ⧸ v) hp2 hd
  have hnorm : Ideal.absNorm v = Fintype.card (𝓞 K ⧸ v) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  rw [← hnorm] at hcard heul
  set J := jacobiSym (Ideal.absNorm v) d.natAbs
  -- `d^m ≡ J (mod v)`, hence modulo `Q`
  have hdv : ((d : 𝓞 K) ^ m - (J : 𝓞 K)) ∈ v := by
    rw [← hmemv, map_sub, map_pow, map_intCast, map_intCast, heul, sub_self]
  have hε : ((d : 𝓞 L) ^ m - (J : 𝓞 L)) ∈ Q := by
    have : algebraMap (𝓞 K) (𝓞 L) ((d : 𝓞 K) ^ m - (J : 𝓞 K)) ∈ Q := by
      have : ((d : 𝓞 K) ^ m - (J : 𝓞 K)) ∈ Q.under (𝓞 K) := hv ▸ hdv
      exact this
    simpa using this
  have h2dQ : ((2 * d : ℤ) : 𝓞 L) ∉ Q := by
    intro h
    apply h2d
    rw [hv]
    show algebraMap (𝓞 K) (𝓞 L) ((2 * d : ℤ) : 𝓞 K) ∈ Q
    rw [map_intCast]; exact h
  -- `J = ±1`
  have hpd : ¬ (p : ℤ) ∣ d := by
    intro hdvd
    apply h2d
    rw [← hmemv, map_intCast]
    obtain ⟨e, he⟩ := hdvd
    rw [he]; push_cast
    rw [show ((p : 𝓞 K ⧸ v)) = 0 from CharP.cast_eq_zero _ p]; ring
  obtain ⟨f, -, hq⟩ := FiniteField.card (𝓞 K ⧸ v) p
  have hJ : J = 1 ∨ J = -1 := by
    apply jacobiSym.eq_one_or_neg_one
    rw [hnorm, hq]
    have hcop : Nat.Coprime p d.natAbs :=
      (Nat.Prime.coprime_iff_not_dvd hpp).mpr fun h => hpd (Int.natCast_dvd.mpr h)
    have := hcop.pow_left (f : ℕ)
    rw [Int.gcd_natCast_natCast]
    exact this
  -- the Frobenius congruence
  have hfrob' : σ • s - s ^ (2 * m + 1) ∈ Q := by
    have := hfrob s
    rw [← hv, Nat.card_eq_fintype_card, ← hnorm, hcard] at this
    exact this
  have hσd : σ • (d : 𝓞 L) = (d : 𝓞 L) :=
    map_intCast (MulSemiringAction.toRingHom (L ≃ₐ[K] L) (𝓞 L) σ) d
  have ht : (σ • s) ^ 2 = (d : 𝓞 L) := by rw [← smul_pow', hs, hσd]
  exact eq_sign_mul_of_frob hs ht hfrob' hε hJ h2dQ

end ZInQ.Contrib.CloudB3RC53.GenusOdd

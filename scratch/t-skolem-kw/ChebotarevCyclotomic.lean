import Mathlib

/-!
# t-skolem-kw: the leaf `ChebotarevExists` holds for cyclotomic fields (sanity check)

`PkgI6.ChebotarevExists` (T18, finite form) quantifies over all finite Galois `M/ℚ`.  Here it is
proved for every cyclotomic field `M` (`IsCyclotomicExtension {n} ℚ M`), from Mathlib's
Dirichlet theorem, the discriminant of `ℚ(ζ_n)`, `𝓞 = ℤ[ζ]` and Dedekind's discriminant
criterion.  This checks that the leaf, as formalized (Mathlib's `IsArithFrobAt`,
`Algebra.IsUnramifiedAt`, `Q.under ℤ = (p)`), is the intended statement on the abelian fields;
it is not the case the decomposition needs (C10 needs non-abelian `M`).
-/

open NumberField

namespace TSkolemKW.ChebCyc

/-- The body of `PkgI6.ChebotarevExists` for one field `M` (so `ChebotarevExists` is
`∀ M, ChebotarevAt M`). -/
def ChebotarevAt (M : Type) [Field M] [NumberField M] [IsGalois ℚ M] : Prop :=
  ∀ (S : Finset ℕ) (σ : M ≃ₐ[ℚ] M),
    ∃ p : ℕ, p.Prime ∧ p ∉ S ∧ ∃ Q : Ideal (𝓞 M), ∃ _ : Q.IsPrime,
      Q.under ℤ = Ideal.span {(p : ℤ)} ∧ Algebra.IsUnramifiedAt ℤ Q ∧ IsArithFrobAt ℤ σ Q

lemma card_quot (p : ℕ) [Fact p.Prime] : Nat.card (ℤ ⧸ Ideal.span {(p : ℤ)}) = p := by
  rw [Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]

theorem chebotarevAt_cyclotomic (n : ℕ) [NeZero n] (M : Type) [Field M] [NumberField M]
    [IsGalois ℚ M] [IsCyclotomicExtension {n} ℚ M] : ChebotarevAt M := by
  intro S σ
  set ζ := IsCyclotomicExtension.zeta n ℚ M
  have hζ : IsPrimitiveRoot ζ n := IsCyclotomicExtension.zeta_spec n ℚ M
  set a : (ZMod n)ˣ := hζ.autToPow ℚ σ
  have hσζ : σ ζ = ζ ^ (a : ZMod n).val := (hζ.autToPow_spec ℚ σ).symm
  -- Dirichlet: a prime `p ≡ a (mod n)` beyond `S` and `n`
  obtain ⟨p, hpN, hp, hpa⟩ := Nat.forall_exists_prime_gt_and_eq_mod (q := n) a.isUnit
    (S.sup id + n)
  have : Fact p.Prime := ⟨hp⟩
  have hpS : p ∉ S := by
    intro h
    have := Finset.le_sup (f := id) h
    simp only [id] at this
    omega
  have hpn : ¬ p ∣ n := by
    intro h
    have := Nat.le_of_dvd (NeZero.pos n) h
    omega
  -- a prime `Q` of `𝓞 M` over `p`
  obtain ⟨Q, -, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
    (Ideal.span {(p : ℤ)}) (⊥ : Ideal (𝓞 M)) (by
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_bot] at hx
      have : x = 0 := (algebraMap ℤ (𝓞 M)).injective_int (hx.trans (map_zero _).symm)
      rw [this]
      exact Ideal.zero_mem _)
  have hQp' : Q.under ℤ = Ideal.span {(p : ℤ)} := hQp
  refine ⟨p, hp, hpS, Q, hQ, hQp', ?_, ?_⟩
  · -- unramified: `p ∤ discr M`
    have hpd : ¬ (p : ℤ) ∣ discr M := by
      intro h
      have h1 : p ∣ (discr M).natAbs := Int.natAbs_dvd_natAbs.2 h |>.trans (by simp)
      rw [IsCyclotomicExtension.Rat.natAbs_discr n M] at h1
      have h2 : p ∣ n ^ Nat.totient n :=
        h1.trans (Nat.div_dvd_of_dvd (Nat.prod_primeFactors_pow_totient_ediv_dvd (NeZero.pos _)))
      exact hpn (hp.dvd_of_dvd_pow h2)
    have hun := (not_dvd_discr_iff_isUnramifiedIn M (𝓞 M)
      (Int.prime_iff_natAbs_prime.2 (by simpa using hp))).1 hpd
    exact hun Q hQ ⟨hQp'.symm⟩
  · -- Frobenius: `σ x ≡ x^p (mod Q)` on `ℤ[ζ] = 𝓞 M`
    intro x
    change σ • x - x ^ Nat.card (ℤ ⧸ Q.under ℤ) ∈ Q
    rw [hQp', card_quot]
    have hpQ : ((p : ℤ) : 𝓞 M) ∈ Q := by
      have : (p : ℤ) ∈ Q.under ℤ := by rw [hQp']; exact Ideal.mem_span_singleton_self _
      exact this
    have hx : x ∈ Algebra.adjoin ℤ {hζ.toInteger} := by
      rw [IsCyclotomicExtension.Rat.adjoin_singleton_eq_top hζ]
      trivial
    induction hx using Algebra.adjoin_induction with
    | mem y hy =>
      rw [Set.mem_singleton_iff] at hy
      subst hy
      have e : σ • hζ.toInteger = hζ.toInteger ^ p := by
        apply RingOfIntegers.ext
        change σ ζ = algebraMap (𝓞 M) M (hζ.toInteger ^ p)
        rw [hσζ, map_pow]
        change ζ ^ (a : ZMod n).val = ζ ^ p
        rw [← hpa, ZMod.val_natCast]
        conv_rhs => rw [← Nat.mod_add_div p n, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
      rw [e, sub_self]
      exact Q.zero_mem
    | algebraMap k =>
      have e : σ • (algebraMap ℤ (𝓞 M) k) = algebraMap ℤ (𝓞 M) k := by
        apply RingOfIntegers.ext
        change σ ((algebraMap ℤ (𝓞 M) k : 𝓞 M) : M) = _
        simp
      rw [e, ← map_pow, ← map_sub]
      have hk : (p : ℤ) ∣ k - k ^ p := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [ZMod.pow_card, sub_self]
      obtain ⟨c, hc⟩ := hk
      rw [hc, map_mul]
      exact Q.mul_mem_right _ hpQ
    | add y z _ _ hy hz =>
      obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp y z
      rw [smul_add, hr]
      have : σ • y + σ • z - (y ^ p + z ^ p + p * y * z * r) =
          (σ • y - y ^ p) + (σ • z - z ^ p) - ((p : ℤ) : 𝓞 M) * (y * z * r) := by
        push_cast
        ring
      rw [this]
      exact Q.sub_mem (Q.add_mem hy hz) (Q.mul_mem_right _ hpQ)
    | mul y z _ _ hy hz =>
      rw [smul_mul', mul_pow]
      have : σ • y * σ • z - y ^ p * z ^ p =
          (σ • y - y ^ p) * σ • z + y ^ p * (σ • z - z ^ p) := by ring
      rw [this]
      exact Q.add_mem (Q.mul_mem_right _ hy) (Q.mul_mem_left _ hz)

end TSkolemKW.ChebCyc

#print axioms TSkolemKW.ChebCyc.chebotarevAt_cyclotomic

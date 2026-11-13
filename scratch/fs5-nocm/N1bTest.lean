import ZInQKernel.HDecomp.QM.Leaves

namespace FS5NoCM

set_option maxRecDepth 100000 in
theorem check3 : ∀ a b c d : ZMod 9,
    a ^ 2 + a * c + c ^ 2 + 7 * (b ^ 2 + b * d + d ^ 2) = 0 →
      3 ∣ a.val ∧ 3 ∣ b.val ∧ 3 ∣ c.val ∧ 3 ∣ d.val := by decide

set_option maxRecDepth 100000 in
theorem check2 : ∀ a b c d : ZMod 4,
    a ^ 2 + a * c + c ^ 2 + 2 * (b ^ 2 + b * d + d ^ 2) = 0 →
      2 ∣ a.val ∧ 2 ∣ b.val ∧ 2 ∣ c.val ∧ 2 ∣ d.val := by decide

open LeafQM

/-- The reduced norm of `ofInt n`, as an integer quadratic form. -/
def Qf (n : Fin 4 → ℤ) : ℤ := n 0 ^ 2 + n 0 * n 2 + n 2 ^ 2 - 2 * (n 1 ^ 2 + n 1 * n 3 + n 3 ^ 2)

theorem nrd_ofInt (n : Fin 4 → ℤ) : ofInt n * star (ofInt n) = algebraMap ℚ B (Qf n : ℚ) := by
  ext <;> simp [ofInt, Qf, QuaternionAlgebra.algebraMap_eq] <;> ring

/-- `p² ∣ nrd(ofInt n)` forces `p ∣ n` for `p = 2, 3` (`𝒪_p` is the set of integral elements of
the ramified `B_p`; a finite check modulo `p²`). -/
theorem dvd_of_sq_dvd_Qf (p : ℕ) (hp : p = 2 ∨ p = 3) (n : Fin 4 → ℤ) (h : (p : ℤ) ^ 2 ∣ Qf n) :
    ∀ i, (p : ℤ) ∣ n i := by
  rcases hp with rfl | rfl
  · have h0 : ((Qf n : ℤ) : ZMod 4) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast h
    have e : ((n 0 : ℤ) : ZMod 4) ^ 2 + (n 0 : ZMod 4) * (n 2 : ZMod 4) + (n 2 : ZMod 4) ^ 2 +
        2 * ((n 1 : ZMod 4) ^ 2 + (n 1 : ZMod 4) * (n 3 : ZMod 4) + (n 3 : ZMod 4) ^ 2) = 0 := by
      have h4 : (4 : ZMod 4) = 0 := by decide
      rw [← h0]; simp only [Qf]; push_cast
      linear_combination (((n 1 : ZMod 4) ^ 2 + (n 1 : ZMod 4) * (n 3 : ZMod 4) +
        (n 3 : ZMod 4) ^ 2)) * h4
    obtain ⟨a, b, c, d⟩ := check2 _ _ _ _ e
    have key : ∀ m : ℤ, 2 ∣ ((m : ZMod 4)).val → (2 : ℤ) ∣ m := by
      intro m hm
      have hv : (((m : ZMod 4)).val : ℤ) = m % 4 := ZMod.val_intCast m
      have h2 : (2 : ℤ) ∣ m % 4 := by
        have := Int.natCast_dvd_natCast.mpr hm
        rwa [hv] at this
      omega
    intro i; fin_cases i
    · exact key _ a
    · exact key _ b
    · exact key _ c
    · exact key _ d
  · have h0 : ((Qf n : ℤ) : ZMod 9) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast h
    have e : ((n 0 : ℤ) : ZMod 9) ^ 2 + (n 0 : ZMod 9) * (n 2 : ZMod 9) + (n 2 : ZMod 9) ^ 2 +
        7 * ((n 1 : ZMod 9) ^ 2 + (n 1 : ZMod 9) * (n 3 : ZMod 9) + (n 3 : ZMod 9) ^ 2) = 0 := by
      have h9 : (9 : ZMod 9) = 0 := by decide
      rw [← h0]; simp only [Qf]; push_cast
      linear_combination (((n 1 : ZMod 9) ^ 2 + (n 1 : ZMod 9) * (n 3 : ZMod 9) +
        (n 3 : ZMod 9) ^ 2)) * h9
    obtain ⟨a, b, c, d⟩ := check3 _ _ _ _ e
    have key : ∀ m : ℤ, 3 ∣ ((m : ZMod 9)).val → (3 : ℤ) ∣ m := by
      intro m hm
      have hv : (((m : ZMod 9)).val : ℤ) = m % 9 := ZMod.val_intCast m
      have h2 : (3 : ℤ) ∣ m % 9 := by
        have := Int.natCast_dvd_natCast.mpr hm
        rwa [hv] at this
      omega
    intro i; fin_cases i
    · exact key _ a
    · exact key _ b
    · exact key _ c
    · exact key _ d

theorem ofInt_nsmul (p : ℕ) (w : Fin 4 → ℤ) : ofInt (fun i => (p : ℤ) * w i) = (p : ℚ) • ofInt w := by
  ext <;> simp [ofInt] <;> ring

theorem mul_star_comm (x : B) : star x * x = x * star x := by
  ext <;> simp <;> ring

/-- **Optimal embeddings have conductor prime to 6** (the algebra behind N1b). If `R ⊆ 𝒪_k` is
the preimage `φ⁻¹(𝒪)` of N5's maximal order under an embedding `φ : k → B` and has finite index,
then `p ∤ [𝒪_k : R]` for `p = 2, 3`: otherwise some `y ∈ 𝒪_k ∖ R` has `p y ∈ R`, so
`φ(p y) = ofInt v ∈ 𝒪`; `nrd φ(y) ∈ ℤ` (its minimal polynomial is that of `y`, integral), so
`p² ∣ nrd(ofInt v)`, hence `p ∣ v` (`dvd_of_sq_dvd_Qf`) and `φ(y) ∈ 𝒪`, i.e. `y ∈ R`. -/
theorem not_dvd_conductor_of_optimal {k : Type} [Field k] [NumberField k]
    (φ : k →ₐ[ℚ] B) (R : Subring k) (hR : R = O.comap φ.toRingHom)
    (hc0 : AV.conductor R ≠ 0) (p : ℕ) (hp : p = 2 ∨ p = 3) : ¬ p ∣ AV.conductor R := by
  intro hdvd
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  haveI : Fact p.Prime := ⟨hpp⟩
  set L := (integralClosure ℤ k).toSubring.toAddSubgroup with hL
  set H := R.toAddSubgroup.addSubgroupOf L with hH
  have hidx : H.index = AV.conductor R := rfl
  have hcard : Nat.card (↥L ⧸ H) = AV.conductor R := by rw [← AddSubgroup.index_eq_card, hidx]
  have hfin : Finite (↥L ⧸ H) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hc0)
  obtain ⟨g, hg⟩ := exists_prime_addOrderOf_dvd_card' (G := ↥L ⧸ H) p (by rw [hcard]; exact hdvd)
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective g
  have hyR : (y : k) ∉ R := by
    intro hy
    have h0 : ((y : ↥L) : ↥L ⧸ H) = 0 := (QuotientAddGroup.eq_zero_iff y).mpr hy
    rw [h0, addOrderOf_zero] at hg
    exact hpp.one_lt.ne hg
  have hpy : p • (y : k) ∈ R := by
    have h1 : p • ((y : ↥L) : ↥L ⧸ H) = 0 := by rw [← hg]; exact addOrderOf_nsmul_eq_zero _
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff] at h1
    exact h1
  have hyint : IsIntegral ℤ (y : k) := y.2
  have hynq : (y : k) ∉ Set.range (algebraMap ℚ k) := by
    rintro ⟨q, hq⟩
    have hqi : IsIntegral ℤ q :=
      (isIntegral_algHom_iff ((Algebra.ofId ℚ k).restrictScalars ℤ)
        (algebraMap ℚ k).injective).mp (by rw [← hq] at hyint; exact hyint)
    obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hqi
    apply hyR
    rw [← hq, ← hm]
    have : algebraMap ℚ k (algebraMap ℤ ℚ m) = (m : k) := by simp
    rw [this]; exact intCast_mem R m
  set x : B := φ (y : k) with hx
  have hxint : IsIntegral ℤ x := hyint.map (φ.restrictScalars ℤ)
  have hxnq : x ∉ Set.range (algebraMap ℚ B) := by
    rintro ⟨q, hq⟩
    apply hynq
    refine ⟨q, φ.injective ?_⟩
    change φ (algebraMap ℚ k q) = φ y
    rw [AlgHom.commutes]; exact hq
  -- the minimal polynomial of `x` is `X² − t X + n`, with integer coefficients
  set t : ℚ := 2 * x.re with ht
  set n : ℚ := (x * star x).re with hn
  have hxx : x * star x = algebraMap ℚ B n := by
    rw [hn, QuaternionAlgebra.mul_star_eq_coe]; rfl
  have hsum : x + star x = algebraMap ℚ B t := by
    rw [QuaternionAlgebra.self_add_star', ht]; simp
  have hP : Polynomial.aeval x (Polynomial.C (1 : ℚ) * Polynomial.X ^ 2 +
      Polynomial.C (-t) * Polynomial.X + Polynomial.C n) = 0 := by
    simp only [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow, Polynomial.aeval_X,
      map_one, one_mul, map_neg]
    rw [← hsum, ← hxx, ← mul_star_comm]
    noncomm_ring
  have hPm : (Polynomial.C (1 : ℚ) * Polynomial.X ^ 2 + Polynomial.C (-t) * Polynomial.X +
      Polynomial.C n).Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff_quadratic one_ne_zero]
  have hPd : (Polynomial.C (1 : ℚ) * Polynomial.X ^ 2 + Polynomial.C (-t) * Polynomial.X +
      Polynomial.C n).natDegree = 2 := Polynomial.natDegree_quadratic one_ne_zero
  have hxintQ : IsIntegral ℚ x := hxint.tower_top
  have hmin : minpoly ℚ x = Polynomial.C (1 : ℚ) * Polynomial.X ^ 2 +
      Polynomial.C (-t) * Polynomial.X + Polynomial.C n := by
    refine (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hxintQ) hPm
      (minpoly.dvd ℚ x hP) ?_).symm
    rw [hPd]
    exact (minpoly.two_le_natDegree_iff hxintQ).mpr hxnq
  have hmin' : minpoly ℚ x = (minpoly ℤ (y : k)).map (algebraMap ℤ ℚ) := by
    rw [hx, minpoly.algHom_eq φ φ.injective]
    exact minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hyint
  obtain ⟨N, hN⟩ : ∃ N : ℤ, (N : ℚ) = n := by
    refine ⟨(minpoly ℤ (y : k)).coeff 0, ?_⟩
    have := congrArg (fun P : Polynomial ℚ => P.coeff 0) (hmin.symm.trans hmin')
    simp only [Polynomial.coeff_map, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C] at this
    simpa using this.symm
  -- `φ(p y) = p x ∈ 𝒪`, so `p² ∣ nrd`, so `x ∈ 𝒪`
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hpp.ne_zero
  have hz : (p : ℚ) • x ∈ O := by
    have h1 : p • (y : k) ∈ O.comap φ.toRingHom := hR ▸ hpy
    have h2 : φ (p • (y : k)) ∈ O := h1
    rwa [map_nsmul, ← Nat.cast_smul_eq_nsmul ℚ] at h2
  obtain ⟨v, hv⟩ := hz
  have hQ : (Qf v : ℚ) = (p : ℚ) ^ 2 * N := by
    have h1 := nrd_ofInt v
    rw [← hv, star_smul, smul_mul_smul_comm, hxx, Algebra.smul_def, ← map_mul] at h1
    rw [hN, ← (algebraMap ℚ B).injective h1, star_trivial]; ring
  have hQ' : (p : ℤ) ^ 2 ∣ Qf v := ⟨N, by exact_mod_cast hQ⟩
  choose w hw using dvd_of_sq_dvd_Qf p hp v hQ'
  have hvw : v = fun i => (p : ℤ) * w i := funext hw
  have hxw : x = ofInt w := by
    apply smul_right_injective B hp0
    simp only
    rw [hv, hvw, ofInt_nsmul]
  apply hyR
  rw [hR]
  exact ⟨w, hxw⟩

/-- **N1b′ (leaf; Shimura's description of CM points on `X₀(6,1)`).** If `End_𝒪(A) ≅ R` for an order
`R` of an imaginary quadratic `k`, then `R` is the preimage `φ⁻¹(𝒪)` of N5's maximal order under
some `ℚ`-embedding `φ : k → B`.
*Published statement*: for `(A, ι)` over `ℂ` with CM, `A = ℂ²/𝒪 v_τ` and `End_𝒪(A) ≅ φ_τ(k) ∩ 𝒪`,
where `φ_τ : k → B` is the embedding whose image fixes `τ ∈ ℍ` (Shimura, Ann. of Math. 85 (1967);
Jordan, thesis (Harvard 1981) §3; González–Rotger, J. Math. Soc. Japan 58 (2006) §5; locators
UNVERIFIED); in characteristic 0 the same holds over `ℚ̄`. Transport to the given `k ⊇ R`: an
isomorphism `R ≅ φ_τ(k) ∩ 𝒪` extends to the fraction fields `k ≅ k_τ` (`R` has rank 2), and the
composite embedding pulls `𝒪` back to `R`. A consequence of the published statement (up to
replacing `B` by `B^op ≅ B`, which preserves `𝒪`). -/
def CMOptimalEmbedding : Prop :=
  ∀ (P : AV.QMPair AV.Qbar) (k : Type) [Field k] [NumberField k] [NumberField.IsTotallyComplex k],
    Module.finrank ℚ k = 2 → ∀ R : Subring k, R ≤ (integralClosure ℤ k).toSubring →
      AV.conductor R ≠ 0 → Nonempty (AV.com P.q ≃+* R) →
        ∃ φ : k →ₐ[ℚ] B, R = O.comap φ.toRingHom

/-- `CMConductorCoprime6` text (verbatim copy for the test). -/
def CMConductorCoprime6' : Prop :=
  ∀ (P : AV.QMPair AV.Qbar) (k : Type) [Field k] [NumberField k] [NumberField.IsTotallyComplex k],
    Module.finrank ℚ k = 2 → ∀ R : Subring k, R ≤ (integralClosure ℤ k).toSubring →
      AV.conductor R ≠ 0 → Nonempty (AV.com P.q ≃+* R) → Nat.Coprime (AV.conductor R) 6

theorem cmConductorCoprime6_of (h : CMOptimalEmbedding) : CMConductorCoprime6' := by
  intro P k _ _ _ hk2 R hR hc0 he
  obtain ⟨φ, hφ⟩ := h P k hk2 R hR hc0 he
  have h2 := not_dvd_conductor_of_optimal φ R hφ hc0 2 (Or.inl rfl)
  have h3 := not_dvd_conductor_of_optimal φ R hφ hc0 3 (Or.inr rfl)
  rw [show (6 : ℕ) = 2 * 3 from rfl, Nat.coprime_mul_iff_right]
  exact ⟨(Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2)),
    (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3))⟩

end FS5NoCM

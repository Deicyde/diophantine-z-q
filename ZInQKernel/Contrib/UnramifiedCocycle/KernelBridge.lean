import ZInQKernel.Contrib.UnramifiedCocycle.ContractedPrimeArithmetic

/-!
# Kernel comparison for the actual global field action

The finite local container, its integer embedding, and its contracted prime
are constructed, not abstract model inputs.  The Frobenius exponent belongs
to the same actual residue action used on every integer element.  This is the
arithmetic comparison needed by the already proved cyclic cochain consumer.
-/

namespace ZInQ.Contrib.UnramifiedCocycle

open GlueDescent.B2Q NumberField IsLocalRing
open ZInQ.Contrib.LocalSquareRoot
open scoped Pointwise

local instance (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩
attribute [local instance] Ideal.Quotient.field

/-- A genuine Frobenius root-action exponent is divisible by the specified
cyclic degree if that primitive level root is fixed. -/
theorem frobeniusExponent_dvd_of_fixed_root
    (p : Nat.Primes) (n : ℕ) [NeZero n] {F : Type*} [Field F]
    (τ : F ≃+* F) {ζ : F} (hζ : IsPrimitiveRoot ζ (unramifiedLevel p n)) (r : ℕ)
    (hfrob : τ ζ = ζ ^ ((p : ℕ) ^ r)) (hfix : τ ζ = ζ) : n ∣ r := by
  have hpow : ζ ^ ((p : ℕ) ^ r) = ζ := hfrob.symm.trans hfix
  have hge : 1 ≤ (p : ℕ) ^ r := Nat.one_le_pow _ _ p.2.pos
  have hroot : ζ ^ ((p : ℕ) ^ r - 1) = 1 := by
    apply mul_right_cancel₀ (hζ.ne_zero (NeZero.ne (unramifiedLevel p n)))
    rw [← pow_succ, Nat.sub_add_cancel hge, one_mul]
    exact hpow
  have hdiv : unramifiedLevel p n ∣ (p : ℕ) ^ r - 1 := hζ.dvd_of_pow_eq_one _ hroot
  have hzero : (((p : ℕ) ^ r - 1 : ℕ) : ZMod (unramifiedLevel p n)) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
  rw [Nat.cast_sub hge, Nat.cast_pow, Nat.cast_one, sub_eq_zero] at hzero
  have hu : frobeniusUnit p n ^ r = 1 := by
    apply Units.ext
    exact hzero
  rw [← frobeniusUnit_order p n]
  exact orderOf_dvd_of_pow_eq_one hu

/-- Identity cyclic coordinate means identity on the ORIGINAL global root character. -/
theorem rootCharacter_one_of_quotient_one (p : Nat.Primes) (n : ℕ) [NeZero n]
    (g : GQp p) (hg : localFrobeniusQuotient p n g = 1) :
    cyc (unramifiedLevel p n) (resp p g) = 1 := by
  change localRootCharacter p (unramifiedLevel p n) g = 1
  have h := localFrobeniusQuotient_character p n g
  simpa [hg] using h.symm

/-- The same global root is fixed by the original `resp` action, including level one. -/
theorem global_primitive_fixed_of_character_one {m : ℕ} [NeZero m]
    (σ : GQ) {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ m)
    (hσ : cyc m σ = 1) : act σ ζ = ζ := by
  have hunit : hζ.autToPow ℚ (act σ) = 1 :=
    (cyc_eq_autToPow hζ σ).symm.trans hσ
  calc
    act σ ζ = ζ ^ (hζ.autToPow ℚ (act σ) : ZMod m).val :=
      (hζ.autToPow_spec ℚ (act σ)).symm
    _ = ζ := by
      rw [hunit, Units.val_one, ZMod.val_one_eq_one_mod, hζ.eq_orderOf, pow_mod_orderOf, pow_one]

/-- Finite residue fields are fixed by Frobenius exponents divisible by their
ACTUAL residue degree.  Exponent zero is included. -/
theorem finiteField_frobenius_multiple
    {K : Type*} [Field K] [Finite K] (p f r : ℕ) (hp : 0 < p)
    (hcard : Nat.card K = p ^ f) (hfr : f ∣ r) (x : K) : x ^ (p ^ r) = x := by
  by_cases hx : x = 0
  · subst hx
    simp only [zero_pow (pow_pos hp r).ne']
  have hroot := finiteField_pow_level_eq_one p f r (by omega) hcard hfr x hx
  have hge : 1 ≤ p ^ r := Nat.one_le_pow _ _ hp
  calc
    x ^ (p ^ r) = x ^ (p ^ r - 1 + 1) := by rw [Nat.sub_add_cancel hge]
    _ = x ^ (p ^ r - 1) * x := pow_succ _ _
    _ = x := by rw [hroot, one_mul]

/-- The actual root-character quotient kills precisely enough of the actual
local field action for any positive level degree divisible by `[L:ℚ]`. -/
theorem localRestriction_one_of_quotient_one
    (p : Nat.Primes) (L : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ L] [IsGalois ℚ L] (n : ℕ) [NeZero n]
    (hdegree : Module.finrank ℚ L ∣ n) (hu : UnramifiedAt L p)
    (g : GQp p) (hg : localFrobeniusQuotient p n g = 1) : localRestriction L p g = 1 := by
  let M := localContainer p L n
  let S := integralClosure ℤ_[p] M
  let : IsFractionRing S M := integralClosure.isFractionRing_of_finite_extension ℚ_[p] M
  have : Module.Finite ℤ_[p] S := IsIntegralClosure.finite ℤ_[p] ℚ_[p] M S
  have hinj : Function.Injective (algebraMap ℤ_[p] M) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[p] ℚ_[p] M]
    exact (algebraMap ℚ_[p] M).injective.comp (IsFractionRing.injective ℤ_[p] ℚ_[p])
  let : FaithfulSMul ℤ_[p] S := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b h
    apply hinj
    rw [IsScalarTower.algebraMap_apply ℤ_[p] S M, h, ← IsScalarTower.algebraMap_apply]
  obtain ⟨Q, hQmax, hQover⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := S) (maximalIdeal ℤ_[p])
  let : Q.IsMaximal := hQmax
  let : Q.LiesOver (maximalIdeal ℤ_[p]) := hQover
  let P := contractedPrime p L n Q
  let σ := localRestriction L p g
  let τ := (localAct p g).restrictNormal M
  obtain ⟨r, hr, hroots⟩ := exists_residue_and_root_frobenius p M Q τ
  let N := unramifiedLevel p n
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (AlgebraicClosure ℚ) N
  have hη : IsPrimitiveRoot (localClosureEmbedding p ζ) N :=
    hζ.map_of_injective (localClosureEmbedding p).injective
  let η : M := ⟨localClosureEmbedding p ζ,
    root_mem_container p L n _ hη.pow_eq_one⟩
  have hηM : IsPrimitiveRoot η N :=
    IsPrimitiveRoot.of_map_of_injective (f := M.val) hη Subtype.val_injective
  have hχ : cyc N (resp p g) = 1 := rootCharacter_one_of_quotient_one p n g hg
  have hζfix : act (resp p g) ζ = ζ := global_primitive_fixed_of_character_one (resp p g) hζ hχ
  have hηfix : τ η = η := by
    apply Subtype.val_injective
    have h1 := AlgEquiv.restrictNormal_commutes (localAct p g) M η
    have h2 := localClosureEmbedding_intertwines p g ζ
    exact h1.trans (h2.trans (congrArg (localClosureEmbedding p) hζfix))
  have hcop : ¬ (p : ℕ) ∣ N := (Nat.Prime.coprime_iff_not_dvd p.2).mp
    (GlueSqrtDisj.coprime_pow_sub_one p.2.two_le (NeZero.pos n))
  have hnr : n ∣ r := frobeniusExponent_dvd_of_fixed_root p n τ.toRingEquiv hηM r
    (hroots N hcop η hηM.pow_eq_one) hηfix
  have hfr : P.inertiaDeg ℤ ∣ r :=
    (contractedResidueDegree_dvd p L n Q hu).trans (hdegree.trans hnr)
  let F := contractedResidueMap p L n Q
  let K := 𝓞 L ⧸ P
  have hfrob : ∀ x : 𝓞 L, F (σ • x) = F x ^ ((p : ℕ) ^ r) := by
    intro x
    change Ideal.Quotient.mk Q (integerEmbedding p L n (σ • x)) = _
    rw [← integerEmbedding_intertwines p L n g x]
    exact hr (integerEmbedding p L n x)
  have hfixed : ∀ x : 𝓞 L, F x ^ ((p : ℕ) ^ r) = F x := by
    intro x
    have hx := finiteField_frobenius_multiple (p : ℕ) (P.inertiaDeg ℤ) r p.2.pos
      (contractedResidueField_card p L n Q) hfr (Ideal.Quotient.mk P x)
    have hmk : F.kerLift (Ideal.Quotient.mk P x) = F x := rfl
    calc
      F x ^ ((p : ℕ) ^ r) = F.kerLift (Ideal.Quotient.mk P x) ^ ((p : ℕ) ^ r) :=
        congrArg (fun z => z ^ ((p : ℕ) ^ r)) hmk.symm
      _ = F.kerLift (Ideal.Quotient.mk P x ^ ((p : ℕ) ^ r)) :=
        (map_pow F.kerLift _ _).symm
      _ = F.kerLift (Ideal.Quotient.mk P x) := congrArg F.kerLift hx
      _ = F x := hmk
  have hinertia : σ ∈ P.inertia Gal(L/ℚ) := by
    apply Ideal.mem_inertia.mpr
    intro x
    change F (σ • x - x) = 0
    rw [map_sub, hfrob x, hfixed x, sub_self]
  rw [contractedPrime_inertia_eq_bot p L n Q hu] at hinertia
  exact hinertia

end ZInQ.Contrib.UnramifiedCocycle

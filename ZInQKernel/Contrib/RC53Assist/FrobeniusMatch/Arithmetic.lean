import ZInQKernel.Contrib.RC53Assist.InnerLimitArith.ArithLabel
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Frobenius.Restriction

/-!
# Compatible arithmetic labels

The arithmetic Frobenius at a rational prime acts on residue fields by that prime.
Its square acts by the cardinality of the residue field of an inert quadratic prime.
Prime transitivity, the decomposition embedding, and unramified uniqueness identify
its restriction with the Frobenius of the arithmetic label, up to conjugation.

Continuity of the character supplies finite normal character fields at every
coefficient precision. Finite Chebotarev on the enlarged stage fields, with kernel
representatives fixing these fields, produces the character condition. The resulting
constructors assume neither the Frobenius match nor the character condition.
-/

set_option maxHeartbeats 600000
set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.FrobeniusMatch

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Manuscript.RC.PrintsArith (GalQ Qbar)
open ZInQ.Manuscript.RC.KummerMaps (tateConjQ tateConjQ_mul_self)
open ZInQ.Contrib.ChebFD.C10 (Zbar)
open ZInQ.Contrib.RC53Assist.InnerLimitArith
open scoped Pointwise WeierstrassCurve PowerSeries.WithPiTopology

/-- The congruence defining a rational arithmetic Frobenius is the ring-of-integers
arithmetic-Frobenius condition. -/
theorem rational_isArithFrobAt (g : GalQ) (p : ℕ) [Fact p.Prime]
    (P : Ideal Zbar) (hP : P.under ℤ = Ideal.span {(p : ℤ)})
    (hF : ∀ x y : Zbar, (y : Qbar) = g (x : Qbar) - (x : Qbar) ^ p → y ∈ P) :
    IsArithFrobAt ℤ g P := by
  intro x
  rw [hP, ZInQ.Contrib.ChebFD.C10.card_quot]
  apply hF x
  rw [AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow]
  rfl

variable {K : Type} [Field K] [NumberField K]

/-- The map on rings of integers induced by the identification of algebraic closures. -/
def integersEquiv (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar) :
    𝓞 (AlgebraicClosure K) ≃+* Zbar :=
  RingOfIntegers.mapRingEquiv e.toRingEquiv

/-- The square of the rational Frobenius is an arithmetic Frobenius over the inert
quadratic prime at the compatible prime of the algebraic closure. No unramifiedness
of the entire algebraic closure is asserted or needed. -/
theorem galKOfQ_sq_isArithFrobAt
    (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar) (g : GalQ) (p : ℕ) [Fact p.Prime]
    (P : Ideal Zbar) [P.IsPrime]
    (hP : P.under ℤ = Ideal.span {(p : ℤ)})
    (hF : ∀ x y : Zbar, (y : Qbar) = g (x : Qbar) - (x : Qbar) ^ p → y ∈ P)
    (hgK : ∀ x : K, (g * g) (e (algebraMap K (AlgebraicClosure K) x)) =
      e (algebraMap K (AlgebraicClosure K) x))
    (q : HeightOneSpectrum (𝓞 K))
    (hPq : (P.comap (integersEquiv e)).under (𝓞 K) = q.asIdeal)
    (hcard : Nat.card (𝓞 K ⧸ q.asIdeal) = p ^ 2) :
    IsArithFrobAt (𝓞 K) (galKOfQ e (g * g) hgK)
      (P.comap (integersEquiv e)) := by
  have hF' := rational_isArithFrobAt g p P hP hF
  intro x
  change galKOfQ e (g * g) hgK • x -
    x ^ Nat.card (𝓞 K ⧸ (P.comap (integersEquiv e)).under (𝓞 K)) ∈
      P.comap (integersEquiv e)
  rw [hPq, hcard, Ideal.mem_comap, map_sub, map_pow]
  have he : integersEquiv e (galKOfQ e (g * g) hgK • x) =
      (g * g) • integersEquiv e x := by
    apply RingOfIntegers.ext
    change e (galKOfQ e (g * g) hgK (x : AlgebraicClosure K)) =
      (g * g) (e (x : AlgebraicClosure K))
    rw [galKOfQ_apply, AlgEquiv.apply_symm_apply]
  rw [he, ← Ideal.Quotient.eq, map_pow]
  simpa only [hP, ZInQ.Contrib.ChebFD.C10.card_quot, pow_two] using
    hF'.mk_pow_smul 2 (integersEquiv e x)

/-- For valuation integers, the maximal ideal is characterized by strict valuation
less than one. -/
theorem valuationInteger_mem_maximalIdeal_iff
    {k : Type} [Field k] {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation k Γ) (x : v.integer) :
    x ∈ IsLocalRing.maximalIdeal v.integer ↔ v (x : k) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    (Valuation.integer.integers v).isUnit_iff_valuation_eq_one]
  change v (x : k) ≠ 1 ↔ v (x : k) < 1
  have hx : v (x : k) ≤ 1 := x.property
  simp only [lt_iff_le_and_ne, hx, true_and]

/-- A Frobenius lift acts by the residue-cardinality power modulo the maximal ideal
of an algebraic closure equipped with the extended valuation. -/
theorem localFrobenius_congruence
    {k : Type} [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    [ValuativeRel (AlgebraicClosure k)] [ValuativeExtension k (AlgebraicClosure k)]
    (φ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)
    (hφ : TauCeti.IsArithFrobeniusLift k φ)
    (y : AlgebraicClosure k) (hy : ValuativeRel.valuation (AlgebraicClosure k) y ≤ 1) :
    ValuativeRel.valuation (AlgebraicClosure k)
      (φ y - y ^ Nat.card (IsLocalRing.ResidueField (ValuativeRel.valuation k).integer)) < 1 := by
  let L := (FiniteGaloisIntermediateField.adjoin k {y}).toIntermediateField
  have : FiniteDimensional k L := inferInstance
  have : IsGalois k L := inferInstance
  let := TauCeti.finiteIntermediateFieldValuativeRel k (AlgebraicClosure k) L
  let := TauCeti.finiteIntermediateFieldTopology k (AlgebraicClosure k) L
  have := TauCeti.finiteIntermediateField_isNonarchimedeanLocalField k (AlgebraicClosure k) L
  have := TauCeti.finiteIntermediateField_valuativeExtension k (AlgebraicClosure k) L
  have : ValuativeExtension L (AlgebraicClosure k) := L.valuativeExtension
  have hyL : y ∈ L := FiniteGaloisIntermediateField.subset_adjoin k {y} (by simp)
  let yL : L := ⟨y, hyL⟩
  have hyv : ValuativeRel.valuation L yL ≤ 1 :=
    (Valuation.HasExtension.val_map_le_one_iff (ValuativeRel.valuation L)
      (ValuativeRel.valuation (AlgebraicClosure k)) yL).mp hy
  let yO : (ValuativeRel.valuation L).integer := ⟨yL, hyv⟩
  have hres := hφ.restrictNormal_smul_residueField_eq_pow L (IsLocalRing.residue _ yO)
  have hd : (φ.restrictNormal L • yO -
      yO ^ Nat.card (IsLocalRing.ResidueField (ValuativeRel.valuation k).integer)) ∈
      IsLocalRing.maximalIdeal (ValuativeRel.valuation L).integer := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow,
      IsLocalRing.ResidueField.residue_smul, hres, sub_self]
  have hv := (valuationInteger_mem_maximalIdeal_iff (ValuativeRel.valuation L) _).mp hd
  have hv' := (Valuation.HasExtension.val_map_lt_one_iff (ValuativeRel.valuation L)
    (ValuativeRel.valuation (AlgebraicClosure k)) _).mpr hv
  have hyO : algebraMap L (AlgebraicClosure k) (yO : L) = y := rfl
  simpa only [AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow,
    AlgEquiv.coe_smul_integerRing, map_sub, map_pow, AlgEquiv.restrictNormal_commutes,
    hyO] using hv'

/-- The absolute Galois group has the ring of integers of the base as its fixed ring
inside the algebraic integers. -/
theorem absoluteIntegers_invariant :
    Algebra.IsInvariant (𝓞 K) (𝓞 (AlgebraicClosure K))
      (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) := by
  refine ⟨fun x hx => ?_⟩
  have hfixed : ∀ g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      g (x : AlgebraicClosure K) = (x : AlgebraicClosure K) := by
    intro g
    exact congrArg Subtype.val (hx g)
  obtain ⟨a, ha⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed
    (x : AlgebraicClosure K)).mpr hfixed
  have hai : IsIntegral ℤ a := by
    have hxint : IsIntegral ℤ (algebraMap K (AlgebraicClosure K) a) := ha.symm ▸ x.2
    exact isIntegral_algebraMap_iff.mp hxint
  refine ⟨⟨a, hai⟩, ?_⟩
  apply RingOfIntegers.ext
  exact ha

/-- Any two primes of the algebraic integers above the same prime of the number
field are conjugate by an automorphism fixing the number field. -/
theorem absolute_primes_conjugate
    (P Q : Ideal (𝓞 (AlgebraicClosure K))) [P.IsPrime] [Q.IsPrime]
    (hPQ : P.under (𝓞 K) = Q.under (𝓞 K)) :
    ∃ g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, Q = g • P := by
  let : TopologicalSpace (𝓞 (AlgebraicClosure K)) := ⊥
  let : DiscreteTopology (𝓞 (AlgebraicClosure K)) := ⟨rfl⟩
  let : ContinuousSMul (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
      (𝓞 (AlgebraicClosure K)) := by
    apply continuousSMul_iff_stabilizer_isOpen.mpr
    intro x
    let F := IntermediateField.adjoin K {(x : AlgebraicClosure K)}
    have : FiniteDimensional K F :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
    apply Subgroup.isOpen_mono (H₁ := F.fixingSubgroup) _ F.fixingSubgroup_isOpen
    intro g hg
    change g • x = x
    apply RingOfIntegers.ext
    exact hg ⟨x, IntermediateField.mem_adjoin_simple_self K _⟩
  let := absoluteIntegers_invariant (K := K)
  exact Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (G :=
    AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) P Q hPQ

section LocalPrime

local instance localClosureValuativeRel (q : HeightOneSpectrum (𝓞 K)) :
    ValuativeRel (AlgebraicClosure (q.adicCompletion K)) :=
  TauCeti.algebraicExtensionValuativeRel (q.adicCompletion K)
    (AlgebraicClosure (q.adicCompletion K))

local instance localClosureValuativeExtension (q : HeightOneSpectrum (𝓞 K)) :
    ValuativeExtension (q.adicCompletion K) (AlgebraicClosure (q.adicCompletion K)) :=
  TauCeti.algebraicExtension_valuativeExtension _ _

/-- The decomposition embedding sends algebraic integers to valuation integers. -/
def localIntegersMap (q : HeightOneSpectrum (𝓞 K)) :
    𝓞 (AlgebraicClosure K) →+*
      (ValuativeRel.valuation (AlgebraicClosure (q.adicCompletion K))).integer :=
  RingHom.codRestrict ((decompLift K q).comp (algebraMap (𝓞 (AlgebraicClosure K))
    (AlgebraicClosure K))) _ fun x => by
      let : Algebra ℤ (AlgebraicClosure (q.adicCompletion K)) :=
        Ring.toIntAlgebra (AlgebraicClosure (q.adicCompletion K))
      rw [Valuation.mem_integer_iff]
      have hi : IsIntegral ℤ (decompLift K q (x : AlgebraicClosure K)) := by
        have hmem := (RingOfIntegers.mapRingHom (decompLift K q) x).property
        rw [mem_integralClosure_iff] at hmem
        exact hmem
      have hi' : IsIntegral
          (ValuativeRel.valuation (AlgebraicClosure (q.adicCompletion K))).integer
          (decompLift K q (x : AlgebraicClosure K)) := hi.tower_top
      exact (Valuation.integer.integers
        (ValuativeRel.valuation (AlgebraicClosure (q.adicCompletion K)))).isIntegral_iff_v_le_one.mp hi'

/-- The prime of the algebraic integers specified by the decomposition embedding. -/
def localPrime (q : HeightOneSpectrum (𝓞 K)) : Ideal (𝓞 (AlgebraicClosure K)) :=
  (IsLocalRing.maximalIdeal (ValuativeRel.valuation
    (AlgebraicClosure (q.adicCompletion K))).integer).comap (localIntegersMap q)

instance localPrime_isPrime (q : HeightOneSpectrum (𝓞 K)) : (localPrime q).IsPrime :=
  Ideal.comap_isPrime _ _

/-- Membership in the decomposition prime is the strict valuation inequality. -/
theorem mem_localPrime (q : HeightOneSpectrum (𝓞 K)) (x : 𝓞 (AlgebraicClosure K)) :
    x ∈ localPrime q ↔ ValuativeRel.valuation (AlgebraicClosure (q.adicCompletion K))
      (decompLift K q (x : AlgebraicClosure K)) < 1 := by
  rw [localPrime, Ideal.mem_comap, valuationInteger_mem_maximalIdeal_iff]
  rfl

/-- The decomposition prime contracts to the specified prime of the number field. -/
theorem localPrime_under (q : HeightOneSpectrum (𝓞 K)) :
    (localPrime q).under (𝓞 K) = q.asIdeal := by
  ext x
  rw [Ideal.mem_under, mem_localPrime]
  change ValuativeRel.valuation (AlgebraicClosure (q.adicCompletion K))
    (decompLift K q (algebraMap K (AlgebraicClosure K) (x : K))) < 1 ↔ x ∈ q.asIdeal
  rw [decompLift_algebraMap, IsScalarTower.algebraMap_apply K (q.adicCompletion K)
    (AlgebraicClosure (q.adicCompletion K)),
    Valuation.HasExtension.val_map_lt_one_iff (ValuativeRel.valuation (q.adicCompletion K))]
  rw [(ValuativeRel.isEquiv (ValuativeRel.valuation (q.adicCompletion K))
    (Valued.v : Valuation (q.adicCompletion K) (WithZero (Multiplicative ℤ)))).lt_one_iff_lt_one]
  rw [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation', Algebra.algebraMap_self_apply]
  exact q.valuation_lt_one_iff_mem x

set_option backward.isDefEq.respectTransparency.types false in
/-- A local arithmetic Frobenius maps to an arithmetic Frobenius at the prime
specified by the decomposition embedding. -/
theorem decompMap_isArithFrobAt (q : HeightOneSpectrum (𝓞 K))
    (φ : Gloc K q) (hφ : TauCeti.IsArithFrobeniusLift (q.adicCompletion K) φ) :
    IsArithFrobAt (𝓞 K) (@id (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
      (decompMap K q φ)) (localPrime q) := by
  intro x
  change (@id (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (decompMap K q φ)) • x -
      x ^ Nat.card (𝓞 K ⧸ (localPrime q).under (𝓞 K)) ∈ localPrime q
  rw [localPrime_under, mem_localPrime]
  change ValuativeRel.valuation (AlgebraicClosure (q.adicCompletion K))
    (decompLift K q (algebraMap (𝓞 (AlgebraicClosure K)) (AlgebraicClosure K)
      ((@id (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (decompMap K q φ)) • x -
        x ^ Nat.card (𝓞 K ⧸ q.asIdeal)))) < 1
  rw [map_sub, map_pow, algebraMap_smul_eq_apply, map_sub, map_pow, decompLift_decompMap]
  have hcard : Nat.card (𝓞 K ⧸ q.asIdeal) =
      Nat.card (IsLocalRing.ResidueField (ValuativeRel.valuation (q.adicCompletion K)).integer) :=
    Nat.card_congr (q.residueFieldEquivAdicCompletion (K := K)).toEquiv
  rw [hcard]
  exact localFrobenius_congruence φ hφ _ (localIntegersMap q x).property

end LocalPrime

open ZInQ.Contrib.CloudB3RC53.RankCounts (unramifiedOutside IsUnramifiedOutside resAbs)

/-- Arithmetic Frobenius elements at one compatible prime have equal restrictions to
an extension unramified at the underlying prime. -/
theorem samePrime_restriction_eq (S : Set (HeightOneSpectrum (𝓞 K)))
    (q : HeightOneSpectrum (𝓞 K)) (hq : q ∉ S)
    (P : Ideal (𝓞 (AlgebraicClosure K))) [P.IsPrime]
    (hPq : P.under (𝓞 K) = q.asIdeal)
    (σ τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (hσ : IsArithFrobAt (𝓞 K) σ P) (hτ : IsArithFrobAt (𝓞 K) τ P) :
    resAbsCont K S σ = resAbsCont K S τ := by
  have hfix : unramifiedOutside K S ≤ IntermediateField.fixedField (Subgroup.zpowers (τ⁻¹ * σ)) := by
    unfold unramifiedOutside
    refine iSup₂_le fun L hL => ?_
    have : FiniteDimensional K L := hL.1
    have : Normal K L := hL.2.1
    let Q := P.under (𝓞 L)
    have : Q.IsPrime := Ideal.IsPrime.under _ P
    have hQq : Q.under (𝓞 K) = q.asIdeal := by
      rw [Ideal.under_under]
      exact hPq
    have : Q.LiesOver q.asIdeal := ⟨hQq.symm⟩
    have : Algebra.IsUnramifiedAt (𝓞 K) Q :=
      (ZInQ.Contrib.CloudB3RC53.RankCounts.KummerS.isUnramifiedOutside_iff K S L).1
        hL.2.2 q hq Q inferInstance inferInstance
    have he : σ.restrictNormal L = τ.restrictNormal L :=
      NumberField.isArithFrobAt_eq_of_isUnramifiedAt
        (hσ.restrictNormal (M := L)) (hτ.restrictNormal (M := L))
    rw [IntermediateField.le_iff_le, Subgroup.zpowers_le, IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    have hsy : σ y = τ y := by
      have h := congrArg (fun f : L ≃ₐ[K] L => (f ⟨y, hy⟩ : AlgebraicClosure K)) he
      simpa only [AlgEquiv.restrictNormal_apply] using h
    change τ.symm (σ y) = y
    rw [hsy, AlgEquiv.symm_apply_apply]
  rw [IntermediateField.le_iff_le, Subgroup.zpowers_le, IntermediateField.mem_fixingSubgroup_iff] at hfix
  change resAbs K S σ = resAbs K S τ
  apply AlgEquiv.ext
  intro y
  apply Subtype.ext
  rw [ZInQ.Contrib.CloudB3RC53.RankCounts.resAbs_apply_coe,
    ZInQ.Contrib.CloudB3RC53.RankCounts.resAbs_apply_coe]
  have h := hfix y y.2
  change τ.symm (σ y) = y at h
  exact τ.symm_apply_eq.mp h

/-- The Frobenius of a moving label is conjugate to any arithmetic Frobenius at a
prime above its stage prime. The conjugator fixes the number field. -/
theorem label_frobenius_conjugate (S : Set (HeightOneSpectrum (𝓞 K)))
    (L : MovingLabel K S) (i : ℕ)
    (P : Ideal (𝓞 (AlgebraicClosure K))) [P.IsPrime]
    (hPq : P.under (𝓞 K) = (L.q i).asIdeal)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (hσ : IsArithFrobAt (𝓞 K) σ P) :
    ∃ g : GKS K S, L.frob i = g * resAbsCont K S σ * g⁻¹ := by
  obtain ⟨g, hg⟩ := absolute_primes_conjugate P (localPrime (L.q i))
    (hPq.trans (localPrime_under (L.q i)).symm)
  have hσ' : IsArithFrobAt (𝓞 K) (g * σ * g⁻¹) (localPrime (L.q i)) :=
    hg ▸ hσ.conj g
  have hφ : TauCeti.IsArithFrobeniusLift ((L.q i).adicCompletion K) (L.φ i) := by
    change urRes K (L.q i) (L.φ i) = _
    rw [L.hφ, ZInQ.Contrib.CloudB3RC53.UnramifiedComplex.frobElt_eUr]
  have hlocal := decompMap_isArithFrobAt (L.q i) (L.φ i) hφ
  refine ⟨resAbsCont K S g, ?_⟩
  calc
    L.frob i = locMap K S (L.q i) (L.φ i) := by
      rw [L.hψ, L.hφ]
      rfl
    _ = resAbsCont K S (decompMap K (L.q i) (L.φ i)) := rfl
    _ = resAbsCont K S (g * σ * g⁻¹) :=
      samePrime_restriction_eq S (L.q i) (L.notMem i) _ (localPrime_under (L.q i))
        _ _ hlocal hσ'
    _ = resAbsCont K S g * resAbsCont K S σ * (resAbsCont K S g)⁻¹ := by
      change resAbs K S (g * σ * g⁻¹) = resAbs K S g * resAbs K S σ * (resAbs K S g)⁻¹
      rw [map_mul, map_mul, map_inv]

/-- A prime of a quadratic number field with residue cardinality `p²` is the
principal ideal generated by `p`. -/
theorem inert_prime_eq_span (hdegree : Module.finrank ℚ K = 2) (p : ℕ) (hp : p.Prime)
    (q : HeightOneSpectrum (𝓞 K)) (habove : (p : 𝓞 K) ∈ q.asIdeal)
    (hcard : Nat.card (𝓞 K ⧸ q.asIdeal) = p ^ 2) :
    q.asIdeal = Ideal.span {(p : 𝓞 K)} := by
  have hnorm : Ideal.absNorm q.asIdeal = p ^ 2 := by
    simpa only [Ideal.absNorm_apply, Submodule.cardQuot_apply] using hcard
  have hspan : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ 2 := by
    rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, hdegree]
  obtain ⟨J, hJ⟩ := (Ideal.dvd_span_singleton.mpr habove :
    q.asIdeal ∣ Ideal.span {(p : 𝓞 K)})
  have hJone : Ideal.absNorm J = 1 := by
    have hmul := congrArg Ideal.absNorm hJ
    rw [hspan, map_mul, hnorm] at hmul
    exact (Nat.eq_of_mul_eq_mul_left (Nat.pow_pos hp.pos)
      (by simpa using hmul)).symm
  rw [hJ, Ideal.absNorm_eq_one_iff.mp hJone, Ideal.mul_top]

/-- Every prime of the algebraic integers above `p` contracts to the inert
quadratic prime above `p`, including the prime witnessing a rational Frobenius. -/
theorem inert_prime_contraction (hdegree : Module.finrank ℚ K = 2)
    (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar) (p : ℕ) (hp : p.Prime)
    (q : HeightOneSpectrum (𝓞 K)) (habove : (p : 𝓞 K) ∈ q.asIdeal)
    (hcard : Nat.card (𝓞 K ⧸ q.asIdeal) = p ^ 2)
    (P : Ideal Zbar) [P.IsPrime] (hP : P.under ℤ = Ideal.span {(p : ℤ)}) :
    (P.comap (integersEquiv e)).under (𝓞 K) = q.asIdeal := by
  let Q := (P.comap (integersEquiv e)).under (𝓞 K)
  have : Q.IsPrime := Ideal.IsPrime.under _ _
  have hqspan := inert_prime_eq_span hdegree p hp q habove hcard
  have hpP : (p : Zbar) ∈ P := ZInQ.Contrib.ChebFD.HSyn.natCast_mem P p hP
  have hpQ : (p : 𝓞 K) ∈ Q := by
    change integersEquiv e (algebraMap (𝓞 K) (𝓞 (AlgebraicClosure K)) (p : 𝓞 K)) ∈ P
    simpa only [map_natCast] using hpP
  have hle : q.asIdeal ≤ Q := by
    rw [hqspan, Ideal.span_le]
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact hpQ
  exact (q.isPrime.isMaximal q.ne_bot).eq_of_le Ideal.IsPrime.ne_top' hle |>.symm

/-- The Frobenius match of an arithmetic label follows from the genuine rational
Frobenius elements, the incidence of the primes, and inertness in the quadratic
number field. Neither a conjugacy witness nor a local-global Frobenius equality
is an input. -/
theorem frobeniusMatchesLabel_of_inert
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {S : Set (HeightOneSpectrum (𝓞 K))} [HasFullTwoTorsion K S (E⁄K)]
    (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)
    (C : ZInQ.Manuscript.RC.CoefModules.ActualConj K S)
    {h : ℕ → GalQ} {F : ℕ → IntermediateField ℚ Qbar} {excl : ℕ → Finset ℕ}
    (D : DerivativePrimes E (tateConjQ e C) h F excl)
    (hK : ∀ i (x : K), (D.frob i * D.frob i)
      (e (algebraMap K (AlgebraicClosure K) x)) = e (algebraMap K (AlgebraicClosure K) x))
    (L : MovingLabel K S) (hdegree : Module.finrank ℚ K = 2)
    (habove : ∀ i, (D.ell i : 𝓞 K) ∈ (L.q i).asIdeal)
    (hinert : ∀ i, Nat.card (𝓞 K ⧸ (L.q i).asIdeal) = D.ell i ^ 2) :
    FrobeniusMatchesLabel E e C D hK L := by
  intro i
  obtain ⟨P, hP, hPZ, hF⟩ := D.isFrob i
  have : P.IsPrime := hP
  have : Fact (D.ell i).Prime := ⟨D.prime i⟩
  have hPq := inert_prime_contraction hdegree e (D.ell i) (D.prime i) (L.q i)
    (habove i) (hinert i) P hPZ
  have hs := galKOfQ_sq_isArithFrobAt e (D.frob i) (D.ell i) P hPZ hF (hK i)
    (L.q i) hPq (hinert i)
  exact label_frobenius_conjugate S L i _ hPq _ hs

section CharacterSelection

open ZInQ.Manuscript.RC.Uniform (Lambda)

variable (S : Set (HeightOneSpectrum (𝓞 K)))
    (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)
    (α : GKS K S →* Lambdaˣ) [IsContChar α]

/-- A finite normal rational extension contains the number field and detects the
character at any prescribed coefficient precision. -/
theorem exists_characterField (i : ℕ) :
    ∃ M : IntermediateField ℚ Qbar,
      FiniteDimensional ℚ M ∧ Normal ℚ M ∧
      (∀ x : K, e (algebraMap K (AlgebraicClosure K) x) ∈ M) ∧
      (∀ (g : GalQ)
        (hg : ∀ x : K, g (e (algebraMap K (AlgebraicClosure K) x)) =
          e (algebraMap K (AlgebraicClosure K) x)),
        (∀ x ∈ M, g x = x) →
          ((α (gksOfQ S e g hg) : Lambdaˣ) : Lambda) - 1 ∈ lamIdeal i) := by
  have hc : Continuous (fun g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K =>
      resAbsCont K S g) := (resAbsCont K S).continuous
  have hn : {g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K |
      ((α (resAbsCont K S g) : Lambdaˣ) : Lambda) - 1 ∈ lamIdeal i} ∈
      nhds (1 : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :=
    (hc.tendsto' 1 1 (map_one (resAbsCont K S))) (eventually_sub_one_mem α i)
  obtain ⟨B, hB, hker⟩ := (krullTopology_mem_nhds_one_iff K (AlgebraicClosure K) _).mp hn
  have : FiniteDimensional K B := hB
  have : FiniteDimensional ℚ B := Module.Finite.trans K B
  have : FiniteDimensional ℚ (B.restrictScalars ℚ) :=
    inferInstanceAs (FiniteDimensional ℚ B)
  let A : IntermediateField ℚ Qbar := (B.restrictScalars ℚ).map e.toAlgHom
  have : FiniteDimensional ℚ A := LinearEquiv.finiteDimensional
    (IntermediateField.equivMap (B.restrictScalars ℚ) e.toAlgHom).toLinearEquiv
  let M := IntermediateField.normalClosure ℚ A Qbar
  refine ⟨M, normalClosure.is_finiteDimensional ℚ A Qbar, normalClosure.normal ℚ A Qbar, ?_, ?_⟩
  · intro x
    apply A.le_normalClosure
    exact ⟨algebraMap K (AlgebraicClosure K) x, B.algebraMap_mem x, rfl⟩
  · intro g hg hfix
    apply hker
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [galKOfQ_apply]
    have hxm : e x ∈ M := A.le_normalClosure ⟨x, hx, rfl⟩
    rw [hfix (e x) hxm, AlgEquiv.symm_apply_apply]

/-- A finite normal extension detecting the character at stage `i`. -/
def characterField (i : ℕ) : IntermediateField ℚ Qbar :=
  (exists_characterField S e α i).choose

instance characterField_finite (i : ℕ) : FiniteDimensional ℚ (characterField S e α i) :=
  (exists_characterField S e α i).choose_spec.1

instance characterField_normal (i : ℕ) : Normal ℚ (characterField S e α i) :=
  (exists_characterField S e α i).choose_spec.2.1

/-- The finite character field includes the original number field. -/
theorem characterField_containsK (i : ℕ) (x : K) :
    e (algebraMap K (AlgebraicClosure K) x) ∈ characterField S e α i :=
  (exists_characterField S e α i).choose_spec.2.2.1 x

/-- Fixing the finite character field forces the stage character to be trivial. -/
theorem characterField_trivial (i : ℕ) (g : GalQ)
    (hg : ∀ x : K, g (e (algebraMap K (AlgebraicClosure K) x)) =
      e (algebraMap K (AlgebraicClosure K) x))
    (hfix : ∀ x ∈ characterField S e α i, g x = x) :
    ((α (gksOfQ S e g hg) : Lambdaˣ) : Lambda) - 1 ∈ lamIdeal i :=
  (exists_characterField S e α i).choose_spec.2.2.2 g hg hfix

variable (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (C : ZInQ.Manuscript.RC.CoefModules.ActualConj K S)
    (h : ℕ → GalQ) (F : ℕ → IntermediateField ℚ Qbar)
    [∀ i, FiniteDimensional ℚ (F i)] (excl : ℕ → Finset ℕ)

/-- Chebotarev on the enlarged stage fields, retaining both the original stage
information and the finite character precision. -/
def enlargedDerivativePrimes :
    DerivativePrimes E (tateConjQ e C) h (fun i => F i ⊔ characterField S e α i) excl := by
  have : ∀ i, FiniteDimensional ℚ ↥(F i ⊔ characterField S e α i) := fun i => inferInstance
  exact Classical.choice (exists_derivativePrimes E (tateConjQ e C) h
    (fun i => F i ⊔ characterField S e α i) excl)

/-- The selected derivative primes viewed on the original stage fields. -/
def selectedDerivativePrimes : DerivativePrimes E (tateConjQ e C) h F excl where
  ell := (enlargedDerivativePrimes S e α E C h F excl).ell
  prime := (enlargedDerivativePrimes S e α E C h F excl).prime
  odd := (enlargedDerivativePrimes S e α E C h F excl).odd
  avoid := (enlargedDerivativePrimes S e α E C h F excl).avoid
  frob := (enlargedDerivativePrimes S e α E C h F excl).frob
  isFrob := (enlargedDerivativePrimes S e α E C h F excl).isFrob
  agree i x hx := (enlargedDerivativePrimes S e α E C h F excl).agree i x
    (le_sup_left (a := F i) (b := characterField S e α i) hx)
  tate := (enlargedDerivativePrimes S e α E C h F excl).tate

/-- The selected Frobenius elements agree with the representatives on the finite
character fields, not merely on the original stage fields. -/
theorem selectedDerivativePrimes_agree_characterField (i : ℕ) (x : Qbar)
    (hx : x ∈ characterField S e α i) :
    (selectedDerivativePrimes S e α E C h F excl).frob i x = (tateConjQ e C * h i) x :=
  (enlargedDerivativePrimes S e α E C h F excl).agree i x
    (le_sup_right (a := F i) (b := characterField S e α i) hx)

/-- If the kernel representatives fix the finite character fields, the squares of
the selected rational Frobenius elements fix those fields. This follows from the
involution property of the actual conjugation and the finite Chebotarev agreement. -/
theorem selectedDerivativePrimes_sq_fixes_characterField
    (hkernel : ∀ i, ∀ x ∈ characterField S e α i, h i x = x)
    (i : ℕ) (x : Qbar) (hx : x ∈ characterField S e α i) :
    ((selectedDerivativePrimes S e α E C h F excl).frob i *
      (selectedDerivativePrimes S e α E C h F excl).frob i) x = x := by
  let M := characterField S e α i
  let Fr := (selectedDerivativePrimes S e α E C h F excl).frob i
  let τ := tateConjQ e C
  have hr : Fr.restrictNormal M = τ.restrictNormal M := by
    apply AlgEquiv.ext
    intro y
    apply Subtype.ext
    rw [AlgEquiv.restrictNormal_apply, AlgEquiv.restrictNormal_apply]
    rw [selectedDerivativePrimes_agree_characterField S e α E C h F excl i y y.2]
    change τ (h i y) = τ y
    rw [hkernel i y y.2]
  have hs : (Fr * Fr).restrictNormal M = 1 := by
    change (AlgEquiv.restrictNormalHom M) (Fr * Fr) = 1
    rw [map_mul]
    change Fr.restrictNormal M * Fr.restrictNormal M = 1
    rw [hr]
    change (AlgEquiv.restrictNormalHom M) τ * (AlgEquiv.restrictNormalHom M) τ = 1
    rw [← map_mul]
    change (AlgEquiv.restrictNormalHom M) (tateConjQ e C * tateConjQ e C) = 1
    rw [tateConjQ_mul_self, map_one]
  have hx' := congrArg (fun f : M ≃ₐ[ℚ] M => (f ⟨x, hx⟩ : Qbar)) hs
  simpa only [AlgEquiv.restrictNormal_apply, AlgEquiv.one_apply] using hx'

/-- The selected squares fix the number field, as a consequence of the enlarged
Chebotarev selection. -/
theorem selectedDerivativePrimes_fixesK
    (hkernel : ∀ i, ∀ x ∈ characterField S e α i, h i x = x) :
    ∀ i (x : K), ((selectedDerivativePrimes S e α E C h F excl).frob i *
      (selectedDerivativePrimes S e α E C h F excl).frob i)
        (e (algebraMap K (AlgebraicClosure K) x)) = e (algebraMap K (AlgebraicClosure K) x) :=
  fun i x => selectedDerivativePrimes_sq_fixes_characterField S e α E C h F excl hkernel i
    (e (algebraMap K (AlgebraicClosure K) x)) (characterField_containsK S e α i x)

/-- The selected derivative primes satisfy the character constraint. The
constraint is proved from the continuous character and finite field agreement. -/
theorem selectedDerivativePrimes_character
    (hkernel : ∀ i, ∀ x ∈ characterField S e α i, h i x = x) (i : ℕ) :
    ((α (ratSqFrob E e C (selectedDerivativePrimes S e α E C h F excl)
      (selectedDerivativePrimes_fixesK S e α E C h F excl hkernel) i) : Lambdaˣ) : Lambda) - 1 ∈
      lamIdeal i :=
  characterField_trivial S e α i _
    (selectedDerivativePrimes_fixesK S e α E C h F excl hkernel i)
    (selectedDerivativePrimes_sq_fixes_characterField S e α E C h F excl hkernel i)

/-- Finite Chebotarev supplies derivative primes satisfying the character
constraint for compatible kernel representatives. The constraint itself is not
an input. -/
theorem exists_derivativePrimes_with_character
    (hkernel : ∀ i, ∀ x ∈ characterField S e α i, h i x = x) :
    ∃ D : DerivativePrimes E (tateConjQ e C) h F excl,
      ∃ hK : ∀ i (x : K), (D.frob i * D.frob i)
        (e (algebraMap K (AlgebraicClosure K) x)) = e (algebraMap K (AlgebraicClosure K) x),
      ∀ i, ((α (ratSqFrob E e C D hK i) : Lambdaˣ) : Lambda) - 1 ∈ lamIdeal i :=
  ⟨selectedDerivativePrimes S e α E C h F excl,
    selectedDerivativePrimes_fixesK S e α E C h F excl hkernel,
    selectedDerivativePrimes_character S e α E C h F excl hkernel⟩

/-- In particular, identity kernel representatives always have derivative primes
with the character constraint, for every continuous character. -/
theorem exists_derivativePrimes_with_character_one :
    ∃ D : DerivativePrimes E (tateConjQ e C) (fun _ => 1) F excl,
      ∃ hK : ∀ i (x : K), (D.frob i * D.frob i)
        (e (algebraMap K (AlgebraicClosure K) x)) = e (algebraMap K (AlgebraicClosure K) x),
      ∀ i, ((α (ratSqFrob E e C D hK i) : Lambdaˣ) : Lambda) - 1 ∈ lamIdeal i :=
  exists_derivativePrimes_with_character S e α E C (fun _ => 1) F excl (fun _ _ _ => rfl)

/-- The actual finite-stage kernel on the rational absolute Galois group: it fixes
the Tate precision and the finite character field. -/
def derivativeKernel (i : ℕ) : Subgroup GalQ :=
  (ZInQ.Manuscript.RC.GlueSweep.Tate.torsField E i ⊔ characterField S e α i).fixingSubgroup

omit [E.IsElliptic] in
/-- A finite-stage kernel representative fixes the character field. -/
theorem derivativeKernel_fixes_characterField (i : ℕ) (g : derivativeKernel S e α E i)
    (x : Qbar) (hx : x ∈ characterField S e α i) : (g : GalQ) x = x :=
  g.property ⟨x, le_sup_right (a := ZInQ.Manuscript.RC.GlueSweep.Tate.torsField E i)
    (b := characterField S e α i) hx⟩

omit [E.IsElliptic] in
/-- A finite-stage kernel representative fixes the required two-power torsion field. -/
theorem derivativeKernel_fixes_torsField (i : ℕ) (g : derivativeKernel S e α E i)
    (x : Qbar) (hx : x ∈ ZInQ.Manuscript.RC.GlueSweep.Tate.torsField E i) : (g : GalQ) x = x :=
  g.property ⟨x, le_sup_left (a := ZInQ.Manuscript.RC.GlueSweep.Tate.torsField E i)
    (b := characterField S e α i) hx⟩

variable [HasFullTwoTorsion K S (E⁄K)]

/-- A compatible arithmetic label constructed from actual primes and compatible
finite-kernel representatives. Its Frobenius match, character condition, and
fixing of the number field are proved, not supplied as inputs. -/
def compatibleArithmeticLabelFromSelection
    (hkernel : ∀ i, ∀ x ∈ characterField S e α i, h i x = x)
    (hh : ∀ i, ∀ x ∈ ZInQ.Manuscript.RC.GlueSweep.Tate.torsField E i, h i x = x)
    (q : ℕ → HeightOneSpectrum (𝓞 K)) (hq : ∀ i, q i ∉ S)
    (hdegree : Module.finrank ℚ K = 2)
    (habove : ∀ i, ((selectedDerivativePrimes S e α E C h F excl).ell i : 𝓞 K) ∈ (q i).asIdeal)
    (hinert : ∀ i, Nat.card (𝓞 K ⧸ (q i).asIdeal) =
      (selectedDerivativePrimes S e α E C h F excl).ell i ^ 2) :
    CompatibleArithmeticLabel E K S α where
  e := e
  C := C
  h := h
  F := F
  excl := excl
  primes := selectedDerivativePrimes S e α E C h F excl
  hh := hh
  hK := selectedDerivativePrimes_fixesK S e α E C h F excl hkernel
  label := MovingLabel.ofPrimes q hq
  above := habove
  inert := hinert
  frobMatch := frobeniusMatchesLabel_of_inert E e C
    (selectedDerivativePrimes S e α E C h F excl)
    (selectedDerivativePrimes_fixesK S e α E C h F excl hkernel)
    (MovingLabel.ofPrimes q hq) hdegree habove hinert
  character := selectedDerivativePrimes_character S e α E C h F excl hkernel

/-- A compatible arithmetic label from actual finite-stage kernel elements.
All properties of the representatives needed by the construction follow from
their membership in the explicitly defined arithmetic kernel. -/
def compatibleArithmeticLabelFromKernel
    (H : ∀ i, derivativeKernel S e α E i)
    (q : ℕ → HeightOneSpectrum (𝓞 K)) (hq : ∀ i, q i ∉ S)
    (hdegree : Module.finrank ℚ K = 2)
    (habove : ∀ i, ((selectedDerivativePrimes S e α E C (fun i => H i) F excl).ell i : 𝓞 K) ∈
      (q i).asIdeal)
    (hinert : ∀ i, Nat.card (𝓞 K ⧸ (q i).asIdeal) =
      (selectedDerivativePrimes S e α E C (fun i => H i) F excl).ell i ^ 2) :
    CompatibleArithmeticLabel E K S α :=
  compatibleArithmeticLabelFromSelection S e α E C (fun i => H i) F excl
    (fun i x hx => derivativeKernel_fixes_characterField S e α E i (H i) x hx)
    (fun i x hx => derivativeKernel_fixes_torsField S e α E i (H i) x hx)
    q hq hdegree habove hinert

/-- A compatible arithmetic label for identity kernel representatives. There is
no character compatibility hypothesis in this construction. -/
def compatibleArithmeticLabel_one
    (q : ℕ → HeightOneSpectrum (𝓞 K)) (hq : ∀ i, q i ∉ S)
    (hdegree : Module.finrank ℚ K = 2)
    (habove : ∀ i, ((selectedDerivativePrimes S e α E C (fun _ => 1) F excl).ell i : 𝓞 K) ∈
      (q i).asIdeal)
    (hinert : ∀ i, Nat.card (𝓞 K ⧸ (q i).asIdeal) =
      (selectedDerivativePrimes S e α E C (fun _ => 1) F excl).ell i ^ 2) :
    CompatibleArithmeticLabel E K S α :=
  compatibleArithmeticLabelFromSelection S e α E C (fun _ => 1) F excl
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) q hq hdegree habove hinert

end CharacterSelection

end ZInQ.Contrib.RC53Assist.FrobeniusMatch

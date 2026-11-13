import Mathlib

open Polynomial
open scoped TensorProduct

noncomputable section

namespace PropTSGlueDev3

abbrev zxMap (E : Type) [Field E] [Algebra ℚ[X] E] : ℤ[X] →+* E :=
  (algebraMap ℚ[X] E).comp (Polynomial.mapRingHom (Int.castRingHom ℚ))

theorem zxMap_injective (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] : Function.Injective (zxMap E) := by
  intro a b h
  simp only [zxMap, RingHom.comp_apply, IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E] at h
  have h1 := (algebraMap (RatFunc ℚ) E).injective h
  have h2 := (IsFractionRing.injective ℚ[X] (RatFunc ℚ)) h1
  exact Polynomial.map_injective _ Int.cast_injective h2

@[reducible] noncomputable def locAlg (E : Type) [Field E] [Algebra (RatFunc ℚ) E]
    [Algebra ℚ[X] E] [IsScalarTower ℚ[X] (RatFunc ℚ) E] (m : Ideal ℤ[X]) [m.IsPrime] :
    Algebra (Localization.AtPrime m) E :=
  (IsLocalization.lift (M := m.primeCompl) (S := Localization.AtPrime m) (g := zxMap E)
    (fun y => by
      rw [isUnit_iff_ne_zero]
      intro h
      apply y.2
      rw [(zxMap_injective E) (h.trans (map_zero _).symm)]
      exact m.zero_mem)).toAlgebra

/-- A field is its own localization at any submonoid of nonzero elements. -/
theorem isLocalization_field_self {A K : Type*} [CommRing A] [Field K] [Algebra A K]
    (M : Submonoid A) (hM : ∀ x ∈ M, algebraMap A K x ≠ 0) :
    IsLocalization (Algebra.algebraMapSubmonoid K M) K := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, x, hx, rfl⟩
    exact isUnit_iff_ne_zero.mpr (by simpa using hM x hx)
  · intro z
    exact ⟨⟨z, 1⟩, by simp⟩
  · intro x y h
    exact ⟨1, by simpa using h⟩

@[reducible] noncomputable def intPolyAlg (E : Type) [Field E] [Algebra ℚ[X] E] : Algebra ℤ[X] E :=
  ((algebraMap ℚ[X] E).comp (Polynomial.mapRingHom (Int.castRingHom ℚ))).toAlgebra

def vertPrime (p : ℕ) : Ideal ℤ[X] := Ideal.map (C : ℤ →+* ℤ[X]) (Ideal.span {(p : ℤ)})

def NoVerticalRam (E : Type) [Field E] [Algebra ℚ[X] E] (p : ℕ) : Prop :=
  letI := intPolyAlg E
  ∀ Q : Ideal (integralClosure ℤ[X] E), Q.IsPrime → Q.under ℤ[X] = vertPrime p →
    Q.ramificationIdx ℤ[X] = 1

theorem vertPrime_isPrime (p : ℕ) (hp : p.Prime) : (vertPrime p).IsPrime :=
  (Ideal.isPrime_map_C_iff_isPrime _).mpr
    ((Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp))

theorem sep_congr {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] {p q : Ideal A}
    [p.IsPrime] [q.IsPrime] (h : p = q) [Algebra.HasSeparableResidueFieldsAt A B p] :
    Algebra.HasSeparableResidueFieldsAt A B q := by
  subst h
  assumption

/-- ℚ(X) is the fraction field of ℤ[X]. -/
theorem isFractionRing_zx :
    letI : Algebra ℤ[X] (RatFunc ℚ) := (zxMap (RatFunc ℚ)).toAlgebra
    IsFractionRing ℤ[X] (RatFunc ℚ) := by
  letI : Algebra ℤ[X] (RatFunc ℚ) := (zxMap (RatFunc ℚ)).toAlgebra
  have hinj : Function.Injective (algebraMap ℤ[X] (RatFunc ℚ)) := zxMap_injective (RatFunc ℚ)
  refine ⟨?_, ?_, ?_⟩
  · intro y
    rw [isUnit_iff_ne_zero]
    intro h
    exact nonZeroDivisors.coe_ne_zero y (hinj (h.trans (map_zero _).symm))
  · intro z
    obtain ⟨⟨P, Q⟩, hz⟩ := IsLocalization.surj (nonZeroDivisors ℚ[X]) z
    obtain ⟨bP, hbPM, hbP⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) P
    obtain ⟨bQ, hbQM, hbQ⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ)
      (Q : ℚ[X])
    set P' := IsLocalization.integerNormalization (nonZeroDivisors ℤ) P
    set Q' := IsLocalization.integerNormalization (nonZeroDivisors ℤ) (Q : ℚ[X])
    have hbP0 : bP ≠ 0 := nonZeroDivisors.ne_zero hbPM
    have hbQ0 : bQ ≠ 0 := nonZeroDivisors.ne_zero hbQM
    have hQ0 : (Q : ℚ[X]) ≠ 0 := nonZeroDivisors.coe_ne_zero Q
    have hmapQ : Q'.map (Int.castRingHom ℚ) = C (bQ : ℚ) * Q := by
      rw [← smul_eq_C_mul]
      simpa [Algebra.smul_def] using hbQ
    have hmapP : P'.map (Int.castRingHom ℚ) = C (bP : ℚ) * P := by
      rw [← smul_eq_C_mul]
      simpa [Algebra.smul_def] using hbP
    have hy : C bP * Q' ∈ nonZeroDivisors ℤ[X] := by
      rw [mem_nonZeroDivisors_iff_ne_zero]
      refine mul_ne_zero (by simpa using hbP0) ?_
      intro h0
      have := hmapQ
      rw [h0, Polynomial.map_zero] at this
      exact mul_ne_zero (by simpa using hbQ0) hQ0 this.symm
    refine ⟨⟨C bQ * P', ⟨_, hy⟩⟩, ?_⟩
    simp only [RingHom.algebraMap_toAlgebra, zxMap, RingHom.comp_apply, coe_mapRingHom,
      Polynomial.map_C, hmapP, hmapQ, map_mul, eq_intCast]
    rw [← hz]
    simp only [map_intCast, Int.cast_id, Polynomial.map_intCast]
    ring
  · intro x y h
    exact ⟨1, by rw [hinj h]⟩


theorem vrd_aux (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E] (p : ℕ) (hp : p.Prime) :
    letI := intPolyAlg E
    haveI := vertPrime_isPrime p hp
    ∀ (q : Ideal (integralClosure ℤ[X] E)) [q.IsPrime] [q.LiesOver (vertPrime p)],
      letI := Localization.AtPrime.algebraOfLiesOver (vertPrime p) q
      FiniteDimensional (vertPrime p).ResidueField q.ResidueField ∧
        Module.finrank (vertPrime p).ResidueField q.ResidueField ≤
          Module.finrank (RatFunc ℚ) E := by
  letI := intPolyAlg E
  haveI := vertPrime_isPrime p hp
  intro q _ _
  letI := Localization.AtPrime.algebraOfLiesOver (vertPrime p) q
  letI iZK : Algebra ℤ[X] (RatFunc ℚ) := (zxMap (RatFunc ℚ)).toAlgebra
  have hZK : IsFractionRing ℤ[X] (RatFunc ℚ) := isFractionRing_zx
  have hZKE : IsScalarTower ℤ[X] (RatFunc ℚ) E := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    simp only [RingHom.algebraMap_toAlgebra, zxMap, RingHom.comp_apply]
    exact IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E _
  have hfinC : Module.Finite ℤ[X] (integralClosure ℤ[X] E) :=
    IsIntegralClosure.finite ℤ[X] (RatFunc ℚ) E (integralClosure ℤ[X] E)
  have hQF : Algebra.QuasiFinite ℤ[X] (integralClosure ℤ[X] E) := inferInstance
  letI : Fintype ((vertPrime p).primesOver (integralClosure ℤ[X] E)) :=
    (Algebra.QuasiFinite.finite_primesOver (vertPrime p)).fintype
  have hNoeth : IsNoetherianRing (integralClosure ℤ[X] E) :=
    IsIntegralClosure.isNoetherianRing ℤ[X] (RatFunc ℚ) E (integralClosure ℤ[X] E)
  have hfd : FiniteDimensional (vertPrime p).ResidueField q.ResidueField := inferInstance
  refine ⟨hfd, ?_⟩
  -- `e(q) > 0`
  have hmin : q ∈ ((vertPrime p).map (algebraMap ℤ[X] (integralClosure ℤ[X] E))).minimalPrimes := by
    refine ⟨⟨inferInstance, Ideal.map_le_iff_le_comap.mpr (le_of_eq (Ideal.over_def q (vertPrime p)))⟩,
      fun q' hq' hle => ?_⟩
    obtain ⟨hq'p, hmap⟩ := hq'
    by_contra hnle
    have hlt : q' < q := lt_of_le_of_ne hle (fun h => hnle (h ▸ le_rfl))
    have h1 := Ideal.IsIntegral.under_lt_under (R := ℤ[X]) hlt
    have h2 : vertPrime p ≤ q'.under ℤ[X] := Ideal.map_le_iff_le_comap.mp hmap
    rw [← Ideal.over_def q (vertPrime p)] at h1
    exact absurd (lt_of_le_of_lt h2 h1) (lt_irrefl _)
  have he : 0 < q.ramificationIdx ℤ[X] := Ideal.ramificationIdx_pos_of_mem_minimalPrimes _ _ hmin
  -- the sum formula
  have hsum := Ideal.sum_ramification_inertia_eq_finrank_fiber (vertPrime p) (integralClosure ℤ[X] E)
  have hqmem : q ∈ (vertPrime p).primesOver (integralClosure ℤ[X] E) := ⟨inferInstance, inferInstance⟩
  have hle := Finset.single_le_sum
    (f := fun x : (vertPrime p).primesOver (integralClosure ℤ[X] E) =>
      x.1.ramificationIdx ℤ[X] * x.1.inertiaDeg ℤ[X]) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ ⟨q, hqmem⟩)
  have hf : q.inertiaDeg ℤ[X] = Module.finrank (vertPrime p).ResidueField q.ResidueField :=
    Ideal.inertiaDeg_eq (vertPrime p) q
  have hfib : Module.finrank (vertPrime p).ResidueField
      ((vertPrime p).Fiber (integralClosure ℤ[X] E)) ≤ Module.finrank (RatFunc ℚ) E := by
    apply le_of_eq
    set 𝔭 := vertPrime p with h𝔭
    -- the local base `ℤ[X]_𝔭` and its maps to `ℚ(X)` and `E`
    letI iE : Algebra (Localization.AtPrime 𝔭) E := locAlg E 𝔭
    letI iK : Algebra (Localization.AtPrime 𝔭) (RatFunc ℚ) := locAlg (RatFunc ℚ) 𝔭
    have hT1 : IsScalarTower ℤ[X] (Localization.AtPrime 𝔭) (RatFunc ℚ) := by
      apply IsScalarTower.of_algebraMap_eq'
      exact (IsLocalization.lift_comp _).symm
    have hfr : IsFractionRing (Localization.AtPrime 𝔭) (RatFunc ℚ) :=
      IsFractionRing.isFractionRing_of_isDomain_of_isLocalization 𝔭.primeCompl _ _
    have hT2 : IsScalarTower (Localization.AtPrime 𝔭) (RatFunc ℚ) E := by
      apply IsScalarTower.of_algebraMap_eq'
      apply IsLocalization.ringHom_ext 𝔭.primeCompl
      rw [RingHom.comp_assoc]
      change (IsLocalization.lift _).comp (algebraMap ℤ[X] (Localization.AtPrime 𝔭)) =
        (algebraMap (RatFunc ℚ) E).comp
          ((IsLocalization.lift _).comp (algebraMap ℤ[X] (Localization.AtPrime 𝔭)))
      rw [IsLocalization.lift_comp, IsLocalization.lift_comp]
      simp only [zxMap, ← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
    have hTR : IsScalarTower ℤ[X] (Localization.AtPrime 𝔭) E := by
      apply IsScalarTower.of_algebraMap_eq'
      exact (IsLocalization.lift_comp _).symm
    have hic : IsIntegrallyClosed (Localization.AtPrime 𝔭) :=
      isIntegrallyClosed_of_isLocalization _ 𝔭.primeCompl 𝔭.primeCompl_le_nonZeroDivisors
    -- `ℤ[X]_𝔭` is a DVR (principal maximal ideal)
    have hCp0 : algebraMap ℤ[X] (Localization.AtPrime 𝔭) (C (p : ℤ)) ≠ 0 := by
      intro h0
      have := IsLocalization.injective (Localization.AtPrime 𝔭) 𝔭.primeCompl_le_nonZeroDivisors
        (h0.trans (map_zero _).symm)
      rw [C_eq_zero] at this
      exact hp.ne_zero (by exact_mod_cast this)
    have h3 : 𝔭 = Ideal.span {C (p : ℤ)} := by
      rw [h𝔭, vertPrime, Ideal.map_span, Set.image_singleton]
    have hmax : IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭) =
        Ideal.span {algebraMap ℤ[X] (Localization.AtPrime 𝔭) (C (p : ℤ))} := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      refine (congrArg (Ideal.map (algebraMap ℤ[X] (Localization.AtPrime 𝔭))) h3).trans ?_
      rw [Ideal.map_span, Set.image_singleton]
    have hnf : ¬ IsField (Localization.AtPrime 𝔭) := by
      intro hF
      have := (IsLocalRing.isField_iff_maximalIdeal_eq).mp hF
      rw [hmax, Ideal.span_singleton_eq_bot] at this
      exact hCp0 this
    have hprin : (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭)).IsPrincipal := ⟨⟨_, hmax⟩⟩
    have hdvr : IsDiscreteValuationRing (Localization.AtPrime 𝔭) :=
      ((IsDiscreteValuationRing.TFAE (Localization.AtPrime 𝔭) hnf).out 1 5).mpr hprin
    -- the integral closure `C₀` of `ℤ[X]_𝔭` in `E`
    have hinj : Function.Injective (algebraMap (Localization.AtPrime 𝔭) E) := by
      rw [IsScalarTower.algebraMap_eq (Localization.AtPrime 𝔭) (RatFunc ℚ) E]
      exact (algebraMap (RatFunc ℚ) E).injective.comp
        (IsFractionRing.injective (Localization.AtPrime 𝔭) (RatFunc ℚ))
    have hfs : FaithfulSMul (Localization.AtPrime 𝔭) E :=
      (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
    have hfree : Module.Free (Localization.AtPrime 𝔭) (integralClosure (Localization.AtPrime 𝔭) E) :=
      IsIntegralClosure.module_free (Localization.AtPrime 𝔭) (RatFunc ℚ) E
        (integralClosure (Localization.AtPrime 𝔭) E)
    have hfin0 : Module.Finite (Localization.AtPrime 𝔭) (integralClosure (Localization.AtPrime 𝔭) E) :=
      IsIntegralClosure.finite (Localization.AtPrime 𝔭) (RatFunc ℚ) E
        (integralClosure (Localization.AtPrime 𝔭) E)
    have hrank : Module.finrank (Localization.AtPrime 𝔭) (integralClosure (Localization.AtPrime 𝔭) E)
        = Module.finrank (RatFunc ℚ) E :=
      IsIntegralClosure.rank (Localization.AtPrime 𝔭) (RatFunc ℚ) E
        (integralClosure (Localization.AtPrime 𝔭) E)
    -- `C₀` is the localization of `C`
    let ιS : integralClosure ℤ[X] E →+* integralClosure (Localization.AtPrime 𝔭) E :=
      { toFun := fun c => ⟨c.1, IsIntegral.tower_top (A := Localization.AtPrime 𝔭) c.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    letI aCS := ιS.toAlgebra
    have hCSE : IsScalarTower (integralClosure ℤ[X] E) (integralClosure (Localization.AtPrime 𝔭) E)
        E := IsScalarTower.of_algebraMap_eq' rfl
    have hZCS : IsScalarTower ℤ[X] (integralClosure ℤ[X] E)
        (integralClosure (Localization.AtPrime 𝔭) E) := by
      apply IsScalarTower.of_algebraMap_eq
      intro x
      apply Subtype.ext
      rw [IsScalarTower.algebraMap_apply ℤ[X] (Localization.AtPrime 𝔭)
        (integralClosure (Localization.AtPrime 𝔭) E)]
      change algebraMap (Localization.AtPrime 𝔭) E (algebraMap ℤ[X] _ x) = algebraMap ℤ[X] E x
      exact (IsScalarTower.algebraMap_apply _ _ _ x).symm
    have hlocE : IsLocalization (Algebra.algebraMapSubmonoid E 𝔭.primeCompl) E :=
      isLocalization_field_self _ (fun x hx h0 => hx (by
        rw [(zxMap_injective E) (h0.trans (map_zero _).symm)]; exact 𝔭.zero_mem))
    have hlocS : IsLocalization (Algebra.algebraMapSubmonoid (integralClosure ℤ[X] E)
        𝔭.primeCompl) (integralClosure (Localization.AtPrime 𝔭) E) :=
      IsLocalization.integralClosure 𝔭.primeCompl
    have hlm : IsLocalizedModule 𝔭.primeCompl
        (IsScalarTower.toAlgHom ℤ[X] (integralClosure ℤ[X] E)
          (integralClosure (Localization.AtPrime 𝔭) E)).toLinearMap :=
      (isLocalizedModule_iff_isLocalization).mpr hlocS
    have hbc := IsLocalizedModule.isBaseChange 𝔭.primeCompl (Localization.AtPrime 𝔭)
      (IsScalarTower.toAlgHom ℤ[X] (integralClosure ℤ[X] E)
          (integralClosure (Localization.AtPrime 𝔭) E)).toLinearMap
    -- the chain of dimensions
    rw [← hrank]
    change Module.finrank 𝔭.ResidueField (𝔭.ResidueField ⊗[ℤ[X]] integralClosure ℤ[X] E) = _
    rw [← (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ[X] (Localization.AtPrime 𝔭) 𝔭.ResidueField
      𝔭.ResidueField (integralClosure ℤ[X] E)).finrank_eq,
      (hbc.equiv.baseChange (Localization.AtPrime 𝔭) 𝔭.ResidueField _ _).finrank_eq,
      Module.finrank_baseChange]
  calc Module.finrank (vertPrime p).ResidueField q.ResidueField = q.inertiaDeg ℤ[X] := hf.symm
    _ ≤ q.ramificationIdx ℤ[X] * q.inertiaDeg ℤ[X] := Nat.le_mul_of_pos_left _ he
    _ ≤ _ := hle
    _ = _ := hsum
    _ ≤ _ := hfib

end PropTSGlueDev3

#print axioms PropTSGlueDev3.vrd_aux

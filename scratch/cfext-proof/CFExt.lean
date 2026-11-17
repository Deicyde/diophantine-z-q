import Mathlib

open scoped TensorProduct
open IsLocalRing Polynomial

set_option linter.style.haveILetI false

namespace CFExtProof

theorem unram_step {K R L : Type*} [Field K] [Field L] [CommRing R] [IsLocalRing R] [Algebra K R]
    [Algebra K L] [Algebra.FormallyUnramified K L] [Module.Finite K L]
    (p : Ideal (R ⊗[K] L)) [p.IsPrime]
    (hp : p.comap (algebraMap R (R ⊗[K] L)) = maximalIdeal R)
    (π : R) (hπ : maximalIdeal R = Ideal.span {π})
    (a : R ⊗[K] L) (ha : a ∈ p) :
    ∃ s ∉ p, ∃ b, s * a = algebraMap R _ π * b := by
  let Ap := Localization.AtPrime p
  haveI : IsLocalHom (algebraMap R Ap) := by
    constructor
    intro x hx
    rw [IsScalarTower.algebraMap_apply R (R ⊗[K] L) Ap] at hx
    have h1 : algebraMap R (R ⊗[K] L) x ∈ p.primeCompl :=
      (IsLocalization.AtPrime.isUnit_to_map_iff Ap p _).mp hx
    by_contra hu
    refine h1 (show algebraMap R (R ⊗[K] L) x ∈ p from ?_)
    rw [← Ideal.mem_comap, hp]; exact hu
  haveI : Algebra.FormallyUnramified R Ap := Algebra.FormallyUnramified.comp R (R ⊗[K] L) Ap
  haveI : Algebra.EssFiniteType R Ap := Algebra.EssFiniteType.comp R (R ⊗[K] L) Ap
  have hmax := Algebra.FormallyUnramified.map_maximalIdeal (R := R) (S := Ap)
  have hmem : algebraMap (R ⊗[K] L) Ap a ∈ maximalIdeal Ap := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]; exact Ideal.mem_map_of_mem _ ha
  rw [← hmax, hπ, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hmem
  obtain ⟨z, hz⟩ := hmem
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl z
  have hz' : algebraMap (R ⊗[K] L) Ap (b * algebraMap R (R ⊗[K] L) π) = algebraMap (R ⊗[K] L) Ap (a * s) := by
    rw [map_mul, map_mul, ← hz, IsScalarTower.algebraMap_apply R (R ⊗[K] L) Ap, mul_right_comm,
      IsLocalization.mk'_spec]
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists p.primeCompl Ap).mp hz'
  refine ⟨c * s, p.primeCompl.mul_mem c.2 s.2, c * b, ?_⟩
  linear_combination -hc

theorem isAlgebraic_adjoin_of_transcendental {K F : Type} [Field K] [Field F] [Algebra K F]
    (t : F) (ht : Transcendental K t) (hfin : FiniteDimensional (IntermediateField.adjoin K {t}) F)
    (π : F) (hπ : Transcendental K π) : Algebra.IsAlgebraic (Algebra.adjoin K {π}) F := by
  let xt : Unit → F := fun _ => t
  let xπ : Unit → F := fun _ => π
  have it : AlgebraicIndependent K xt := algebraicIndependent_unique_type_iff.mpr ht
  have iπ : AlgebraicIndependent K xπ := algebraicIndependent_unique_type_iff.mpr hπ
  have hrt : Set.range xt = {t} := Set.range_const
  have hrπ : Set.range xπ = {π} := Set.range_const
  have halg : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range xt)) F := by
    rw [hrt, ← IntermediateField.isAlgebraic_adjoin_iff_top]
    exact Algebra.IsAlgebraic.of_finite _ _
  have bt : IsTranscendenceBasis K xt := it.isTranscendenceBasis_iff_isAlgebraic.mpr halg
  have htr : Cardinal.mk Unit = Algebra.trdeg K F := bt.cardinalMk_eq_trdeg
  have bπ : IsTranscendenceBasis K xπ :=
    iπ.isTranscendenceBasis_of_trdeg_le_of_finite htr.symm.le
  have := bπ.isAlgebraic
  rwa [hrπ] at this

/-- The archimedean step: a nonzero `d ∈ O` divides a power of `π`. -/
theorem exists_pow_eq_mul {K F : Type} [Field K] [Field F] [Algebra K F] (O : ValuationSubring F)
    (hK : ∀ c : K, algebraMap K F c ∈ O) (π : F) (hπ : π ∈ O.nonunits)
    (d : F) (hd : d ∈ O) (hd0 : d ≠ 0) (halg : IsAlgebraic (Algebra.adjoin K {π}) d) :
    ∃ m : ℕ, ∃ y ∈ O, π ^ m = d * y := by
  let O' : Subalgebra K F := { O.toSubring with algebraMap_mem' := hK }
  have hπO : π ∈ O := O.nonunits_subset hπ
  have hadj : Algebra.adjoin K {π} ≤ O' := Algebra.adjoin_le (Set.singleton_subset_iff.mpr hπO)
  have hev : ∀ P : (Algebra.adjoin K {π})[X], aeval d P ∈ O := by
    intro P
    induction P using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | monomial n a =>
      rw [aeval_monomial]
      exact mul_mem (hadj a.2) (pow_mem hd n)
  obtain ⟨Q, hQ0, hQ⟩ := halg
  obtain ⟨Q', hQeq, hndvd⟩ := Q.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hQ0 0
  rw [map_zero, sub_zero] at hQeq hndvd
  have hQ'd : aeval d Q' = 0 := by
    rw [hQeq, map_mul, map_pow, aeval_X] at hQ
    exact (mul_eq_zero.mp hQ).resolve_left (pow_ne_zero _ hd0)
  have hc0 : Q'.coeff 0 ≠ 0 := fun h => hndvd (X_dvd_iff.mpr h)
  obtain ⟨T, hT⟩ := X_dvd_sub_C (p := Q')
  have hcT : ((Q'.coeff 0 : Algebra.adjoin K {π}) : F) = -(d * aeval d T) := by
    have := congrArg (aeval d) hT
    rw [map_sub, aeval_C, hQ'd, map_mul, aeval_X] at this
    rw [← this]; simp [Subalgebra.algebraMap_eq]
  -- write the constant coefficient as P(π)
  obtain ⟨P, hP⟩ : ∃ P : K[X], aeval π P = ((Q'.coeff 0 : Algebra.adjoin K {π}) : F) := by
    have key : ∀ z ∈ Algebra.adjoin K {π}, ∃ P : K[X], aeval π P = z := by
      intro z hz
      rw [Algebra.adjoin_singleton_eq_range_aeval] at hz
      exact hz
    exact key _ (Q'.coeff 0).2
  have hP0 : P ≠ 0 := by
    rintro rfl
    rw [map_zero] at hP
    exact hc0 (Subtype.ext hP.symm)
  obtain ⟨R, hReq, hRndvd⟩ := P.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hP0 0
  rw [map_zero, sub_zero] at hReq hRndvd
  have hR0 : R.coeff 0 ≠ 0 := fun h => hRndvd (X_dvd_iff.mpr h)
  obtain ⟨S, hS⟩ := X_dvd_sub_C (p := R)
  have hRπ : aeval π R = algebraMap K F (R.coeff 0) + π * aeval π S := by
    have := congrArg (aeval π) hS
    rw [map_sub, aeval_C, map_mul, aeval_X] at this
    rw [← this]; ring
  have hSO : aeval π S ∈ O := hadj (Polynomial.aeval_mem_adjoin_singleton K π)
  have hvc : O.valuation (algebraMap K F (R.coeff 0)) = 1 := by
    apply le_antisymm ((O.valuation_le_one_iff _).mpr (hK _))
    have h1 := (O.valuation_le_one_iff _).mpr (hK (R.coeff 0)⁻¹)
    rw [map_inv₀, map_inv₀] at h1
    have hne : O.valuation (algebraMap K F (R.coeff 0)) ≠ 0 := by simpa using hR0
    exact (inv_le_one₀ (zero_lt_iff.mpr hne)).mp h1
  have hvR : O.valuation (aeval π R) = 1 := by
    rw [hRπ, Valuation.map_add_eq_of_lt_left, hvc]
    rw [hvc, map_mul]
    calc O.valuation π * O.valuation (aeval π S) ≤ O.valuation π :=
          mul_le_of_le_one_right' ((O.valuation_le_one_iff _).mpr hSO)
      _ < 1 := (O.mem_nonunits_iff).mp hπ
  set m := rootMultiplicity 0 P
  have hvd : O.valuation (π ^ m) ≤ O.valuation d := by
    have e1 : O.valuation (aeval π P) = O.valuation (π ^ m) := by
      rw [hReq, map_mul, map_pow, aeval_X, map_mul, hvR, mul_one]
    rw [← e1, hP, hcT, Valuation.map_neg, map_mul]
    exact mul_le_of_le_one_right' ((O.valuation_le_one_iff _).mpr (hev T))
  refine ⟨m, π ^ m / d, ?_, by field_simp⟩
  rw [← O.valuation_le_one_iff, map_div₀]
  have hv0 : O.valuation d ≠ 0 := by simpa using hd0
  exact (div_le_one₀ (zero_lt_iff.mpr hv0)).mpr hvd


/-- Verbatim copy of `JavanpeykarRebase.ConstantFieldExtensionUnramifiedFinite`
(ZInQKernel/Contrib/OneProof/JavanpeykarRebase.lean:48). -/
def ConstantFieldExtensionUnramifiedFinite : Prop :=
  ∀ (K F L FL : Type) [Field K] [Field F] [Field L] [Field FL] [Algebra K F] [Algebra K L]
    [Algebra L FL] [Algebra K FL] [IsScalarTower K L FL] [CharZero K] [FiniteDimensional K L]
    (ι : F →ₐ[K] FL),
    (∃ t : F, Transcendental K t ∧ FiniteDimensional (IntermediateField.adjoin K {t}) F) →
    (∀ a : F, IsAlgebraic K a → a ∈ Set.range (algebraMap K F)) →
    Function.Bijective (Algebra.TensorProduct.productMap ι (IsScalarTower.toAlgHom K L FL)) →
    ∀ w : ValuationSubring FL, (∀ c : L, algebraMap L FL c ∈ w) → ∀ π : F,
      π ∈ (w.comap (ι : F →+* FL)).nonunits →
      (∀ x ∈ (w.comap (ι : F →+* FL)).nonunits, ∃ y ∈ w.comap (ι : F →+* FL), x = π * y) →
      ∀ x ∈ w.nonunits, ∃ y ∈ w, x = ι π * y


theorem mem_nonunits_comap {E E' : Type} [Field E] [Field E'] (A : ValuationSubring E')
    (f : E →+* E') (x : E) : x ∈ (A.comap f).nonunits ↔ f x ∈ A.nonunits := by
  simp only [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_comap, map_inv₀,
    map_eq_zero]

/-- **Stichtenoth 3.6.3(a), finite case, proved.** -/
theorem constantFieldExtensionUnramifiedFinite_proof : ConstantFieldExtensionUnramifiedFinite := by
  intro K F L FL _ _ _ _ _ _ _ _ _ _ _ ι ht hfull hbij w hw π hπ hgen x hx
  set O := w.comap (ι : F →+* FL) with hOdef
  have hK : ∀ c : K, algebraMap K F c ∈ O := by
    intro c
    rw [ValuationSubring.mem_comap]
    change ι (algebraMap K F c) ∈ w
    rw [ι.commutes, IsScalarTower.algebraMap_apply K L FL]
    exact hw _
  letI : Algebra K O := ((algebraMap K F).codRestrict O hK).toAlgebra
  let jO : O →ₐ[K] F := { O.subtype with commutes' := fun _ => rfl }
  let φ : O ⊗[K] L →ₐ[K] FL := Algebra.TensorProduct.productMap (ι.comp jO)
    (IsScalarTower.toAlgHom K L FL)
  have hφt : ∀ (r : O) (l : L), φ (r ⊗ₜ l) = ι (r : F) * algebraMap L FL l := fun _ _ => rfl
  have hφw : ∀ z, φ z ∈ w := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul r l => rw [hφt]; exact mul_mem (ValuationSubring.mem_comap.mp r.2) (hw l)
    | add u v hu hv => rw [map_add]; exact add_mem hu hv
  have hφO : ∀ r : O, φ (algebraMap O (O ⊗[K] L) r) = ι (r : F) := by
    intro r
    rw [Algebra.TensorProduct.algebraMap_apply, hφt, map_one, mul_one]
    rfl
  let φw : O ⊗[K] L →+* w := φ.toRingHom.codRestrict w hφw
  let p : Ideal (O ⊗[K] L) := (maximalIdeal w).comap φw
  haveI : p.IsPrime := Ideal.comap_isPrime φw (maximalIdeal w)
  have hmemp : ∀ z, z ∈ p ↔ φ z ∈ w.nonunits := by
    intro z
    change φw z ∈ maximalIdeal w ↔ _
    rw [ValuationSubring.valuation_lt_one_iff, ValuationSubring.mem_nonunits_iff]
    rfl
  have hmaxO : ∀ r : O, r ∈ maximalIdeal O ↔ (r : F) ∈ O.nonunits := fun r =>
    ValuationSubring.coe_mem_nonunits_iff.symm
  have hp : p.comap (algebraMap O (O ⊗[K] L)) = maximalIdeal O := by
    ext r
    rw [Ideal.mem_comap, hmemp, hφO, hmaxO]
    exact (mem_nonunits_comap w _ _).symm
  have hπO : π ∈ O := O.nonunits_subset hπ
  let π' : O := ⟨π, hπO⟩
  have hspan : maximalIdeal O = Ideal.span {π'} := by
    ext r
    rw [hmaxO, Ideal.mem_span_singleton']
    constructor
    · intro hr
      obtain ⟨y, hy, hry⟩ := hgen _ hr
      exact ⟨⟨y, hy⟩, Subtype.ext (by simp [π', hry, mul_comm])⟩
    · rintro ⟨a, rfl⟩
      rw [ValuationSubring.mem_nonunits_iff] at hπ ⊢
      change O.valuation ((a : F) * π) < 1
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' (O.valuation_le_one a)) hπ
  haveI : Algebra.FormallyUnramified K L := Algebra.FormallyUnramified.of_isSeparable K L
  -- decomposition `x = ι c * φ a`
  have hdec : ∀ z : FL, ∃ c : F, ∃ a : O ⊗[K] L, z = ι c * φ a := by
    intro z
    obtain ⟨z, rfl⟩ := hbij.2 z
    induction z using TensorProduct.inductionOn with
    | tmul f l => exact ⟨f, 1 ⊗ₜ l, by rw [hφt]; simp⟩
    | add u v hu hv =>
      obtain ⟨c1, a1, h1⟩ := hu
      obtain ⟨c2, a2, h2⟩ := hv
      have key : ∀ (c1 c2 : F) (a1 a2 : O ⊗[K] L) (r : F) (hr : r ∈ O), c2 = c1 * r →
          ι c1 * φ a1 + ι c2 * φ a2 = ι c1 * φ (a1 + ((⟨r, hr⟩ : O) ⊗ₜ (1 : L)) * a2) := by
        intro c1 c2 a1 a2 r hr hc
        rw [map_add, map_mul, hφt, hc, map_mul, map_one, mul_one]
        ring
      rw [map_add, h1, h2]
      by_cases hc1 : c1 = 0
      · exact ⟨c2, a2, by simp [hc1]⟩
      by_cases hc2 : c2 = 0
      · exact ⟨c1, a1, by simp [hc2]⟩
      rcases O.mem_or_inv_mem (c2 / c1) with h | h
      · exact ⟨c1, _, key c1 c2 a1 a2 _ h (by field_simp)⟩
      · rw [inv_div] at h
        exact ⟨c2, _, by rw [add_comm]; exact key c2 c1 a2 a1 _ h (by field_simp)⟩
  have hunit : ∀ s, s ∉ p → φ s ≠ 0 ∧ (φ s)⁻¹ ∈ w := by
    intro s hs
    rw [hmemp, ValuationSubring.mem_nonunits_iff_or, not_or, not_not] at hs
    exact hs
  have hval_lt : ∀ u v : FL, u ∈ w → v ∈ w.nonunits → u * v ∈ w.nonunits := by
    intro u v hu hv
    rw [ValuationSubring.mem_nonunits_iff, map_mul] at *
    exact lt_of_le_of_lt (mul_le_of_le_one_left' ((w.valuation_le_one_iff u).mpr hu)) hv
  -- the final step
  have hbase : ∀ (c : F) (a s : O ⊗[K] L), s ∉ p → ι c * φ a = x * φ s →
      c ∈ O.nonunits → ∃ y ∈ w, x = ι π * y := by
    intro c a s hs he hc
    obtain ⟨y0, hy0, rfl⟩ := hgen c hc
    obtain ⟨hs0, hsinv⟩ := hunit s hs
    refine ⟨ι y0 * φ a * (φ s)⁻¹, mul_mem (mul_mem (ValuationSubring.mem_comap.mp hy0)
      (hφw a)) hsinv, ?_⟩
    rw [map_mul] at he
    field_simp
    linear_combination -he
  -- the iteration
  have hiter : ∀ k : ℕ, ∀ (c : F) (a s : O ⊗[K] L), s ∉ p → ι c * φ a = x * φ s →
      c * π ^ k ∈ O.nonunits → ∃ y ∈ w, x = ι π * y := by
    intro k
    induction k with
    | zero =>
      intro c a s hs he hc
      rw [pow_zero, mul_one] at hc
      exact hbase c a s hs he hc
    | succ k ih =>
      intro c a s hs he hc
      by_cases hc' : c ∈ O.nonunits
      · exact hbase c a s hs he hc'
      rw [ValuationSubring.mem_nonunits_iff_or, not_or, not_not] at hc'
      obtain ⟨hc0, hcinv⟩ := hc'
      have ha : a ∈ p := by
        rw [hmemp]
        have : φ a = ι c⁻¹ * (x * φ s) := by
          rw [← he, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]
        rw [this, mul_comm x]
        exact hval_lt _ _ (ValuationSubring.mem_comap.mp hcinv)
          (hval_lt _ _ (hφw s) hx)
      obtain ⟨s', hs', b, hb⟩ := unram_step p hp π' hspan a ha
      refine ih (c * π) b (s * s') (fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hs hs') ?_
        (by rwa [mul_assoc, ← pow_succ'])
      have hb' := congrArg φ hb
      rw [map_mul, map_mul, hφO] at hb'
      rw [map_mul, map_mul, mul_assoc, ← hb', mul_left_comm, he]
      ring
  -- the archimedean bound and conclusion
  obtain ⟨c, a, hxa⟩ := hdec x
  have hs1 : (1 : O ⊗[K] L) ∉ p := Ideal.IsPrime.ne_top ‹_› ∘ (Ideal.eq_top_of_isUnit_mem _ · isUnit_one)
  have he1 : ι c * φ a = x * φ 1 := by rw [map_one, mul_one, hxa]
  by_cases hπ0 : π = 0
  · exact hiter 1 c a 1 hs1 he1 (by simp [hπ0])
  by_cases hcn : c ∈ O.nonunits
  · exact hbase c a 1 hs1 he1 hcn
  rw [ValuationSubring.mem_nonunits_iff_or, not_or, not_not] at hcn
  obtain ⟨hc0, hcinv⟩ := hcn
  obtain ⟨t, htr, hfin⟩ := ht
  have hπtr : Transcendental K π := by
    intro halg
    obtain ⟨c0, hc0'⟩ := hfull π halg
    have hπinv : π⁻¹ ∈ O := by rw [← hc0', ← map_inv₀]; exact hK _
    have h2 := hπ
    rw [ValuationSubring.mem_nonunits_iff_or] at h2
    rcases h2 with h | h
    · exact hπ0 h
    · exact h hπinv
  have halgF := isAlgebraic_adjoin_of_transcendental t htr hfin π hπtr
  obtain ⟨m, y, hy, hm⟩ := exists_pow_eq_mul O hK π hπ c⁻¹ hcinv (inv_ne_zero hc0)
    (halgF.isAlgebraic _)
  refine hiter (m + 1) c a 1 hs1 he1 ?_
  have : c * π ^ (m + 1) = y * π := by
    rw [pow_succ, ← mul_assoc, hm]; field_simp
  rw [this]
  rw [ValuationSubring.mem_nonunits_iff] at hπ
  rw [ValuationSubring.mem_nonunits_iff, map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' ((O.valuation_le_one_iff y).mpr hy)) hπ

end CFExtProof

#print axioms CFExtProof.constantFieldExtensionUnramifiedFinite_proof

import Mathlib
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Inertia
import ZInQKernel.Contrib.TauCeti.RingTheory.DedekindDomain.AdicValuation.Transport
import ZInQKernel.Contrib.TauCeti.RingTheory.DedekindDomain.AdicValuation.Basic

namespace ZInQ.RLeaf.T37

open IsDedekindDomain Pointwise

section Bridge

variable {R K L : Type*} [CommRing R] [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
  [Algebra K L] [Algebra R L] [IsScalarTower R K L] [Algebra.IsAlgebraic K L]
  (B : Type*) [CommRing B] [IsDomain B] [IsDedekindDomain B] [Algebra B L] [IsFractionRing B L]
  [Algebra R B] [IsScalarTower R B L] [IsIntegralClosure B R L]

/-- The automorphism of `L = Frac B` induced by `galRestrict σ` is `σ`. -/
theorem ringEquivOfRingEquiv_galRestrict (σ : Gal(L/K)) (x : L) :
    IsFractionRing.ringEquivOfRingEquiv (A := B) (K := L) (B := B) (L := L)
      ((galRestrict R K L B σ : B ≃ₐ[R] B) : B ≃+* B) x = σ x := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := B) x
  rw [map_div₀, map_div₀, IsFractionRing.ringEquivOfRingEquiv_algebraMap,
    IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  simp only [AlgEquiv.coe_toRingEquiv]
  rw [algebraMap_galRestrict_apply, algebraMap_galRestrict_apply]

variable {B}

/-- An automorphism acting trivially modulo `v` preserves the `v`-adic valuation. -/
theorem valuation_apply_of_forall_sub_mem (σ : Gal(L/K)) (v : HeightOneSpectrum B)
    (hσ : ∀ a : B, galRestrict R K L B σ a - a ∈ v.asIdeal) (x : L) :
    v.valuation L (σ x) = v.valuation L x := by
  set e : B ≃+* B := ((galRestrict R K L B σ : B ≃ₐ[R] B) : B ≃+* B)
  have he : ∀ a, e a = galRestrict R K L B σ a := fun _ => rfl
  have hvw : v.asIdeal = Ideal.map e v.asIdeal := by
    apply le_antisymm
    · intro a ha
      have hb : e.symm a ∈ v.asIdeal := by
        have h1 := hσ (e.symm a)
        rw [← he, e.apply_symm_apply] at h1
        have := v.asIdeal.sub_mem ha h1
        simpa using this
      rw [Ideal.mem_map_of_equiv]
      exact ⟨e.symm a, hb, e.apply_symm_apply a⟩
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, he]
      have := v.asIdeal.add_mem ha (hσ a)
      simpa using this
  have := HeightOneSpectrum.valuation_ringEquivOfRingEquiv (K := L) (K' := L) e hvw x
  rwa [ringEquivOfRingEquiv_galRestrict] at this

/-- **Bridge**: an element of the ideal-theoretic inertia group of `v` (it acts trivially on
`B / v`) lies in the decomposition group and in the inertia group of the valuation subring of `v`
(Tau Ceti's / Mathlib's `ValuationSubring.inertiaSubgroup`). -/
theorem mem_inertiaSubgroup_of_forall_sub_mem (σ : Gal(L/K)) (v : HeightOneSpectrum B)
    (hσ : ∀ a : B, galRestrict R K L B σ a - a ∈ v.asIdeal) :
    ∃ h : σ ∈ (v.valuation L).valuationSubring.decompositionSubgroup K,
      (⟨σ, h⟩ : (v.valuation L).valuationSubring.decompositionSubgroup K) ∈
        (v.valuation L).valuationSubring.inertiaSubgroup K := by
  have hval := valuation_apply_of_forall_sub_mem σ v hσ
  have hval' : ∀ x : L, v.valuation L (σ⁻¹ x) = v.valuation L x := fun x => by
    conv_rhs => rw [← AlgEquiv.apply_symm_apply σ x]
    rw [hval]; rfl
  have hdec : σ ∈ (v.valuation L).valuationSubring.decompositionSubgroup K := by
    change σ • (v.valuation L).valuationSubring = (v.valuation L).valuationSubring
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def,
      Valuation.mem_valuationSubring_iff, Valuation.mem_valuationSubring_iff, hval']
  refine ⟨hdec, ?_⟩
  rw [ValuationSubring.mem_inertiaSubgroup_iff]
  intro y
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
  have hy : v.valuation L (y : L) ≤ 1 := y.2
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer v (y : L) hy
  set Y : L := (y : L)
  have hsmul : (((⟨σ, hdec⟩ : (v.valuation L).valuationSubring.decompositionSubgroup K) • y :
      (v.valuation L).valuationSubring) : L) = σ Y :=
    ValuationSubring.coe_decompositionSubgroup_smul _ _ y
  rw [AddSubgroupClass.coe_sub, hsmul]
  -- notation
  set D : L := algebraMap B L (d : B)
  set Nn : L := algebraMap B L n
  have hσD : σ D = algebraMap B L (galRestrict R K L B σ (d : B)) :=
    (algebraMap_galRestrict_apply R σ (d : B)).symm
  have hσN : σ Nn = algebraMap B L (galRestrict R K L B σ n) :=
    (algebraMap_galRestrict_apply R σ n).symm
  have hσY : σ Y * σ D = σ Nn := by rw [← map_mul, hnd]
  have hD1 : v.valuation L D = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact (v.intValuation_eq_one_iff_mem_primeCompl (d : B)).mpr d.2
  have hσD1 : v.valuation L (σ D) = 1 := by rw [hval, hD1]
  have hkey : (σ Y - Y) * (D * σ D) = (σ Nn - Nn) * D - Nn * (σ D - D) := by
    linear_combination D * hσY - σ D * hnd
  have hlt1 : v.valuation L (σ Nn - Nn) < 1 := by
    rw [hσN, ← map_sub, HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact hσ n
  have hlt2 : v.valuation L (σ D - D) < 1 := by
    rw [hσD, ← map_sub, HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact hσ d
  have hN1 : v.valuation L Nn ≤ 1 := HeightOneSpectrum.valuation_le_one v n
  have hrhs : v.valuation L ((σ Nn - Nn) * D - Nn * (σ D - D)) < 1 := by
    refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ ?_)
    · rw [map_mul, hD1, mul_one]; exact hlt1
    · rw [map_mul]
      calc v.valuation L Nn * v.valuation L (σ D - D) ≤ 1 * v.valuation L (σ D - D) := by
            gcongr
        _ < 1 := by rw [one_mul]; exact hlt2
  rw [← hkey, map_mul, map_mul, hD1, hσD1, mul_one, mul_one] at hrhs
  exact hrhs

end Bridge

section Core

open Polynomial WeierstrassCurve

variable {k : Type*} [Field k] [CharZero k] {L : Type*} [Field L] [Algebra (RatFunc k) L]
  [Algebra k[X] L] [IsScalarTower k[X] (RatFunc k) L] [FiniteDimensional (RatFunc k) L]
  [IsGalois (RatFunc k) L] [DecidableEq L]

/-- `γ < 1` in `ℤᵐ⁰` forces `γ ≤ exp (-1)`. -/
theorem le_exp_neg_one_of_lt_one {γ : WithZero (Multiplicative ℤ)} (h : γ < 1) :
    γ ≤ WithZero.exp (-1) := by
  rcases eq_or_ne γ 0 with rfl | hne
  · exact zero_le
  rw [← WithZero.exp_log hne] at h ⊢
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
  rw [WithZero.exp_le_exp]
  omega

/-- **Core of T37.** Let `L / k(T)` be finite Galois, generated by the coordinates of the
`N`-torsion of `W`, and let `B` be a valuation ring of `L` containing `k[T]` in which `p` is not a
unit. If `W` has good reduction at `p` (`k` of characteristic `0`), then `p` generates the maximal
ideal of `B`. -/
theorem core (W : WeierstrassCurve (RatFunc k)) [W.IsElliptic] (p : k[X]) (hp : Irreducible p)
    (hcoef : ∀ a ∈ ({W.a₁, W.a₂, W.a₃, W.a₄, W.a₆} : Set (RatFunc k)),
      ∃ b c : k[X], ¬ p ∣ c ∧ a * algebraMap k[X] (RatFunc k) c = algebraMap k[X] (RatFunc k) b)
    (hdisc : ∃ b c : k[X], ¬ p ∣ b ∧ ¬ p ∣ c ∧
      W.Δ * algebraMap k[X] (RatFunc k) c = algebraMap k[X] (RatFunc k) b)
    (N : ℕ) (hN : 0 < N)
    (hL : IntermediateField.adjoin (RatFunc k)
      (Affine.Point.xCoord '' {Q : (W⁄L).toAffine.Point | N • Q = 0} ∪
        Affine.Point.yCoord '' {Q : (W⁄L).toAffine.Point | N • Q = 0}) = ⊤)
    (B : ValuationSubring L) (hRB : ∀ c : k[X], algebraMap k[X] L c ∈ B)
    (hpB : algebraMap k[X] L p ∈ B.nonunits) :
    ∀ y ∈ B.nonunits, y / algebraMap k[X] L p ∈ B := by
  classical
  let A := integralClosure k[X] L
  have : IsDedekindDomain A := IsIntegralClosure.isDedekindDomain k[X] (RatFunc k) L A
  have : IsFractionRing A L := IsIntegralClosure.isFractionRing_of_finite_extension k[X] (RatFunc k) L A
  have : Module.Finite k[X] A := IsIntegralClosure.finite k[X] (RatFunc k) L A
  -- `A ⊆ B`
  have hAB : ∀ a : A, (a : L) ∈ B := by
    intro a
    obtain ⟨q, hqm, hq⟩ := a.2
    let φ0 : k[X] →+* B := (algebraMap k[X] L).codRestrict B.toSubring hRB
    have hint : IsIntegral B (a : L) := by
      refine ⟨q.map φ0, hqm.map φ0, ?_⟩
      rw [Polynomial.eval₂_map]
      have hc : (algebraMap B L).comp φ0 = algebraMap k[X] L := RingHom.ext fun _ => rfl
      rw [hc]; exact hq
    obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    rw [← hb]
    exact b.2
  let φ : A →+* B :=
    { toFun := fun a => ⟨(a : L), hAB a⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hφ : ∀ a : A, ((φ a : B) : L) = (a : L) := fun _ => rfl
  let P : Ideal A := (IsLocalRing.maximalIdeal B).comap φ
  have hmemP : ∀ a : A, a ∈ P ↔ (a : L) ∈ B.nonunits := fun a => by
    rw [Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff, hφ]
  have hcoeA : ∀ c : k[X], ((algebraMap k[X] A c : A) : L) = algebraMap k[X] L c := fun c => rfl
  have hcoeA' : ∀ c : k[X], algebraMap k[X] L c = algebraMap A L (algebraMap k[X] A c) :=
    fun c => rfl
  have hp0 : p ≠ 0 := hp.ne_zero
  have hπP : algebraMap k[X] A p ∈ P := by rw [hmemP, hcoeA]; exact hpB
  have hinj : Function.Injective (algebraMap k[X] L) := by
    rw [IsScalarTower.algebraMap_eq k[X] (RatFunc k) L]
    exact (algebraMap (RatFunc k) L).injective.comp (IsFractionRing.injective k[X] (RatFunc k))
  have hπ0 : algebraMap k[X] A p ≠ 0 := by
    intro h
    have h' : algebraMap k[X] L p = 0 := by rw [← hcoeA, h]; rfl
    exact hp0 (hinj (h'.trans (map_zero _).symm))
  have hPbot : P ≠ ⊥ := fun h => hπ0 (by rw [← Ideal.mem_bot, ← h]; exact hπP)
  let u : IsDedekindDomain.HeightOneSpectrum A := ⟨P, Ideal.comap_isPrime _ _, hPbot⟩
  set v := u.valuation L with hv_def
  -- `P ∩ k[X] = (p)`
  have hcomap : P.comap (algebraMap k[X] A) = Ideal.span {p} := by
    have hmax : (Ideal.span {p}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp
    refine (hmax.eq_of_le (Ideal.comap_isPrime _ _).ne_top ?_).symm
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hπP
  have hnotP : ∀ c : k[X], ¬ p ∣ c → algebraMap k[X] A c ∉ P := fun c hc h => by
    have : c ∈ P.comap (algebraMap k[X] A) := h
    rw [hcomap, Ideal.mem_span_singleton] at this
    exact hc this
  have hvA1 : ∀ a : A, a ∉ P → v (algebraMap A L a) = 1 := fun a ha => by
    rw [hv_def, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact (u.intValuation_eq_one_iff_mem_primeCompl a).mpr ha
  have hval_c : ∀ c : k[X], ¬ p ∣ c → v (algebraMap k[X] L c) = 1 := fun c hc => by
    rw [hcoeA']; exact hvA1 _ (hnotP c hc)
  have hval_le : ∀ c : k[X], v (algebraMap k[X] L c) ≤ 1 := fun c => by
    rw [hcoeA', hv_def]
    exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one u _
  -- `B` is the valuation ring of `u`
  have hunitB : ∀ d : A, d ∉ P → IsUnit (φ d) := fun d hd => by
    by_contra h
    exact hd ((IsLocalRing.mem_maximalIdeal _).mpr h)
  have hmV : ∀ y : L, v y < 1 → y ∈ B.nonunits := by
    intro y hy
    obtain ⟨n, d, hnd⟩ := IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer u
      y hy.le
    have hd1 : v (algebraMap A L (d : A)) = 1 := hvA1 _ d.2
    have hn : (n : A) ∈ P := by
      have h' : v (algebraMap A L n) < 1 := by
        rw [← hnd, map_mul, hd1, mul_one]; exact hy
      exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem u n).mp h'
    obtain ⟨e, he⟩ := hunitB (d : A) d.2
    have hy' : y = (n : L) * ((e⁻¹ : Bˣ) : B) := by
      have h1 : ((e : B) : L) = algebraMap A L (d : A) := by rw [he]; rfl
      have h2 : ((e : B) : L) * (((e⁻¹ : Bˣ) : B) : L) = 1 :=
        congrArg Subtype.val (Units.mul_inv e)
      calc y = y * (((e : B) : L) * (((e⁻¹ : Bˣ) : B) : L)) := by rw [h2, mul_one]
        _ = (y * algebraMap A L (d : A)) * (((e⁻¹ : Bˣ) : B) : L) := by rw [h1]; ring
        _ = _ := by rw [hnd]; rfl
    rw [hy', ValuationSubring.mem_nonunits_iff, map_mul]
    have h1 : B.valuation (n : L) < 1 := (B.mem_nonunits_iff).mp ((hmemP n).mp hn)
    have h2 : B.valuation (((e⁻¹ : Bˣ) : B) : L) ≤ 1 :=
      (B.valuation_le_one_iff _).mpr (((e⁻¹ : Bˣ) : B)).2
    calc B.valuation (n : L) * B.valuation (((e⁻¹ : Bˣ) : B) : L) ≤ B.valuation (n : L) * 1 := by
          gcongr
      _ < 1 := by rw [mul_one]; exact h1
  have hVB : v.valuationSubring ≤ B := by
    intro y hy
    obtain ⟨n, d, hnd⟩ := IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer u
      y hy
    obtain ⟨e, he⟩ := hunitB (d : A) d.2
    have h1 : ((e : B) : L) = algebraMap A L (d : A) := by rw [he]; rfl
    have h2 : ((e : B) : L) * (((e⁻¹ : Bˣ) : B) : L) = 1 :=
      congrArg Subtype.val (Units.mul_inv e)
    have hy' : y = (n : L) * (((e⁻¹ : Bˣ) : B) : L) := by
      calc y = y * (((e : B) : L) * (((e⁻¹ : Bˣ) : B) : L)) := by rw [h2, mul_one]
        _ = (y * algebraMap A L (d : A)) * (((e⁻¹ : Bˣ) : B) : L) := by rw [h1]; ring
        _ = _ := by rw [hnd]; rfl
    rw [hy']
    exact B.mul_mem _ _ (hAB n) (((e⁻¹ : Bˣ) : B)).2
  have hBV : B ≤ v.valuationSubring := by
    intro y hy
    by_contra hy'
    rw [Valuation.mem_valuationSubring_iff, not_le] at hy'
    have hy0 : y ≠ 0 := by rintro rfl; simp at hy'
    have hinv : v y⁻¹ < 1 := by
      rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hy'
    have h1 := hmV _ hinv
    rw [ValuationSubring.mem_nonunits_iff] at h1
    have h2 := (B.valuation_le_one_iff y).mpr hy
    have : B.valuation (y * y⁻¹) < 1 := by
      rw [map_mul]
      calc B.valuation y * B.valuation y⁻¹ ≤ 1 * B.valuation y⁻¹ := by gcongr
        _ < 1 := by rw [one_mul]; exact h1
    rw [mul_inv_cancel₀ hy0, map_one] at this
    exact lt_irrefl _ this
  have hBeq : B = v.valuationSubring := le_antisymm hBV hVB
  -- Tau Ceti's hypotheses at `V = 𝒪_v`
  have hvK : ∀ a : RatFunc k, (∃ b c : k[X], ¬ p ∣ c ∧
      a * algebraMap k[X] (RatFunc k) c = algebraMap k[X] (RatFunc k) b) →
      v (algebraMap (RatFunc k) L a) ≤ 1 := by
    rintro a ⟨b, c, hc, habc⟩
    have h := congrArg (algebraMap (RatFunc k) L) habc
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h
    have h' := congrArg v h
    rw [map_mul, hval_c c hc, mul_one] at h'
    rw [h']; exact hval_le b
  have hint : ∀ a ∈ ({W.a₁, W.a₂, W.a₃, W.a₄, W.a₆} : Set (RatFunc k)),
      algebraMap (RatFunc k) L a ∈ v.valuationSubring := fun a ha => hvK a (hcoef a ha)
  let Wi : WeierstrassCurve v.valuationSubring :=
    ⟨⟨_, hint W.a₁ (by simp)⟩, ⟨_, hint W.a₂ (by simp)⟩, ⟨_, hint W.a₃ (by simp)⟩,
      ⟨_, hint W.a₄ (by simp)⟩, ⟨_, hint W.a₆ (by simp)⟩⟩
  have hWi : W⁄L = Wi⁄L := by ext <;> rfl
  have hI : WeierstrassCurve.IsIntegral v.valuationSubring (W⁄L) := ⟨⟨Wi, hWi⟩⟩
  have hΔ : algebraMap v.valuationSubring L (integralModel v.valuationSubring (W⁄L)).Δ =
      algebraMap (RatFunc k) L W.Δ := by
    have h := congrArg WeierstrassCurve.Δ (baseChange_integralModel_eq v.valuationSubring (W⁄L))
    simpa only [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ] using h
  have hΔ1 : v (algebraMap (RatFunc k) L W.Δ) = 1 := by
    obtain ⟨b, c, hb, hc, hbc⟩ := hdisc
    have h := congrArg (algebraMap (RatFunc k) L) hbc
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h
    have h' := congrArg v h
    rw [map_mul, hval_c c hc, mul_one, hval_c b hb] at h'
    exact h'
  have hE : (integralModel v.valuationSubring (W⁄L)).IsElliptic := by
    refine ⟨?_⟩
    by_contra h
    have h1 := (Valuation.mem_maximalIdeal_iff (v := v)).mp ((IsLocalRing.mem_maximalIdeal _).mpr h)
    have h2 : v ((integralModel v.valuationSubring (W⁄L)).Δ : L) = 1 := by
      rw [← hΔ1, ← hΔ]; rfl
    rw [h2] at h1
    exact lt_irrefl _ h1
  have hn : ((N : ℕ) : A) ∉ u.asIdeal := by
    have h : ((N : ℕ) : A) = algebraMap k[X] A ((N : ℕ) : k[X]) := (map_natCast _ N).symm
    rw [h]
    refine hnotP _ fun hdvd => hp.not_isUnit (isUnit_of_dvd_unit hdvd ?_)
    rw [← Polynomial.C_eq_natCast, Polynomial.isUnit_C]
    exact isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hN.ne')
  have hS : ∀ σ ∈ v.valuationSubring.inertiaSubgroup (RatFunc k),
      ∀ Q ∈ {Q : (W⁄L).toAffine.Point | N • Q = 0},
        Affine.Point.map ((σ : v.valuationSubring.decompositionSubgroup (RatFunc k)) :
          Gal(L/RatFunc k)).toAlgHom (N • Q) = N • Q := by
    intro σ _ Q hQ
    rw [Set.mem_setOf_eq] at hQ
    rw [hQ, map_zero]
  have hbot := WeierstrassCurve.inertiaSubgroup_eq_bot_of_adjoin_coords_eq_top (A := A)
    (K := RatFunc k) (L := L) u hn hS hL
  -- the ideal-theoretic inertia group of `P` is trivial
  letI := IsIntegralClosure.MulSemiringAction k[X] (RatFunc k) L A
  have : IsGaloisGroup Gal(L/RatFunc k) k[X] A :=
    IsGaloisGroup.of_isFractionRing _ _ _ (RatFunc k) L
  have hinert : Ideal.inertia Gal(L/RatFunc k) P = ⊥ := by
    rw [eq_bot_iff]
    intro σ hσ
    have hσ' : ∀ a : A, galRestrict k[X] (RatFunc k) L A σ a - a ∈ u.asIdeal := fun a => hσ a
    obtain ⟨h, hmem⟩ := mem_inertiaSubgroup_of_forall_sub_mem (B := A) σ u hσ'
    rw [hbot, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hmem)
  -- hence `e(P | p) = 1`
  have hmax0 : (Ideal.span {p}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp
  have : (Ideal.span {p}).IsPrime := hmax0.isPrime
  have : P.LiesOver (Ideal.span {p}) := ⟨hcomap.symm⟩
  have : P.IsPrime := Ideal.comap_isPrime _ _
  have : P.IsMaximal := Ideal.IsPrime.isMaximal this hPbot
  have hinjA : Function.Injective (algebraMap k[X] A) := fun a b h =>
    hinj (by rw [hcoeA', hcoeA', h])
  have : Module.IsTorsionFree k[X] A := Module.isTorsionFree_iff_algebraMap_injective.mpr hinjA
  have : Module.Flat k[X] A := inferInstance
  have : CharZero (Ideal.span {p}).ResidueField :=
    charZero_of_injective_ringHom
      ((algebraMap k[X] (Ideal.span {p}).ResidueField).comp Polynomial.C).injective
  have : Algebra.HasSeparableResidueFieldsAt k[X] A (Ideal.span {p}) := inferInstance
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(L/RatFunc k))
    (Ideal.span {p}) P
  rw [hinert, Subgroup.card_bot,
    Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {p}) P Gal(L/RatFunc k)] at hcard
  have hmapspan : (Ideal.span {p}).map (algebraMap k[X] A) = Ideal.span {algebraMap k[X] A p} := by
    rw [Ideal.map_span, Set.image_singleton]
  have hmap0 : (Ideal.span {p}).map (algebraMap k[X] A) ≠ ⊥ := by
    rw [hmapspan, Ne, Ideal.span_singleton_eq_bot]; exact hπ0
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count (Ideal.span {p}) P hmap0]
    at hcard
  obtain ⟨Q, hPQ, hfac⟩ := Ideal.eq_prime_pow_mul_coprime hmap0 P
  rw [← hcard, pow_one] at hfac
  have hnot2 : algebraMap k[X] A p ∉ P ^ 2 := by
    intro h2
    have hle : Ideal.span {algebraMap k[X] A p} ≤ P ^ 2 := by
      rw [Ideal.span_le, Set.singleton_subset_iff]; exact h2
    rw [← hmapspan, hfac] at hle
    have hdvd : P * P ∣ P * Q := by rw [← pow_two]; exact Ideal.dvd_iff_le.mpr hle
    have hPQ' : P ∣ Q := (mul_dvd_mul_iff_left hPbot).mp hdvd
    rw [sup_eq_left.mpr (Ideal.le_of_dvd hPQ')] at hPQ
    exact (Ideal.IsPrime.ne_top inferInstance) hPQ
  have hvπ : v (algebraMap k[X] L p) = WithZero.exp (-1) := by
    rw [hcoeA', hv_def, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact u.intValuation_eq_exp_neg_one_of_mem_of_notMem_sq hπP hnot2
  -- conclusion
  intro y hy
  rw [hBeq] at hy ⊢
  have hyV : y ∈ v.valuationSubring := ValuationSubring.nonunits_subset hy
  have hy1 : v y < 1 := (Valuation.mem_maximalIdeal_iff (v := v) (a := ⟨y, hyV⟩)).mp
    (ValuationSubring.coe_mem_nonunits_iff.mp hy)
  rw [Valuation.mem_valuationSubring_iff, map_div₀, hvπ]
  have h := le_exp_neg_one_of_lt_one hy1
  rw [div_le_one₀ (by simp)]
  exact h

end Core

end ZInQ.RLeaf.T37
#print axioms ZInQ.RLeaf.T37.core

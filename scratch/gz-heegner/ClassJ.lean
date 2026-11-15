import ZInQKernel.Contrib.OneProof.GrossZagierHeegner
import ZInQKernel.Contrib.OneProof.RingClassLattice

/-! gz-heegner development: proof of `HeegnerClassJ` (merged into `Heegner.lean` when done). -/

noncomputable section

open NumberField TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
  TauCeti.ClassFieldTheory IsDedekindDomain
open ZInQ.RouteK.Rank5b ZInQ.RouteK.Redei ZInQ.Contrib.TYZGenus.RingClass
  ZInQ.Contrib.TYZGenus.Shimura

namespace ZInQ.GZHeegner

def sD (D : ℤ) : ℂ := Complex.I * (Real.sqrt (-(D : ℝ)) : ℂ)

def jLat (D a b : ℤ) : Submodule ℤ ℂ := Submodule.span ℤ {(a : ℂ), (-(b : ℂ) + sD D) / 2}

section ClassJ

variable {m : ℕ} [NeZero m]

set_option maxRecDepth 20000 in
/-- **Chebotarev for the Hilbert class field of `ℚ(√−m)`**: every class of `Pic(𝓞_K)` contains a
prime outside a given finite set (copy of the kernel's `RingClassTwo.exists_prime_picClass_eq`,
for the maximal order). -/
theorem exists_prime_picClass_eq1 (c : Pic (conductorOrder (QNeg m) 1))
    (T : Set (HeightOneSpectrum (𝓞 (QNeg m)))) (hT : T.Finite) :
    ∃ 𝔭 : HeightOneSpectrum (𝓞 (QNeg m)), 𝔭 ∉ T ∧
      ¬ (conductorOrder (QNeg m) 1).conductor ≤ 𝔭.asIdeal ∧
      ∀ hJ : 𝔭.asIdeal ∈ integralIdealsPrimeTo (conductorOrder (QNeg m) 1).conductorModulus,
        (conductorOrder (QNeg m) 1).picClass ⟨_, hJ⟩ = c := by
  have hD := NumberField.Chebotarev.hasNaturalDensity_frobeniusPrimeSet (QNeg m) (ringClassField (conductorOrder (QNeg m) 1))
    (ConjClasses.mk (ringClassArtinEquiv (conductorOrder (QNeg m) 1) c))
  have hδ : (Nat.card (ConjClasses.mk (ringClassArtinEquiv (conductorOrder (QNeg m) 1) c)).carrier : ℝ) /
      Nat.card (ringClassField (conductorOrder (QNeg m) 1) ≃ₐ[QNeg m] ringClassField (conductorOrder (QNeg m) 1)) ≠ 0 := by
    apply div_ne_zero
    · have : Nonempty (ConjClasses.mk (ringClassArtinEquiv (conductorOrder (QNeg m) 1) c)).carrier :=
        ⟨⟨_, ConjClasses.mem_carrier_mk⟩⟩
      exact_mod_cast (Nat.card_pos (α := (ConjClasses.mk (ringClassArtinEquiv (conductorOrder (QNeg m) 1) c)).carrier)).ne'
    · exact_mod_cast (Nat.card_pos (α := ringClassField (conductorOrder (QNeg m) 1) ≃ₐ[QNeg m] ringClassField (conductorOrder (QNeg m) 1))).ne'
  have hinf := ((hD.infinite hδ).sdiff (hT.union (finite_conductor_primes (d := m) 1)))
  obtain ⟨𝔭, h𝔭, h𝔭T⟩ := hinf.nonempty
  rw [Set.mem_union, not_or] at h𝔭T
  refine ⟨𝔭, h𝔭T.1, h𝔭T.2, fun hJ => ?_⟩
  obtain ⟨⟨Q, hQp, hQo⟩, hF⟩ :=
    NumberField.Chebotarev.exists_isArithFrobAt_of_mem_frobeniusPrimeSet_mk h𝔭
  have hur := NumberField.Chebotarev.isUnramifiedAt_of_mem_frobeniusPrimeSet h𝔭 Q
  have : ((⟨𝔭.asIdeal, hJ⟩ : integralIdealsPrimeTo (conductorOrder (QNeg m) 1).conductorModulus) :
    Ideal (𝓞 (QNeg m))).IsMaximal := 𝔭.isMaximal
  have : Q.LiesOver ((⟨𝔭.asIdeal, hJ⟩ : integralIdealsPrimeTo (conductorOrder (QNeg m) 1).conductorModulus) :
    Ideal (𝓞 (QNeg m))) := hQo
  have hF' := isArithFrobAt_ringClassArtinEquiv_picClass (conductorOrder (QNeg m) 1) ⟨_, hJ⟩ Q
  exact (ringClassArtinEquiv (conductorOrder (QNeg m) 1)).injective (isArithFrobAt_eq_of_isUnramifiedAt hF' hF)

/-- Elements of `𝓞_K`, `m ≡ 3 (mod 4)`, are `x₀ + x₁θ`, `θ = (1 + √−m)/2`. -/
theorem exists_coords_theta (hsq : Squarefree m) (h3 : m % 4 = 3) (y : 𝓞 (QNeg m)) :
    ∃ x₀ x₁ : ℤ, y = (x₀ : 𝓞 (QNeg m)) + x₁ * thetaO m h3 := by
  obtain ⟨a, t, N, ha, ht, hN⟩ := two_coords hsq y
  have hm : (m : ℤ) % 4 = 3 := by exact_mod_cast h3
  have hpar := parity_three hm hN
  have hat : 2 ∣ a - t := by
    rcases Int.emod_two_eq_zero_or_one t with h | h
    · have h2t : 2 ∣ t := Int.dvd_of_emod_eq_zero h
      exact dvd_sub (hpar.2 h2t) h2t
    · have hnt : ¬ 2 ∣ t := by omega
      have hna : ¬ 2 ∣ a := fun h' => hnt (hpar.1 h')
      omega
  obtain ⟨x₀, hx₀⟩ := hat
  refine ⟨x₀, t, ?_⟩
  rw [RingOfIntegers.ext_iff]
  simp only [RingOfIntegers.coe_eq_algebraMap, map_add, map_mul, map_intCast, algebraMap_thetaO,
    theta_eq]
  have hre : (algebraMap (𝓞 (QNeg m)) (QNeg m) y).re = a / 2 := by
    rw [← RingOfIntegers.coe_eq_algebraMap, ← ha]; ring
  have him : (algebraMap (𝓞 (QNeg m)) (QNeg m) y).im = t / 2 := by
    rw [← RingOfIntegers.coe_eq_algebraMap, ← ht]; ring
  have hax : (a : ℚ) = 2 * x₀ + t := by exact_mod_cast (by linarith : a = 2 * x₀ + t)
  ext
  · rw [hre]; simp [hax]; ring
  · rw [him]; simp [div_eq_mul_inv]

theorem coe_thetaO (h3 : m % 4 = 3) : ((thetaO m h3 : 𝓞 (QNeg m)) : QNeg m) = ⟨1 / 2, 1 / 2⟩ := by
  rw [RingOfIntegers.coe_eq_algebraMap, algebraMap_thetaO, theta_eq]

theorem kappa_theta_sub (h3 : m % 4 = 3) (r : ℤ) :
    kappa m (((thetaO m h3 - (r : 𝓞 (QNeg m)) : 𝓞 (QNeg m)) : QNeg m)) =
      (-(((2 * r - 1 : ℤ)) : ℂ) + sD (-(m : ℤ))) / 2 := by
  have h1 : (((thetaO m h3 - (r : 𝓞 (QNeg m)) : 𝓞 (QNeg m)) : QNeg m)) = ⟨1 / 2 - r, 1 / 2⟩ := by
    rw [RingOfIntegers.coe_eq_algebraMap, map_sub, ← RingOfIntegers.coe_eq_algebraMap,
      coe_thetaO, map_intCast]
    ext <;> simp
  rw [h1]
  simp only [kappa, sD]
  push_cast
  simp only [neg_neg]
  ring

theorem kappa_intCast (r : ℤ) : kappa m (((r : 𝓞 (QNeg m)) : QNeg m)) = r := by
  rw [RingOfIntegers.coe_eq_algebraMap, map_intCast]
  simp [kappa]

theorem kappa_lin (u v : ℤ) (x y : QNeg m) :
    kappa m (u * x + v * y) = u * kappa m x + v * kappa m y := by
  simp only [← kappaAlg_apply, map_add, map_mul, map_intCast]

theorem mem_order_one (y : 𝓞 (QNeg m)) :
    (y : QNeg m) ∈ (conductorOrder (QNeg m) 1).toSubalgebra :=
  ⟨0, y, by simp⟩

/-- **The lattice of an ideal with basis `⟨a, θ − r⟩`.** -/
theorem idealLat_eq_jLat (h3 : m % 4 = 3) (I : Ideal (𝓞 (QNeg m))) (a r : ℤ)
    (ha : ((a : ℤ) : 𝓞 (QNeg m)) ∈ I) (hr : thetaO m h3 - (r : 𝓞 (QNeg m)) ∈ I)
    (hI : ∀ y ∈ I, ∃ u v : ℤ, y = (u : 𝓞 (QNeg m)) * a + (v : 𝓞 (QNeg m)) * (thetaO m h3 - r)) :
    idealLat m 1 I = jLat (-(m : ℤ)) a (2 * r - 1) := by
  unfold idealLat jLat
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, ⟨-, y, hyI, rfl⟩, rfl⟩
    obtain ⟨u, v, rfl⟩ := hI y hyI
    rw [SetLike.mem_coe, Submodule.mem_span_pair]
    refine ⟨u, v, ?_⟩
    have : ((((u : 𝓞 (QNeg m)) * a + (v : 𝓞 (QNeg m)) * (thetaO m h3 - r) : 𝓞 (QNeg m))) : QNeg m) =
        (u : QNeg m) * (((a : 𝓞 (QNeg m)) : QNeg m)) +
          (v : QNeg m) * (((thetaO m h3 - (r : 𝓞 (QNeg m)) : 𝓞 (QNeg m)) : QNeg m)) := by
      simp only [RingOfIntegers.coe_eq_algebraMap, map_add, map_mul, map_intCast]
    rw [this, kappa_lin, kappa_intCast, kappa_theta_sub]
    simp [zsmul_eq_mul]
  · rw [Submodule.span_le]
    rintro _ (rfl | h)
    · exact Submodule.subset_span ⟨_, ⟨mem_order_one _, _, ha, rfl⟩, kappa_intCast a⟩
    · rw [Set.mem_singleton_iff] at h; subst h
      exact Submodule.subset_span ⟨_, ⟨mem_order_one _, _, hr, rfl⟩, kappa_theta_sub h3 r⟩

/-- `(θ − r)(1 − θ − r) = r² − r + (m + 1)/4`. -/
theorem theta_norm (h3 : m % 4 = 3) (r : ℤ) :
    (thetaO m h3 - r) * (1 - thetaO m h3 - r) =
      (((r ^ 2 - r + ((m : ℤ) + 1) / 4) : ℤ) : 𝓞 (QNeg m)) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, m = 4 * k + 3 := ⟨m / 4, by omega⟩
  have hk' : ((m : ℤ) + 1) / 4 = k + 1 := by omega
  rw [hk', RingOfIntegers.ext_iff]
  simp only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_sub, map_one, map_intCast]
  rw [← RingOfIntegers.coe_eq_algebraMap, coe_thetaO]
  have hm : (m : ℚ) = 4 * k + 3 := by exact_mod_cast hk
  push_cast
  simp only [sq]
  ext <;> simp [hm] <;> ring

end ClassJ

open ZInQ.Contrib.TYZGenus.RingClass in
/-- **`HeegnerClassJ`, proved** (Chebotarev in the Hilbert class field, Tau Ceti; the prime is split
or ramified, so `𝔭 = ⟨p, θ − r⟩`; an inert prime is principal, so its class is trivial and `J = 𝓞_K`). -/
theorem heegnerClassJ' (m : ℕ) [NeZero m] (hsq : Squarefree m) (h3 : m % 4 = 3) (M : ℤ)
    (hM : M ≠ 0) (cl : Pic (conductorOrder (QNeg m) 1)) :
    ∃ (J : integralIdealsPrimeTo (conductorOrder (QNeg m) 1).conductorModulus) (a b : ℤ),
      (conductorOrder (QNeg m) 1).picClass J = cl ∧ 0 < a ∧ 4 * a ∣ b ^ 2 - (-(m : ℤ)) ∧
      IsCoprime a M ∧ idealLat m 1 J = jLat (-(m : ℤ)) a b := by
  have hT : {𝔭 : HeightOneSpectrum (𝓞 (QNeg m)) |
      Ideal.span {((M : ℤ) : 𝓞 (QNeg m))} ≤ 𝔭.asIdeal}.Finite := by
    have hne : Ideal.span {((M : ℤ) : 𝓞 (QNeg m))} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact_mod_cast hM
    exact (Ideal.finite_factors hne).subset fun 𝔭 h𝔭 => Ideal.dvd_iff_le.2 h𝔭
  obtain ⟨𝔭, h𝔭T, hcond, h𝔭c⟩ := exists_prime_picClass_eq1 cl _ hT
  have hJ := mem_primeTo_of_not_le (d := m) (f := 1) 𝔭 hcond
  have hM𝔭 : ((M : ℤ) : 𝓞 (QNeg m)) ∉ 𝔭.asIdeal := fun h =>
    h𝔭T ((Ideal.span_singleton_le_iff_mem _).2 h)
  obtain ⟨p, hp, hlies⟩ := exists_prime_liesOver 𝔭.asIdeal 𝔭.ne_bot
  obtain ⟨σ, hσ⟩ := exists_conj_ne_one (n := m)
  -- the split/ramified case
  have split : Ideal.absNorm 𝔭.asIdeal = p → ∃ (J : integralIdealsPrimeTo
      (conductorOrder (QNeg m) 1).conductorModulus) (a b : ℤ),
      (conductorOrder (QNeg m) 1).picClass J = cl ∧ 0 < a ∧ 4 * a ∣ b ^ 2 - (-(m : ℤ)) ∧
      IsCoprime a M ∧ idealLat m 1 J = jLat (-(m : ℤ)) a b := by
    intro hN
    obtain ⟨r, hr⟩ := exists_int_sub_mem_of_absNorm 𝔭.asIdeal hp hN (thetaO m h3)
    refine ⟨⟨𝔭.asIdeal, hJ⟩, p, 2 * r - 1, h𝔭c hJ, by exact_mod_cast hp.pos, ?_, ?_, ?_⟩
    · -- `p ∣ r² − r + (m+1)/4`
      have hmem : (((r ^ 2 - r + ((m : ℤ) + 1) / 4) : ℤ) : 𝓞 (QNeg m)) ∈ 𝔭.asIdeal := by
        rw [← theta_norm h3 r]; exact Ideal.mul_mem_right _ _ hr
      obtain ⟨t, ht⟩ := (intCast_mem_iff_of_liesOver (p := p) 𝔭.asIdeal _).1 hmem
      obtain ⟨k, hk⟩ : ∃ k : ℕ, m = 4 * k + 3 := ⟨m / 4, by omega⟩
      have hk' : ((m : ℤ) + 1) / 4 = k + 1 := by omega
      rw [hk'] at ht
      refine ⟨t, ?_⟩
      have hm : (m : ℤ) = 4 * k + 3 := by exact_mod_cast hk
      rw [hm]; linear_combination 4 * ht
    · have hpM : ¬ (p : ℤ) ∣ M := fun h => hM𝔭 ((intCast_mem_iff_of_liesOver (p := p) 𝔭.asIdeal M).2 h)
      exact (Prime.irreducible (Nat.prime_iff_prime_int.1 hp)).coprime_iff_not_dvd.2 hpM
    · apply idealLat_eq_jLat h3 𝔭.asIdeal p r (by exact_mod_cast natCast_mem_of_liesOver (p := p) 𝔭.asIdeal) hr
      intro y hy
      obtain ⟨x₀, x₁, rfl⟩ := exists_coords_theta hsq h3 y
      have h1 : (((x₀ + x₁ * r : ℤ)) : 𝓞 (QNeg m)) ∈ 𝔭.asIdeal := by
        have : (((x₀ + x₁ * r : ℤ)) : 𝓞 (QNeg m)) =
            ((x₀ : 𝓞 (QNeg m)) + x₁ * thetaO m h3) - x₁ * (thetaO m h3 - r) := by push_cast; ring
        rw [this]; exact Ideal.sub_mem _ hy (Ideal.mul_mem_left _ _ hr)
      obtain ⟨t, ht⟩ := (intCast_mem_iff_of_liesOver (p := p) 𝔭.asIdeal _).1 h1
      refine ⟨t, x₁, ?_⟩
      have ht' : (x₀ : 𝓞 (QNeg m)) = p * t - x₁ * r := by
        have : ((x₀ : ℤ) : 𝓞 (QNeg m)) = ((p * t - x₁ * r : ℤ) : 𝓞 (QNeg m)) := by
          congr 1; linarith
        rw [this]; push_cast; ring
      rw [ht']; push_cast; ring
  rcases prime_trichotomy m σ hσ hp 𝔭.asIdeal with ⟨-, -, hN⟩ | ⟨-, hP, -⟩ | ⟨-, -, hN⟩
  · exact split hN
  · -- inert: `𝔭 = (p)` is principal, so `cl = 1`
    have h1 : (conductorOrder (QNeg m) 1).picClass ⟨𝔭.asIdeal, hJ⟩ = 1 :=
      ((conductorOrder (QNeg m) 1).picClass_eq_one_iff _).2
        ⟨p, Subalgebra.natCast_mem _ p, hP⟩
    rw [h𝔭c hJ] at h1
    subst h1
    refine ⟨1, 1, 1, map_one _, one_pos, ⟨((m : ℤ) + 1) / 4, by omega⟩, isCoprime_one_left, ?_⟩
    have h := idealLat_eq_jLat h3 (⊤ : Ideal (𝓞 (QNeg m))) 1 1 Submodule.mem_top
      Submodule.mem_top (fun y _ => by
        obtain ⟨x₀, x₁, rfl⟩ := exists_coords_theta hsq h3 y
        exact ⟨x₀ + x₁, x₁, by push_cast; ring⟩)
    norm_num at h
    convert h using 2
    simp [Ideal.one_eq_top]
  · exact split hN

end ZInQ.GZHeegner

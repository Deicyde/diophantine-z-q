import ZInQKernel.Contrib.OneProof.Abhyankar.KummerUnram

/-!
# abhyankar: `KummerUnramBranch` (Abhyankar's lemma for DVRs at `(f)`)

* `branch_e` — for `Ω₁ = L(t₁)`, `t₁^N = f`, and `A₁ = A[t₁, g] ⊆ Ω₁` (regular local of dimension 2 with
  maximal ideal `(t₁, g)`, `KummerBase`), every prime of the integral closure of `A₁` in `Ω₁` over `(t₁)` has
  ramification index `1` over `A₁`: Abhyankar's lemma for DVRs (`HDec.HSyn.t2_proved`) at `A_(f)` gives index `N`
  over `A`, `(t₁)` has index `N` over `A` (`A₁_(t₁)` is a DVR with uniformizer `t₁`, `f = t₁^N`), and indices
  multiply (`A₁ → A₁^{Ω₁}` is free, `TPurity3.normalFreeDim2`). Adapted from `TsKummer.abhyankar_core`
  (ZInQKernel/OneProof/H/TailG.lean), without its `ℚ`-algebra and Dedekind hypotheses.
-/

open IsLocalRing HDec Polynomial

set_option linter.all false

noncomputable section

namespace Abhyankar

theorem kummerBase' (A Ω : Type) [CommRing A] [IsDomain A] [IsRegularLocalRing A] [Field Ω]
    [Algebra A Ω] (hinj : Function.Injective (algebraMap A Ω)) (hdim : ringKrullDim A = 2)
    (f g : A) (hm : maximalIdeal A = Ideal.span {f, g}) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (t u : Ω) (ht : t ^ a = algebraMap A Ω f) (hu : u ^ b = algebraMap A Ω g)
    (A₁ : Subalgebra A Ω) (hA₁ : A₁ = Algebra.adjoin A {t, u}) (s v : A₁) (hs : (s : Ω) = t)
    (hv : (v : Ω) = u) :
    IsRegularLocalRing A₁ ∧ ringKrullDim A₁ = 2 ∧ ∃ _ : IsLocalRing A₁, maximalIdeal A₁ = Ideal.span {s, v} := by
  subst hA₁
  obtain ⟨hreg, hdim', hmax⟩ := kummerBase A Ω hinj hdim f g hm a b ha hb t u ht hu
  have e1 : s = ⟨t, Algebra.subset_adjoin (by simp)⟩ := Subtype.ext hs
  have e2 : v = ⟨u, Algebra.subset_adjoin (by simp)⟩ := Subtype.ext hv
  subst e1 e2
  exact ⟨hreg, hdim', hreg.toIsLocalRing, (IsLocalRing.eq_maximalIdeal hmax).symm⟩

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 3200000 in
theorem branch_e (A K L Ω₁ : Type) [CommRing A] [IsDomain A] [IsRegularLocalRing A] [Field K]
    [Field L] [Field Ω₁] [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [FiniteDimensional K L] [IsGalois K L] [Algebra L Ω₁] [Algebra K Ω₁]
    [Algebra A Ω₁] [IsScalarTower A K Ω₁] [IsScalarTower K L Ω₁] [FiniteDimensional L Ω₁]
    (hdim : ringKrullDim A = 2) (f g : A) (hm : maximalIdeal A = Ideal.span {f, g})
    (hfp : (Ideal.span {f}).IsPrime) (p : ℕ) (hp : p.Prime) (hpm : (p : A) ∈ maximalIdeal A)
    (hdeg : Module.finrank K L < p) (t₁ : Ω₁) (ht₁ : t₁ ^ Module.finrank K L = algebraMap A Ω₁ f)
    (hadj₁ : IntermediateField.adjoin L {t₁} = ⊤)
    (A₁ : Subalgebra A Ω₁) (hA₁ : A₁ = Algebra.adjoin A {t₁, algebraMap A Ω₁ g}) (s g₁ : A₁)
    (hs : (s : Ω₁) = t₁) (hg₁ : (g₁ : Ω₁) = algebraMap A Ω₁ g)
    (Q₁ : Ideal (integralClosure A₁ Ω₁)) [hQ₁p : Q₁.IsPrime] (hQ₁ : Q₁.under A₁ = Ideal.span {s}) :
    Q₁.ramificationIdx A₁ = 1 := by
  classical
  set N := Module.finrank K L with hNdef
  have hN : 0 < N := Module.finrank_pos
  have hAΩ : Function.Injective (algebraMap A Ω₁) := by
    rw [IsScalarTower.algebraMap_eq A K Ω₁]
    exact (algebraMap K Ω₁).injective.comp (IsFractionRing.injective A K)
  obtain ⟨hreg₁, hdim₁, hloc₁, hmaxA₁⟩ := kummerBase' A Ω₁ hAΩ hdim f g hm N 1 hN one_pos t₁
    (algebraMap A Ω₁ g) ht₁ (pow_one _) A₁ hA₁ s g₁ hs hg₁
  haveI := hreg₁
  haveI hsp : (Ideal.span {s}).IsPrime :=
    span_prime_of_pair hdim₁ (x := g₁) (y := s) (by rw [hmaxA₁, TPurity3.span_pair_comm])
  haveI : IsIntegrallyClosed A := TPurity3.isIntegrallyClosed_of_dim2 hdim
  haveI : IsIntegrallyClosed A₁ := TPurity3.isIntegrallyClosed_of_dim2 hdim₁
  have hf0 : f ≠ 0 := TPurity3.ne_zero_of_pair hm (TPurity3.height_maximalIdeal_of_dim2 hdim)
  have hfm : f ∈ maximalIdeal A := by rw [hm]; exact Ideal.subset_span (by simp)
  have hp₀1 : (Ideal.span {f}).height = 1 := by
    apply le_antisymm (Ideal.height_span_singleton_le_one ((mem_maximalIdeal f).mp hfm))
    rw [ENat.one_le_iff_ne_zero]
    intro h0
    have := Ideal.height_eq_zero_iff_eq_bot.mp h0
    rw [Ideal.span_singleton_eq_bot] at this
    exact hf0 this
  haveI : IsDomain (Localization.AtPrime (Ideal.span {f})) :=
    IsLocalization.isDomain_localization (Ideal.span {f}).primeCompl_le_nonZeroDivisors
  haveI hDVR : IsDiscreteValuationRing (Localization.AtPrime (Ideal.span {f})) := dvr_atPrime (Ideal.span {f}) hp₀1
  letI : Algebra (Localization.AtPrime (Ideal.span {f})) K := IsLocalization.localizationAlgebraOfSubmonoidLe _ K
    (Ideal.span {f}).primeCompl (nonZeroDivisors A) (Ideal.span {f}).primeCompl_le_nonZeroDivisors
  haveI : IsScalarTower A (Localization.AtPrime (Ideal.span {f})) K :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ K _ _ (Ideal.span {f}).primeCompl_le_nonZeroDivisors
  haveI : IsFractionRing (Localization.AtPrime (Ideal.span {f})) K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Ideal.span {f}).primeCompl _ K
  letI : Algebra (Localization.AtPrime (Ideal.span {f})) L :=
    ((algebraMap K L).comp (algebraMap (Localization.AtPrime (Ideal.span {f})) K)).toAlgebra
  letI : Algebra (Localization.AtPrime (Ideal.span {f})) Ω₁ :=
    ((algebraMap K Ω₁).comp (algebraMap (Localization.AtPrime (Ideal.span {f})) K)).toAlgebra
  haveI : IsScalarTower (Localization.AtPrime (Ideal.span {f})) K L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower (Localization.AtPrime (Ideal.span {f})) K Ω₁ := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower A (Localization.AtPrime (Ideal.span {f})) L := IsScalarTower.of_algebraMap_eq (fun x => by
    show algebraMap A L x = algebraMap K L (algebraMap (Localization.AtPrime (Ideal.span {f})) K (algebraMap A _ x))
    rw [← IsScalarTower.algebraMap_apply A (Localization.AtPrime (Ideal.span {f})) K,
      ← IsScalarTower.algebraMap_apply A K L])
  haveI : IsScalarTower A (Localization.AtPrime (Ideal.span {f})) Ω₁ := IsScalarTower.of_algebraMap_eq (fun x => by
    show algebraMap A Ω₁ x = algebraMap K Ω₁ (algebraMap (Localization.AtPrime (Ideal.span {f})) K (algebraMap A _ x))
    rw [← IsScalarTower.algebraMap_apply A (Localization.AtPrime (Ideal.span {f})) K,
      ← IsScalarTower.algebraMap_apply A K Ω₁])
  have hPM : ∀ x ∈ (Ideal.span {f}).primeCompl, algebraMap A Ω₁ x ≠ 0 := fun x hx h0 =>
    hx (by rw [hAΩ (h0.trans (map_zero _).symm)]; exact (Ideal.span {f}).zero_mem)
  have hmaxRp : maximalIdeal (Localization.AtPrime (Ideal.span {f})) =
      Ideal.span {algebraMap A (Localization.AtPrime (Ideal.span {f})) f} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact (Ideal.map_span _ _).trans (by rw [Set.image_singleton])
  have hirr : Irreducible (algebraMap A (Localization.AtPrime (Ideal.span {f})) f) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hmaxRp
  have hunit : IsUnit (N : Localization.AtPrime (Ideal.span {f})) := by
    have := (isUnit_natCast_of_not_dvd hp hpm (n := N)
      (fun h => absurd (Nat.le_of_dvd hN h) (not_le.mpr hdeg))).map (algebraMap A (Localization.AtPrime (Ideal.span {f})))
    rwa [map_natCast] at this
  have htame := tame_at p hp hpm hdeg (Ideal.span {f}) (Localization.AtPrime (Ideal.span {f})) (K := K) (L := L)
  have hyp : ∀ (Q : Ideal (integralClosure (Localization.AtPrime (Ideal.span {f})) L)) [Q.IsPrime]
      [Q.LiesOver (maximalIdeal (Localization.AtPrime (Ideal.span {f})))],
      IsUnit ((Q.ramificationIdx (Localization.AtPrime (Ideal.span {f})) : ℕ) : Localization.AtPrime (Ideal.span {f})) ∧
      Q.ramificationIdx (Localization.AtPrime (Ideal.span {f})) ∣ N ∧
      Algebra.IsSeparable (Localization.AtPrime (Ideal.span {f}) ⧸ maximalIdeal (Localization.AtPrime (Ideal.span {f})))
        (integralClosure (Localization.AtPrime (Ideal.span {f})) L ⧸ Q) :=
    fun Q _ _ => ⟨(htame Q).2.1, (htame Q).1, (htame Q).2.2⟩
  have ht : t₁ ^ N = algebraMap (Localization.AtPrime (Ideal.span {f})) Ω₁ (algebraMap A (Localization.AtPrime (Ideal.span {f})) f) := by
    rw [← IsScalarTower.algebraMap_apply A (Localization.AtPrime (Ideal.span {f})) Ω₁]; exact ht₁
  have key := HDec.HSyn.t2_proved (Localization.AtPrime (Ideal.span {f})) K L Ω₁
    (algebraMap A (Localization.AtPrime (Ideal.span {f})) f) hirr N hN hunit hyp t₁ ht hadj₁
  -- localizing the integral closure of `A` in `Ω₁`
  obtain ⟨hM1, hM2, hM3⟩ := TsKummer.intCl_isLocalization A (Localization.AtPrime (Ideal.span {f})) Ω₁
    (Ideal.span {f}).primeCompl hPM
  letI := (TsKummer.intClIncl A (Localization.AtPrime (Ideal.span {f})) Ω₁).toAlgebra
  -- `integralClosure A₁ Ω₁ = integralClosure A Ω₁`
  haveI hintA₁ : Algebra.IsIntegral A A₁ := by
    rw [hA₁]
    exact Algebra.IsIntegral.adjoin (by
      rintro x (rfl | rfl)
      · exact ⟨_, monic_X_pow_sub_C f hN.ne', by simp [ht₁]⟩
      · exact isIntegral_algebraMap)
  have hmem : ∀ x : Ω₁, IsIntegral A₁ x ↔ IsIntegral A x := fun x =>
    ⟨fun h => isIntegral_trans x h, fun h => h.tower_top⟩
  let f0 : integralClosure A₁ Ω₁ ≃+* integralClosure A Ω₁ :=
    { toFun := fun x => ⟨x.1, (hmem x.1).1 x.2⟩
      invFun := fun y => ⟨y.1, (hmem y.1).2 y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  let fe : integralClosure A₁ Ω₁ ≃ₐ[A] integralClosure A Ω₁ :=
    AlgEquiv.ofRingEquiv (f := f0) (fun r => rfl)
  -- `(s) ∩ A = (f)`
  have hs0 : s ≠ 0 := by
    intro h
    apply hf0
    apply hAΩ
    rw [map_zero, ← ht₁, ← hs, h]
    simp [hN.ne']
  have hs1 : (Ideal.span {s}).height = 1 := by
    have hsm : s ∈ maximalIdeal A₁ := by rw [hmaxA₁]; exact Ideal.subset_span (by simp)
    apply le_antisymm (Ideal.height_span_singleton_le_one ((mem_maximalIdeal s).mp hsm))
    rw [ENat.one_le_iff_ne_zero]
    intro h0
    have := Ideal.height_eq_zero_iff_eq_bot.mp h0
    rw [Ideal.span_singleton_eq_bot] at this
    exact hs0 this
  haveI : FaithfulSMul A A₁ :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (fun x y h => hAΩ (congrArg Subtype.val h))
  have hfs : algebraMap A A₁ f = s ^ N := Subtype.ext (by
    show algebraMap A Ω₁ f = (s : Ω₁) ^ N
    rw [hs, ht₁])
  have hsunder : (Ideal.span {s}).comap (algebraMap A A₁) = Ideal.span {f} := by
    symm
    apply Ideal.eq_of_le_of_height_le
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      show algebraMap A A₁ f ∈ Ideal.span {s}
      rw [hfs]
      exact Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self s) N hN
    · rw [hp₀1]
      exact le_of_eq (height_under_eq_one (Ideal.span {s}) hs1)
  haveI : (Ideal.span {s}).LiesOver (Ideal.span {f}) := ⟨hsunder.symm⟩
  haveI : Q₁.LiesOver (Ideal.span {s}) := ⟨hQ₁.symm⟩
  haveI : Q₁.LiesOver (Ideal.span {f}) := Ideal.LiesOver.trans Q₁ (Ideal.span {s}) (Ideal.span {f})
  set P := Q₁.map fe with hP_def
  haveI : P.IsPrime := Ideal.map_isPrime_of_equiv fe
  have hPunder : P.under A = Ideal.span {f} := by
    ext x
    rw [Ideal.under, Ideal.mem_comap, hP_def, ← fe.commutes x, ← Ideal.mem_comap,
      Ideal.comap_map_of_bijective fe fe.bijective, ← Ideal.mem_comap]
    change x ∈ Q₁.under A ↔ x ∈ Ideal.span {f}
    rw [← Ideal.LiesOver.over (P := Q₁) (p := Ideal.span {f})]
  haveI : P.LiesOver (Ideal.span {f}) := ⟨hPunder.symm⟩
  haveI := IsLocalization.AtPrime.isPrime_map_of_liesOver (integralClosure A Ω₁) (Ideal.span {f})
    (integralClosure (Localization.AtPrime (Ideal.span {f})) Ω₁) P
  haveI := IsLocalization.AtPrime.liesOver_map_of_liesOver (Ideal.span {f})
    (Localization.AtPrime (Ideal.span {f})) (integralClosure (Localization.AtPrime (Ideal.span {f})) Ω₁) P
  have h1 := (key (P.map (algebraMap (integralClosure A Ω₁)
    (integralClosure (Localization.AtPrime (Ideal.span {f})) Ω₁)))).1
  rw [IsLocalization.AtPrime.ramificationIdx_map_eq_ramificationIdx (Ideal.span {f})
    (Localization.AtPrime (Ideal.span {f})) (integralClosure (Localization.AtPrime (Ideal.span {f})) Ω₁) P,
    hP_def, TsKummer.ramificationIdx_map_algEquiv fe Q₁] at h1
  -- the tower `A → A₁ → integralClosure A₁ Ω₁`
  haveI : FiniteDimensional K Ω₁ := Module.Finite.trans L Ω₁
  haveI : IsScalarTower A L Ω₁ := IsScalarTower.of_algebraMap_eq (fun a => by
    rw [IsScalarTower.algebraMap_apply A K Ω₁, IsScalarTower.algebraMap_apply A K L,
      ← IsScalarTower.algebraMap_apply K L Ω₁])
  have hAL : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  have hNL : ((N : ℕ) : L) ≠ 0 := by
    have hu' := (isUnit_natCast_of_not_dvd hp hpm (n := N)
      (fun h => absurd (Nat.le_of_dvd hN h) (not_le.mpr hdeg))).map (algebraMap A L)
    rw [map_natCast] at hu'
    exact hu'.ne_zero
  haveI : Algebra.IsSeparable L Ω₁ := by
    have h1 := (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable (F := L) (x := t₁)).mpr
      (isSeparable_of_pow hNL (a := algebraMap A L f) (fun h => hf0 (hAL (by rw [h, map_zero])))
        (by rw [ht₁, ← IsScalarTower.algebraMap_apply]))
    rw [hadj₁] at h1
    exact Algebra.IsSeparable.of_algHom _ _ (IntermediateField.topEquiv (F := L) (E := Ω₁)).symm.toAlgHom
  haveI : Algebra.IsSeparable K Ω₁ := Algebra.IsSeparable.trans K L Ω₁
  haveI : Module.Finite A (integralClosure A Ω₁) := IsIntegralClosure.finite A K Ω₁ (integralClosure A Ω₁)
  let eA : integralClosure A Ω₁ ≃ₗ[A] integralClosure A₁ Ω₁ :=
    { toFun := fun x => ⟨x.1, (hmem x.1).2 x.2⟩
      invFun := fun x => ⟨x.1, (hmem x.1).1 x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => by
        apply Subtype.ext
        show r • (x : Ω₁) = _
        rfl }
  haveI : Module.Finite A (integralClosure A₁ Ω₁) := Module.Finite.equiv eA
  haveI : Module.Finite A₁ (integralClosure A₁ Ω₁) := Module.Finite.of_restrictScalars_finite A _ _
  haveI : IsIntegrallyClosed (integralClosure A₁ Ω₁) := isIntegrallyClosed_tower A K Ω₁ A₁
  haveI : Module.Free A₁ (integralClosure A₁ Ω₁) := TPurity3.normalFreeDim2 A₁ _ hdim₁
    (fun x y h => Subtype.ext (congrArg (fun w : integralClosure A₁ Ω₁ => (w : Ω₁)) h))
  have htow := Ideal.ramificationIdx_tower (R := A) (Ideal.span {s}) Q₁
  have hsn' : (Ideal.span {s}).ramificationIdx A = N := by
    haveI : IsDomain (Localization.AtPrime (Ideal.span {s})) :=
      IsLocalization.isDomain_localization (Ideal.span {s}).primeCompl_le_nonZeroDivisors
    haveI : IsDiscreteValuationRing (Localization.AtPrime (Ideal.span {s})) := dvr_atPrime _ hs1
    rw [Ideal.ramificationIdx_eq (Ideal.span {f}) (Ideal.span {s})]
    have hmapn : (Ideal.span {f}).map (algebraMap A (Localization.AtPrime (Ideal.span {s}))) =
        maximalIdeal (Localization.AtPrime (Ideal.span {s})) ^ N := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow, Ideal.span_singleton_pow,
        Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton,
        IsScalarTower.algebraMap_apply A A₁ (Localization.AtPrime (Ideal.span {s})), hfs]
    rw [hmapn, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal, ENat.toNat_natCast]
  rw [h1, hsn'] at htow
  have : N * Q₁.ramificationIdx A₁ = N * 1 := by rw [← htow, mul_one]
  exact Nat.eq_of_mul_eq_mul_left hN this

end Abhyankar

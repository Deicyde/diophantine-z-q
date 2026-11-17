import Mathlib

/-!
# Part A: an unramified separable-algebraic extension of a DVR is ind-étale

`O` a DVR with fraction field `K`, `O' ⊆ K'` a valuation ring, `K'/K` separable algebraic, `O → O'` with
every uniformizer of `O` irreducible in `O'` and `κ(O')/κ(O)` separable. Then every finite subset of `O'` lies
in an `O`-subalgebra of `O'` that is étale over `O`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open IsLocalRing

namespace NeronSH

section KeyLemma

variable {O K K' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
  [IsFractionRing O K] [Field K'] [Algebra K K'] [Algebra O K'] [IsScalarTower O K K']
  (O' : ValuationSubring K') [Algebra O O'] [IsScalarTower O O' K']

theorem mem_of_isIntegral {x : K'} (hx : IsIntegral O x) : x ∈ O' := by
  have h1 : IsIntegral O' x := hx.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h1
  rw [← hy]; exact y.2

variable (K) in
/-- The subfield of `K'` generated over `K` by a finite subset of `O'`. -/
noncomputable abbrev Lf (s : Finset O') : IntermediateField K K' :=
  IntermediateField.adjoin K ((fun x : O' => (x : K')) '' (s : Set O'))

variable [Algebra.IsSeparable K K']

instance (s : Finset O') : FiniteDimensional K (Lf K O' s) :=
  IntermediateField.finiteDimensional_adjoin
    (fun x _ => (Algebra.IsSeparable.isSeparable K x).isIntegral)

instance (s : Finset O') : Algebra.IsSeparable K (Lf K O' s) :=
  Algebra.IsSeparable.of_algHom K K' (Lf K O' s).val

variable (O K) in
/-- The integral closure of `O` in `L`. -/
noncomputable abbrev Df (s : Finset O') : Subalgebra O (Lf K O' s) := integralClosure O (Lf K O' s)

instance (s : Finset O') : IsScalarTower O (Lf K O' s) K' :=
  IsScalarTower.of_algebraMap_eq (fun x => rfl)

instance (s : Finset O') : Module.Finite O (Df O K O' s) :=
  IsIntegralClosure.finite O K (Lf K O' s) (Df O K O' s)

instance (s : Finset O') : IsDedekindDomain (Df O K O' s) :=
  integralClosure.isDedekindDomain O K (Lf K O' s)

variable (K) in
include K in
theorem algebraMap_injective_OK' : Function.Injective (algebraMap O K') := by
  rw [IsScalarTower.algebraMap_eq O K K']
  exact (algebraMap K K').injective.comp (IsFractionRing.injective O K)

theorem coe_algebraMap_Df (s : Finset O') (a : O) :
    (((algebraMap O (Df O K O' s) a : Lf K O' s)) : K') = algebraMap O K' a :=
  (IsScalarTower.algebraMap_apply O (Lf K O' s) K' a).symm

instance (s : Finset O') : Module.IsTorsionFree O (Df O K O' s) := by
  rw [Module.isTorsionFree_iff_algebraMap_injective]
  intro a b h
  have h2 := congrArg (fun x : Df O K O' s => ((x : Lf K O' s) : K')) h
  simp only [coe_algebraMap_Df] at h2
  exact algebraMap_injective_OK' K h2

instance (s : Finset O') : Module.Flat O (Df O K O' s) := inferInstance

instance (s : Finset O') : Algebra.FinitePresentation O (Df O K O' s) :=
  Algebra.FinitePresentation.of_finiteType.mp inferInstance

variable (O K) in
/-- `D → O'`. -/
noncomputable def ι (s : Finset O') : Df O K O' s →+* O' :=
  ((algebraMap (Lf K O' s) K').comp (Df O K O' s).val.toRingHom).codRestrict O'.toSubring
    (fun x => mem_of_isIntegral (O := O) O' (by
      have := x.2
      exact (IsIntegral.map (IsScalarTower.toAlgHom O (Lf K O' s) K') this :)))

theorem coe_ι (s : Finset O') (x : Df O K O' s) : (ι O K O' s x : K') = ((x : Lf K O' s) : K') := rfl

theorem ι_injective (s : Finset O') : Function.Injective (ι O K O' s) := by
  intro x y h
  have h2 := congrArg (fun z : O' => (z : K')) h
  simp only [coe_ι] at h2
  exact Subtype.ext (Subtype.ext h2)

theorem ι_algebraMap (s : Finset O') (a : O) : ι O K O' s (algebraMap O _ a) = algebraMap O O' a := by
  apply Subtype.ext
  rw [coe_ι, coe_algebraMap_Df]
  exact IsScalarTower.algebraMap_apply O O' K' a

variable [IsLocalHom (algebraMap O O')]
  (hunr : ∀ π : O, Irreducible π → Irreducible (algebraMap O O' π))

variable (O K) in
/-- `𝔫 = 𝔪' ∩ D`. -/
noncomputable abbrev nI (s : Finset O') : Ideal (Df O K O' s) := (maximalIdeal O').comap (ι O K O' s)

instance (s : Finset O') : (nI O K O' s).IsPrime := Ideal.comap_isPrime _ _

theorem ι_comp_algebraMap (s : Finset O') :
    (ι O K O' s).comp (algebraMap O (Df O K O' s)) = algebraMap O O' :=
  RingHom.ext (ι_algebraMap O' s)

instance (s : Finset O') : (nI O K O' s).LiesOver (maximalIdeal O) := by
  constructor
  rw [Ideal.under, Ideal.comap_comap, ι_comp_algebraMap]
  exact Ideal.LiesOver.over

include hunr in
theorem algebraMap_mem_nI (s : Finset O') (π : O) (hπ : Irreducible π) :
    algebraMap O (Df O K O' s) π ∈ nI O K O' s := by
  show ι O K O' s (algebraMap O _ π) ∈ maximalIdeal O'
  rw [ι_algebraMap]
  exact (IsLocalRing.mem_maximalIdeal _).mpr (hunr π hπ).not_isUnit

theorem algebraMap_Df_injective (s : Finset O') : Function.Injective (algebraMap O (Df O K O' s)) := by
  intro a b h
  have h2 := congrArg (fun x : Df O K O' s => ((x : Lf K O' s) : K')) h
  simp only [coe_algebraMap_Df] at h2
  exact algebraMap_injective_OK' K h2

include hunr in
theorem nI_ne_bot (s : Finset O') : nI O K O' s ≠ ⊥ := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  intro h
  have h1 := algebraMap_mem_nI (K := K) O' hunr s π hπ
  rw [h, Ideal.mem_bot, ← map_zero (algebraMap O (Df O K O' s))] at h1
  exact hπ.ne_zero (algebraMap_Df_injective O' s h1)

variable (O K) in
/-- `D_𝔫`. -/
abbrev Dn (s : Finset O') : Type := Localization.AtPrime (nI O K O' s)

include hunr in
theorem isDVR_Dn (s : Finset O') : IsDiscreteValuationRing (Dn O K O' s) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (Df O K O' s) (nI_ne_bot O' hunr s) _

variable (O K) in
/-- `ψ : D_𝔫 → O'`. -/
noncomputable def ψ (s : Finset O') : Dn O K O' s →+* O' :=
  IsLocalization.lift (M := (nI O K O' s).primeCompl) (S := Dn O K O' s) (g := ι O K O' s)
    (fun y => IsLocalRing.notMem_maximalIdeal.mp y.2)

theorem ψ_algebraMap (s : Finset O') (x : Df O K O' s) :
    ψ O K O' s (algebraMap _ (Dn O K O' s) x) = ι O K O' s x :=
  IsLocalization.lift_eq _ _

theorem ψ_algebraMap_O (s : Finset O') (a : O) :
    ψ O K O' s (algebraMap O (Dn O K O' s) a) = algebraMap O O' a := by
  rw [IsScalarTower.algebraMap_apply O (Df O K O' s) (Dn O K O' s), ψ_algebraMap, ι_algebraMap]

theorem ψ_mk' (s : Finset O') (c : Df O K O' s) (t : (nI O K O' s).primeCompl) :
    ψ O K O' s (IsLocalization.mk' (Dn O K O' s) c t) * ι O K O' s t = ι O K O' s c := by
  rw [← ψ_algebraMap, ← ψ_algebraMap, ← map_mul, IsLocalization.mk'_spec]

instance isLocalHom_ψ (s : Finset O') : IsLocalHom (ψ O K O' s) := by
  constructor
  intro z hz
  obtain ⟨⟨c, t⟩, rfl⟩ := IsLocalization.mk'_surjective (nI O K O' s).primeCompl z
  rw [IsLocalization.AtPrime.isUnit_mk'_iff]
  intro hc
  have h1 := ψ_mk' (O := O) (K := K) O' s c t
  have h2 : IsUnit (ι O K O' s c) := by
    rw [← h1]; exact hz.mul (IsLocalRing.notMem_maximalIdeal.mp t.2)
  exact (IsLocalRing.mem_maximalIdeal _).mp hc h2

theorem isLocalHom_algebraMap_Dn (s : Finset O') : IsLocalHom (algebraMap O (Dn O K O' s)) := by
  constructor
  intro a ha
  have h1 := ha.map (ψ O K O' s)
  rw [ψ_algebraMap_O] at h1
  exact IsLocalHom.map_nonunit _ h1

variable (O K) in
/-- `ψ` as an `O`-algebra map. -/
noncomputable def ψa (s : Finset O') : Dn O K O' s →ₐ[O] O' :=
  { ψ O K O' s with commutes' := ψ_algebraMap_O (O := O) (K := K) O' s }

instance (s : Finset O') : IsLocalHom (ψa O K O' s) := ⟨(isLocalHom_ψ (O := O) (K := K) O' s).map_nonunit⟩

variable [Algebra.IsSeparable (ResidueField O) (ResidueField O')]

include hunr in
theorem isUnramifiedAt_nI (s : Finset O') : Algebra.IsUnramifiedAt O (nI O K O' s) := by
  haveI := isDVR_Dn (O := O) (K := K) O' hunr s
  haveI := isLocalHom_algebraMap_Dn (O := O) (K := K) O' s
  haveI : Algebra.IsSeparable (ResidueField O) (ResidueField (Dn O K O' s)) :=
    Algebra.IsSeparable.of_algHom _ (ResidueField O') (ResidueField.mapAlgHom' (ψa O K O' s))
  haveI : Algebra.EssFiniteType O (Dn O K O' s) := inferInstance
  apply Algebra.FormallyUnramified.of_map_maximalIdeal
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ, Ideal.map_span, Set.image_singleton]
  refine ((IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp ?_).symm
  apply Irreducible.of_map (f := ψ O K O' s)
  rw [ψ_algebraMap_O]
  exact hunr π hπ

include hunr in
theorem exists_etale_away (s : Finset O') :
    ∃ f ∉ nI O K O' s, Algebra.Etale O (Localization.Away f) := by
  haveI := isUnramifiedAt_nI (O := O) (K := K) O' hunr s
  haveI : Algebra.IsEtaleAt O (nI O K O' s) := Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat _
  exact Algebra.exists_etale_of_isEtaleAt _

include hunr in
theorem exists_rep (s : Finset O') (x : O') (hx : x ∈ s) :
    ∃ (c t : Df O K O' s), t ∉ nI O K O' s ∧ x * ι O K O' s t = ι O K O' s c := by
  by_cases hx0 : x = 0
  · exact ⟨0, 1, fun h => (Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one _).mpr h),
      by rw [hx0, zero_mul, map_zero]⟩
  haveI := isDVR_Dn (O := O) (K := K) O' hunr s
  haveI : IsFractionRing (Df O K O' s) (Lf K O' s) :=
    IsIntegralClosure.isFractionRing_of_finite_extension O K (Lf K O' s) (Df O K O' s)
  have hxL : (x : K') ∈ Lf K O' s := IntermediateField.subset_adjoin K _ ⟨x, hx, rfl⟩
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := Df O K O' s) (⟨x, hxL⟩ : Lf K O' s)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hιb : ι O K O' s b ≠ 0 := by
    rw [← map_zero (ι O K O' s)]; exact fun h => hb0 (ι_injective (O := O) (K := K) O' s h)
  have hab' : ι O K O' s a = x * ι O K O' s b := by
    have hbL : algebraMap (Df O K O' s) (Lf K O' s) b ≠ 0 := by
      rw [← map_zero (algebraMap (Df O K O' s) (Lf K O' s))]
      exact fun h => hb0 (IsFractionRing.injective _ _ h)
    rw [div_eq_iff hbL] at hab
    apply Subtype.ext
    have := congrArg (fun z : Lf K O' s => (z : K')) hab
    change ((a : Lf K O' s) : K') = (x : K') * ((b : Lf K O' s) : K')
    simpa using this
  have hιa : ι O K O' s a ≠ 0 := by rw [hab']; exact mul_ne_zero hx0 hιb
  haveI : IsDomain (Dn O K O' s) :=
    IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors _)
  have hVR : ValuationRing (Dn O K O' s) := inferInstance
  -- `β ∣ α` in the valuation ring `D_𝔫`
  obtain ⟨δ, hδ⟩ : ∃ δ : Dn O K O' s,
      algebraMap _ (Dn O K O' s) b * δ = algebraMap _ (Dn O K O' s) a := by
    rcases hVR.cond'
      (algebraMap _ (Dn O K O' s) a) (algebraMap _ (Dn O K O' s) b) with
      ⟨γ, h | h⟩
    · have h1 := congrArg (ψ O K O' s) h
      rw [map_mul, ψ_algebraMap, ψ_algebraMap] at h1
      have h2 : x * ψ O K O' s γ = 1 := by
        apply mul_left_cancel₀ hιa
        calc ι O K O' s a * (x * ψ O K O' s γ) = x * (ι O K O' s a * ψ O K O' s γ) := by ring
          _ = x * ι O K O' s b := by rw [h1]
          _ = ι O K O' s a * 1 := by rw [mul_one, hab']
      have hγ : IsUnit γ :=
        (IsLocalHom.map_nonunit (f := ψ O K O' s) γ (IsUnit.of_mul_eq_one_right x h2))
      obtain ⟨u, rfl⟩ := hγ
      refine ⟨↑u⁻¹, ?_⟩
      rw [← h, mul_assoc, Units.mul_inv, mul_one]
    · exact ⟨γ, h⟩
  obtain ⟨⟨c, t⟩, rfl⟩ := IsLocalization.mk'_surjective (nI O K O' s).primeCompl δ
  refine ⟨c, t, t.2, ?_⟩
  have h1 := congrArg (ψ O K O' s) hδ
  rw [map_mul, ψ_algebraMap, ψ_algebraMap] at h1
  have hψ : ψ O K O' s (IsLocalization.mk' (Dn O K O' s) c t) = x := by
    apply mul_left_cancel₀ hιb
    rw [h1, hab', mul_comm]
  rw [← hψ]
  exact ψ_mk' (O := O) (K := K) O' s c t

variable (O K) in
/-- `ι` as an `O`-algebra map. -/
noncomputable def ιa (s : Finset O') : Df O K O' s →ₐ[O] O' :=
  { ι O K O' s with commutes' := ι_algebraMap (O := O) (K := K) O' s }

variable (K) in
include K hunr in
/-- **Ind-étaleness.** Every finite subset of `O'` lies in an `O`-subalgebra of `O'` étale over `O`. -/
theorem exists_etale_subalgebra (s : Finset O') :
    ∃ B : Subalgebra O O', Algebra.Etale O B ∧ (s : Set O') ⊆ B := by
  classical
  obtain ⟨f, hf, hfe⟩ := exists_etale_away (O := O) (K := K) O' hunr s
  choose c t ht hct using fun x : s => exists_rep (O := O) (K := K) O' hunr s x.1 x.2
  let P := (nI O K O' s).primeCompl
  let h : Df O K O' s := f * ∏ x : s, t x
  have hP : h ∈ P := P.mul_mem hf (Submonoid.prod_mem P (fun x _ => ht x))
  -- `D[1/h]` is étale over `O`
  haveI : Algebra.Etale O (Localization.Away h) := by
    rw [← Algebra.basicOpen_subset_etaleLocus_iff_etale]
    exact (show (PrimeSpectrum.basicOpen h : Set (PrimeSpectrum (Df O K O' s))) ⊆
      PrimeSpectrum.basicOpen f from PrimeSpectrum.basicOpen_mul_le_left f _).trans
      (Algebra.basicOpen_subset_etaleLocus_iff_etale.mpr hfe)
  have hunit : ∀ y : Submonoid.powers h, IsUnit (ιa O K O' s y) := by
    rintro ⟨_, n, rfl⟩
    exact (IsLocalRing.notMem_maximalIdeal.mp hP).pow n
  let φ : Localization.Away h →ₐ[O] O' := IsLocalization.liftAlgHom hunit
  have hφ : ∀ z : Df O K O' s, φ (algebraMap _ _ z) = ι O K O' s z :=
    fun z => IsLocalization.lift_eq _ _
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers h) z
    have h1 := congrArg φ (IsLocalization.mk'_spec (Localization.Away h) a b)
    rw [map_mul, hz, zero_mul, hφ] at h1
    have ha : a = 0 := ι_injective (O := O) (K := K) O' s (by rw [← h1, map_zero])
    show IsLocalization.mk' (Localization.Away h) a b = 0
    rw [ha, IsLocalization.mk'_zero]
  refine ⟨φ.range, Algebra.Etale.of_equiv (A := Localization.Away h) (B := φ.range)
    (AlgEquiv.ofInjective φ hinj), ?_⟩
  intro x hx
  let xs : s := ⟨x, hx⟩
  have htu : IsUnit (algebraMap _ (Localization.Away h) (t xs)) :=
    isUnit_of_dvd_unit (map_dvd _
      (Dvd.dvd.mul_left (Finset.dvd_prod_of_mem t (Finset.mem_univ xs)) f))
      (IsLocalization.Away.algebraMap_isUnit h)
  obtain ⟨u, hu⟩ := htu
  refine ⟨algebraMap _ _ (c xs) * ↑u⁻¹, ?_⟩
  have hιt : ι O K O' s (t xs) ≠ 0 := by
    intro h0
    exact (IsLocalRing.notMem_maximalIdeal.mp (ht xs)).ne_zero h0
  have e1 : φ ↑u = ι O K O' s (t xs) := by rw [hu, hφ]
  have key : φ (algebraMap _ _ (c xs) * ↑u⁻¹) = x := by
    apply mul_left_cancel₀ hιt
    calc ι O K O' s (t xs) * φ (algebraMap _ _ (c xs) * ↑u⁻¹)
        = φ ↑u * φ (algebraMap _ _ (c xs) * ↑u⁻¹) := by rw [e1]
      _ = φ (↑u * (algebraMap _ _ (c xs) * ↑u⁻¹)) := (map_mul φ _ _).symm
      _ = φ (algebraMap _ _ (c xs)) := by
          congr 1; rw [mul_comm, mul_assoc, Units.inv_mul, mul_one]
      _ = ι O K O' s (c xs) := hφ _
      _ = ι O K O' s (t xs) * x := by rw [← hct xs, mul_comm]
  exact key

end KeyLemma



end NeronSH

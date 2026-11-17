import ZInQKernel.Contrib.OneProof.StrictHenselizationPair
import ZInQKernel.Contrib.OneProof.BLRLocalizes

/-!
# `neronBaseChangeStrictHenselization` and BLR 7.2 Thm. 1, proved (task neron-sh-proof)

`GapSHPair.NeronBaseChangeStrictHenselization` (field `neronBaseChangeStrictHenselization`; BLR §1.2 Prop. 2:
Néron models commute with strict henselization) is proved here from Mathlib and the tree, with no new leaf, via
the stronger chain statement `ReductGlue.NeronBaseChangeUnramifiedDVR` (BLR §7.2 Thm. 1 form: base change along
an extension of DVRs `O ⊆ O'` with `K'/K` separable algebraic, ramification index 1, separable residue extension).

* **Part A (commutative algebra, Mathlib only).** `NeronSH.exists_etale_subalgebra`: such an `O'` is ind-étale
  over `O`: every finite subset `s ⊆ O'` lies in an `O`-subalgebra of `O'` étale over `O`. `D` = integral closure
  of `O` in `L = K(s)` (finite, Dedekind, flat); `𝔫 = 𝔪' ∩ D`; `D_𝔫` is a DVR unramified over `O`
  (`Algebra.FormallyUnramified.of_map_maximalIdeal`), so `D` is étale at `𝔫`
  (`Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat`) and `D[1/f]` is étale; each `x ∈ s` is `c/t` with `t ∉ 𝔫`
  (valuation-ring argument in `D_𝔫`); the subalgebra is the image of `D[1/(f ∏ t)]`. Strict henselianity is not
  used.
* **Part B (algebraic geometry).** `NeronSH.isNeronModelOver_indSmooth`: if every finite subset of `R₁` lies in a
  smooth `R`-subalgebra, `R₁ ↪ K₁` and `Spec K₁ = Spec R₁ ×_R Spec K`, the base change of a Néron model
  (`CToPrinted.IsNeronModelOver`) over `R` is a Néron model over `R₁`. `Spec R₁ = lim Spec B` over the smooth
  subalgebras `B` (a directed set); a smooth affine `R₁`-scheme `V` spreads out to a smooth `W` over some `Spec Bᵢ`
  (EGA IV 8.8.2 (ii), 17.7.8 (ii), proved in `ZInQKernel/Contrib/CloudW01Spread`); a morphism `V_{K₁} → X` descends
  to some `(Spec Bⱼ ×_{Bᵢ} W) ×_R K` (Mathlib's `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`);
  that stage is smooth over `R`, so the Néron property over `R` extends it; uniqueness and gluing are gt-blr's
  `GapBLR.uqA`, `GapBLR.glue_cover`.
* **Part C.** `K'` is the localization of `O'` at the image of `O ∖ 0` (a uniformizer of `O` stays one in `O'`),
  hence the pullback square; `neronBaseChangeUnramifiedDVR_proof` and the field
  `neronBaseChangeStrictHenselization_proof`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open IsLocalRing
open CategoryTheory Limits AlgebraicGeometry

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

namespace NeronSH

/-! ## `Spec R₁ = lim Spec Bᵢ` for a directed family of subalgebras with union `R₁` -/

section Family

variable {R R₁ : Type} [CommRing R] [CommRing R₁] [Algebra R R₁]
  {ι : Type} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] (B : ι → Subalgebra R R₁) (hB : Monotone B)

/-- The inclusion `Bᵢ → Bⱼ`. -/
noncomputable def incl {i j : ι} (h : i ≤ j) : B i →+* B j := (Subalgebra.inclusion (hB h)).toRingHom

theorem incl_val {i j : ι} (h : i ≤ j) (x : B i) : ((incl B hB h x : B j) : R₁) = x := rfl

/-- The diagram `i ↦ Bᵢ`. -/
noncomputable def ringDiag : ι ⥤ CommRingCat.{0} where
  obj i := CommRingCat.of (B i)
  map f := CommRingCat.ofHom (incl B hB (leOfHom f))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- `R₁` as a cocone. -/
noncomputable def ringCocone : Cocone (ringDiag B hB) where
  pt := CommRingCat.of R₁
  ι := { app i := CommRingCat.ofHom (B i).val.toRingHom
         naturality _ _ _ := rfl }

/-- **`R₁ = colim Bᵢ`.** -/
noncomputable def ringCoconeIsColimit (hcov : ∀ x : R₁, ∃ i, x ∈ B i) :
    IsColimit (ringCocone B hB) := by
  haveI : ReflectsColimit (ringDiag B hB) (forget CommRingCat) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  refine isColimitOfReflects (forget CommRingCat) (Types.FilteredColimit.isColimitOf' _ _ ?_ ?_)
  · intro (x : R₁)
    obtain ⟨i, hi⟩ := hcov x
    exact ⟨i, (⟨x, hi⟩ : B i), rfl⟩
  · intro i x y h
    refine ⟨i, 𝟙 i, ?_⟩
    have : (x : B i) = y := Subtype.ext h
    rw [this]

/-- The diagram `i ↦ Spec Bᵢ`. -/
noncomputable def specDiag : ιᵒᵖ ⥤ Scheme.{0} where
  obj i := Spec (CommRingCat.of (B i.unop))
  map f := Spec.map (CommRingCat.ofHom (incl B hB (leOfHom f.unop)))
  map_id i := by rw [← Spec.map_id]; rfl
  map_comp f g := by rw [← Spec.map_comp]; rfl

/-- `Spec R₁` as a cone. -/
noncomputable def specCone : Cone (specDiag B hB) where
  pt := Spec (CommRingCat.of R₁)
  π :=
    { app i := Spec.map (CommRingCat.ofHom (B i.unop).val.toRingHom)
      naturality i j f := by
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, specDiag]
        rw [← Spec.map_comp]
        rfl }

theorem specCone_π_app (i : ιᵒᵖ) :
    (specCone B hB).π.app i = Spec.map (CommRingCat.ofHom (B i.unop).val.toRingHom) := rfl

/-- **`Spec R₁ = lim Spec Bᵢ`.** -/
noncomputable def specConeIsLimit (hcov : ∀ x : R₁, ∃ i, x ∈ B i) : IsLimit (specCone B hB) := by
  have h := isLimitOfPreserves Scheme.Spec (ringCoconeIsColimit B hB hcov).op
  refine (IsLimit.equivOfNatIsoOfIso (NatIso.ofComponents (fun _ => Iso.refl _) ?_) _ _
    (Cone.ext (Iso.refl _) ?_)) h
  · intro m n f
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · intro n
    simp only [Iso.refl_hom, Category.id_comp]

instance specDiag_isAffineHom {i j : ιᵒᵖ} (f : i ⟶ j) : IsAffineHom ((specDiag B hB).map f) :=
  show IsAffineHom (Spec.map _) from inferInstance

instance specDiag_compactSpace (i : ιᵒᵖ) : CompactSpace ((specDiag B hB).obj i) :=
  show CompactSpace (Spec _) from inferInstance

instance specDiag_quasiSeparatedSpace (i : ιᵒᵖ) :
    QuasiSeparatedSpace ((specDiag B hB).obj i) :=
  show QuasiSeparatedSpace (Spec _) from inferInstance

/-- `Spec Bᵢ → Spec R`. -/
noncomputable def ej (i : ιᵒᵖ) : (specDiag B hB).obj i ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (B i.unop)))

theorem smooth_ej (i : ιᵒᵖ) [Algebra.Smooth R (B i.unop)] : Smooth (ej B hB i) := by
  have : Smooth (Spec.map (CommRingCat.ofHom (algebraMap R (B i.unop)))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    exact RingHom.smooth_algebraMap.mpr inferInstance
  exact this

theorem π_ej (i : ιᵒᵖ) : (specCone B hB).π.app i ≫ ej B hB i =
    Spec.map (CommRingCat.ofHom (algebraMap R R₁)) := by
  refine (Spec.map_comp (CommRingCat.ofHom (algebraMap R (B i.unop)))
    (CommRingCat.ofHom (B i.unop).val.toRingHom)).symm.trans ?_
  rfl

theorem map_ej {i j : ιᵒᵖ} (f : i ⟶ j) : (specDiag B hB).map f ≫ ej B hB j = ej B hB i := by
  refine (Spec.map_comp (CommRingCat.ofHom (algebraMap R (B j.unop)))
    (CommRingCat.ofHom (incl B hB (leOfHom f.unop)))).symm.trans ?_
  rfl

open ZInQ.Contrib.SpreadOut in
/-- **Spreading out** (EGA IV 8.8.2 (ii), 17.7.8 (ii), proved in the tree): a smooth affine `R₁`-scheme is the base
change of a smooth scheme over some `Spec Bᵢ`. -/
theorem exists_spread (hcov : ∀ x : R₁, ∃ i, x ∈ B i) (V : Scheme.{0}) [IsAffine V]
    (v : V ⟶ Spec (CommRingCat.of R₁)) [Smooth v] :
    ∃ (a : ιᵒᵖ) (W : Over ((specDiag B hB).obj a)) (φ : V ⟶ W.left),
      Smooth W.hom ∧ QuasiCompact W.hom ∧ QuasiSeparated W.hom ∧
        IsPullback φ v W.hom ((specCone B hB).π.app a) := by
  haveI : IsAffineHom v := inferInstance
  haveI : LocallyOfFinitePresentation (Over.mk v).hom := (inferInstance : LocallyOfFinitePresentation v)
  haveI : QuasiCompact (Over.mk v).hom := (inferInstance : QuasiCompact v)
  haveI : QuasiSeparated (Over.mk v).hom := (inferInstance : QuasiSeparated v)
  obtain ⟨i, Xi, hl, hq, hs, ⟨e⟩⟩ := EGAIV_8_8_2_ii_proof ι (specDiag B hB) (specCone B hB)
    (specConeIsLimit B hB hcov) (Over.mk v) (inferInstance : LocallyOfFinitePresentation v)
    (inferInstance : QuasiCompact v) (inferInstance : QuasiSeparated v)
  haveI : Smooth (Over.mk v).hom := ‹Smooth v›
  have hsm : Smooth ((Over.pullback ((specCone B hB).π.app i)).obj Xi).hom :=
    @smooth_of_iso _ _ (Over.mk v) e ‹Smooth v›
  obtain ⟨j, a, hj⟩ := EGAIV_17_7_8_ii_proof ι (specDiag B hB) (specCone B hB)
    (specConeIsLimit B hB hcov) i Xi hl hq hs hsm
  have hw : e.inv.left ≫ pullback.snd Xi.hom ((specCone B hB).π.app i) = v := Over.w e.inv
  have hπ : (specCone B hB).π.app j ≫ (specDiag B hB).map a = (specCone B hB).π.app i :=
    (specCone B hB).w a
  have hc0 : (e.inv.left ≫ pullback.fst Xi.hom ((specCone B hB).π.app i)) ≫ Xi.hom =
      v ≫ (specCone B hB).π.app i := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hw]
    exact rfl
  have hcomm : (e.inv.left ≫ pullback.fst Xi.hom ((specCone B hB).π.app i)) ≫ Xi.hom =
      (v ≫ (specCone B hB).π.app j) ≫ (specDiag B hB).map a :=
    hc0.trans ((congrArg (fun t => v ≫ t) hπ.symm).trans (Category.assoc _ _ _).symm)
  let φ : V ⟶ pullback Xi.hom ((specDiag B hB).map a) := pullback.lift _ _ hcomm
  refine ⟨j, (Over.pullback ((specDiag B hB).map a)).obj Xi, φ, hj,
    show QuasiCompact (pullback.snd Xi.hom _) from inferInstance,
    show QuasiSeparated (pullback.snd Xi.hom _) from inferInstance, ?_⟩
  have houter : IsPullback (e.inv.left ≫ pullback.fst Xi.hom ((specCone B hB).π.app i)) v Xi.hom
      ((specCone B hB).π.app i) :=
    IsPullback.of_iso_pullback ⟨hc0⟩ ((Over.forget _).mapIso e.symm) rfl hw
  have h1 : φ ≫ pullback.fst _ _ = e.inv.left ≫ pullback.fst Xi.hom ((specCone B hB).π.app i) :=
    pullback.lift_fst _ _ _
  refine IsPullback.of_right (h₁₂ := pullback.fst Xi.hom ((specDiag B hB).map a))
    (h₂₂ := (specDiag B hB).map a) ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  rw [h1]; erw [hπ]; exact houter

end Family


/-! ## The diagram over a fixed stage `Spec C` -/

section OverDiag

variable {R R₁ : Type} [CommRing R] [CommRing R₁] [Algebra R R₁]
  {ι : Type} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] (B : ι → Subalgebra R R₁) (hB : Monotone B)
  (C : Subalgebra R R₁) (hC : ∀ i, C ≤ B i)

/-- `Spec Bᵢ → Spec C`. -/
noncomputable def toC (i : ιᵒᵖ) : (specDiag B hB).obj i ⟶ Spec (CommRingCat.of C) :=
  Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (hC i.unop)).toRingHom)

theorem map_toC {i j : ιᵒᵖ} (f : i ⟶ j) :
    (specDiag B hB).map f ≫ toC B hB C hC j = toC B hB C hC i := by
  refine (Spec.map_comp _ _).symm.trans ?_
  rfl

/-- `i ↦ (Spec Bᵢ → Spec C)`. -/
noncomputable def oD : ιᵒᵖ ⥤ Over (Spec (CommRingCat.of C)) where
  obj i := Over.mk (toC B hB C hC i)
  map f := Over.homMk ((specDiag B hB).map f) (map_toC B hB C hC f)
  map_id i := by ext1; exact (specDiag B hB).map_id i
  map_comp f g := by ext1; exact (specDiag B hB).map_comp f g

/-- `Spec R₁ → Spec C`. -/
noncomputable abbrev πC : Spec (CommRingCat.of R₁) ⟶ Spec (CommRingCat.of C) :=
  Spec.map (CommRingCat.ofHom C.val.toRingHom)

theorem π_toC (i : ιᵒᵖ) : (specCone B hB).π.app i ≫ toC B hB C hC i = πC C := by
  refine (Spec.map_comp _ _).symm.trans ?_
  rfl

/-- `Spec R₁ → Spec Bᵢ` (explicitly typed). -/
noncomputable abbrev πB (i : ιᵒᵖ) : Spec (CommRingCat.of R₁) ⟶ (specDiag B hB).obj i :=
  Spec.map (CommRingCat.ofHom (B i.unop).val.toRingHom)

theorem πB_toC (i : ιᵒᵖ) : πB B hB i ≫ toC B hB C hC i = πC C := by
  refine (Spec.map_comp _ _).symm.trans ?_
  rfl

theorem πB_ej (i : ιᵒᵖ) : πB B hB i ≫ ej B hB i = Spec.map (CommRingCat.ofHom (algebraMap R R₁)) := by
  refine (Spec.map_comp _ _).symm.trans ?_
  rfl

/-- `Spec R₁` as a cone over `oD`. -/
noncomputable def oC : Cone (oD B hB C hC) where
  pt := Over.mk (πC C)
  π := { app i := Over.homMk ((specCone B hB).π.app i) (π_toC B hB C hC i)
         naturality i j f := by ext1; exact (specCone B hB).π.naturality f }

/-- `Spec R₁ = lim Spec Bᵢ` in `Over (Spec C)`. -/
noncomputable def oCIsLimit (hcov : ∀ x : R₁, ∃ i, x ∈ B i) : IsLimit (oC B hB C hC) := by
  haveI : IsConnected ιᵒᵖ := IsCofiltered.isConnected _
  apply isLimitOfReflects (Over.forget _)
  refine (IsLimit.equivOfNatIsoOfIso (NatIso.ofComponents (fun _ => Iso.refl _) ?_) _ _
    (Cone.ext (Iso.refl _) ?_)) (specConeIsLimit B hB hcov)
  · intro m n f
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · intro n
    simp only [Iso.refl_hom, Category.id_comp]

end OverDiag

section PullbackMap

variable {X Y : Scheme.{0}} (f : X ⟶ Y)

/-- The map `(Over.pullback f).map k` is the base change of `k`. -/
theorem isPullback_pullback_map_left {g h : Over Y} (k : g ⟶ h) :
    IsPullback ((Over.pullback f).map k).left (pullback.fst g.hom f) (pullback.fst h.hom f) k.left := by
  refine IsPullback.of_right (h₁₂ := pullback.snd h.hom f) (h₂₂ := h.hom) (v₁₃ := f) ?_ ?_
    (IsPullback.of_hasPullback h.hom f).flip
  · have e1 : ((Over.pullback f).map k).left ≫ pullback.snd h.hom f = pullback.snd g.hom f := by
      simp [Over.pullback_map_left]
    have e2 : k.left ≫ h.hom = g.hom := Over.w k
    rw [e1, e2]
    exact (IsPullback.of_hasPullback g.hom f).flip
  · simp [Over.pullback_map_left]

instance isAffineHom_pullback_map_left {g h : Over Y} (k : g ⟶ h) [IsAffineHom k.left] :
    IsAffineHom ((Over.pullback f).map k).left :=
  MorphismProperty.of_isPullback (isPullback_pullback_map_left f k).flip ‹_›

end PullbackMap

/-! ## Descent of the generic-fibre morphism and the Néron extension -/

section Descend

variable {R R₁ K K₁ : Type} [CommRing R] [CommRing R₁] [Field K] [Field K₁] [Algebra R R₁] [Algebra R K]
  [Algebra R₁ K₁] [Algebra K K₁] [Algebra R K₁] [IsScalarTower R R₁ K₁] [IsScalarTower R K K₁]
  {ι : Type} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] (B : ι → Subalgebra R R₁) (hB : Monotone B)
  (C : Subalgebra R R₁) (hC : ∀ i, C ≤ B i)

theorem πC_eC : πC C ≫ Spec.map (CommRingCat.ofHom (algebraMap R C)) =
    Spec.map (CommRingCat.ofHom (algebraMap R R₁)) := by
  refine (Spec.map_comp _ _).symm.trans ?_
  rfl

theorem toC_eC (i : ιᵒᵖ) : toC B hB C hC i ≫ Spec.map (CommRingCat.ofHom (algebraMap R C)) = ej B hB i := by
  refine (Spec.map_comp _ _).symm.trans ?_
  rfl

theorem specK_comp : Spec.map (CommRingCat.ofHom (algebraMap K K₁)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)) =
    Spec.map (CommRingCat.ofHom (algebraMap R K₁)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

theorem specK₁_comp : Spec.map (CommRingCat.ofHom (algebraMap R₁ K₁)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R R₁)) = Spec.map (CommRingCat.ofHom (algebraMap R K₁)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

include hB hC in
/-- **Descent and extension.** -/
theorem descend_ext (hsm : ∀ i, Algebra.Smooth R (B i)) (hcov : ∀ x : R₁, ∃ i, x ∈ B i)
    (hsq : IsPullback (Spec.map (CommRingCat.ofHom (algebraMap R₁ K₁)))
      (Spec.map (CommRingCat.ofHom (algebraMap K K₁)))
      (Spec.map (CommRingCat.ofHom (algebraMap R R₁))) (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    {X : Over (Spec (CommRingCat.of R))} (hX : CToPrinted.IsNeronModelOver R K X)
    (W : Over (Spec (CommRingCat.of C))) [Smooth W.hom] [QuasiCompact W.hom] [QuasiSeparated W.hom]
    (V : Scheme.{0}) (v : V ⟶ Spec (CommRingCat.of R₁)) (φ : V ⟶ W.left)
    (Hφ : IsPullback φ v W.hom (πC C))
    (b : pullback v (Spec.map (CommRingCat.ofHom (algebraMap R₁ K₁))) ⟶ X.left)
    (hb : b ≫ X.hom = pullback.snd v (Spec.map (CommRingCat.ofHom (algebraMap R₁ K₁))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R K₁))) :
    ∃ g : V ⟶ X.left, g ≫ X.hom = v ≫ Spec.map (CommRingCat.ofHom (algebraMap R R₁)) ∧
      pullback.fst v (Spec.map (CommRingCat.ofHom (algebraMap R₁ K₁))) ≫ g = b := by
  haveI : IsConnected ιᵒᵖ := IsCofiltered.isConnected _
  haveI : Smooth X.hom := hX.1
  let eC : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom (algebraMap R C))
  let jK : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let kK₁ := Spec.map (CommRingCat.ofHom (algebraMap R₁ K₁))
  let D := (oD B hB C hC ⋙ Over.pullback W.hom) ⋙ Over.map (W.hom ≫ eC)
  let cD := (Over.map (W.hom ≫ eC)).mapCone ((Over.pullback W.hom).mapCone (oC B hB C hC))
  have hcD : IsLimit cD := by
    apply isLimitOfReflects (Over.forget _)
    exact isLimitOfPreserves (Over.forget W.left)
      (isLimitOfPreserves (Over.pullback W.hom) (oCIsLimit B hB C hC hcov))
  let E := (D ⋙ Over.pullback jK) ⋙ Over.forget (Spec (CommRingCat.of K))
  let cE := (Over.forget _).mapCone ((Over.pullback jK).mapCone cD)
  have hcE : IsLimit cE := isLimitOfPreserves _ (isLimitOfPreserves _ hcD)
  -- finiteness of the stages
  have hDhom : ∀ j, (D.obj j).hom = pullback.fst (toC B hB C hC j) W.hom ≫ ej B hB j := fun j => by
    change pullback.snd (toC B hB C hC j) W.hom ≫ W.hom ≫ eC = _
    rw [← Category.assoc, ← pullback.condition, Category.assoc, toC_eC]
  haveI : QuasiCompact eC := show QuasiCompact (Spec.map _) from inferInstance
  haveI : QuasiSeparated eC := show QuasiSeparated (Spec.map _) from inferInstance
  haveI : ∀ j, QuasiCompact (D.obj j).hom := fun j => by
    haveI : QuasiCompact (toC B hB C hC j) := show QuasiCompact (Spec.map _) from inferInstance
    haveI : QuasiCompact (pullback.snd (toC B hB C hC j) W.hom) := inferInstance
    change QuasiCompact (pullback.snd (toC B hB C hC j) W.hom ≫ W.hom ≫ eC); infer_instance
  haveI : ∀ j, QuasiSeparated (D.obj j).hom := fun j => by
    haveI : QuasiSeparated (toC B hB C hC j) := show QuasiSeparated (Spec.map _) from inferInstance
    haveI : QuasiSeparated (pullback.snd (toC B hB C hC j) W.hom) := inferInstance
    change QuasiSeparated (pullback.snd (toC B hB C hC j) W.hom ≫ W.hom ≫ eC); infer_instance
  haveI : ∀ j, Smooth (D.obj j).hom := fun j => by
    haveI := hsm j.unop
    haveI := smooth_ej B hB j
    haveI : Smooth (pullback.fst (toC B hB C hC j) W.hom) :=
      MorphismProperty.of_isPullback (IsPullback.of_hasPullback (toC B hB C hC j) W.hom).flip ‹Smooth W.hom›
    rw [hDhom j]
    exact MorphismProperty.comp_mem @Smooth _ _ ‹_› (smooth_ej B hB j)
  haveI : ∀ j, CompactSpace (E.obj j) := fun j => by
    have : CompactSpace ((pullback (D.obj j).hom jK : Scheme.{0})) := inferInstance
    exact this
  haveI : ∀ j, QuasiSeparatedSpace (E.obj j) := fun j =>
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd (D.obj j).hom jK)
  haveI : ∀ {j k : ιᵒᵖ} (f : j ⟶ k), IsAffineHom (E.map f) := fun {j k} f => by
    haveI : IsAffineHom ((oD B hB C hC).map f).left :=
      show IsAffineHom ((specDiag B hB).map f) from inferInstance
    haveI : IsAffineHom ((Over.pullback W.hom).map ((oD B hB C hC).map f)).left :=
      isAffineHom_pullback_map_left W.hom ((oD B hB C hC).map f)
    haveI : IsAffineHom (D.map f).left := ‹IsAffineHom ((Over.pullback W.hom).map ((oD B hB C hC).map f)).left›
    exact isAffineHom_pullback_map_left jK (D.map f)
  -- the apex `cE.pt = (Spec R₁ ×_C W) ×_R K` and the comparison with `V ×_{R₁} K₁`
  let e := Hφ.flip.isoPullback
  have he1 : e.inv ≫ v = pullback.fst (πC C) W.hom := IsPullback.isoPullback_inv_fst _
  have he2 : e.inv ≫ φ = pullback.snd (πC C) W.hom := IsPullback.isoPullback_inv_snd _
  have he3 : e.hom ≫ pullback.fst (πC C) W.hom = v := IsPullback.isoPullback_hom_fst _
  have he4 : e.hom ≫ pullback.snd (πC C) W.hom = φ := IsPullback.isoPullback_hom_snd _
  let h2 : pullback (πC C) W.hom ⟶ Spec (CommRingCat.of R) := pullback.snd (πC C) W.hom ≫ W.hom ≫ eC
  have hh2 : pullback.fst (πC C) W.hom ≫ πC C ≫ eC = h2 := by
    rw [← Category.assoc, pullback.condition, Category.assoc]
  let P : Scheme.{0} := pullback h2 jK
  have hP : (pullback.fst h2 jK ≫ pullback.fst (πC C) W.hom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R R₁)) = pullback.snd h2 jK ≫ jK := by
    rw [← πC_eC C, Category.assoc, hh2, pullback.condition]
  let κ : P ⟶ Spec (CommRingCat.of K₁) := hsq.lift _ _ hP
  have hκ1 : κ ≫ kK₁ = pullback.fst h2 jK ≫ pullback.fst (πC C) W.hom := hsq.lift_fst _ _ _
  have hκ2 : κ ≫ Spec.map (CommRingCat.ofHom (algebraMap K K₁)) = pullback.snd h2 jK :=
    hsq.lift_snd _ _ _
  let α : P ⟶ pullback v kK₁ := pullback.lift (pullback.fst h2 jK ≫ e.inv) κ (by
    rw [Category.assoc, he1, hκ1])
  have hab : (α ≫ b) ≫ X.hom = pullback.snd h2 jK ≫ jK := by
    rw [Category.assoc, hb, ← Category.assoc, pullback.lift_snd, ← specK_comp (R := R) (K := K) (K₁ := K₁),
      ← Category.assoc, hκ2]
  let a : cE.pt ⟶ pullback X.hom jK := (pullback.lift (α ≫ b) (pullback.snd h2 jK) hab : P ⟶ _)
  have ha2 : a ≫ pullback.snd X.hom jK = pullback.snd h2 jK := pullback.lift_snd _ _ _
  let t : E ⟶ (Functor.const _).obj (Spec (CommRingCat.of K)) :=
    NatTrans.mk (fun j => ((Over.pullback jK).obj (D.obj j)).hom) (by
      intro j k f; exact Over.w ((Over.pullback jK).map (D.map f)))
  have ha : cE.π ≫ t = (Functor.const _).map (a ≫ pullback.snd X.hom jK) := by
    ext j
    simp only [NatTrans.comp_app, Functor.const_map_app]
    rw [ha2]
    exact Over.w ((Over.pullback jK).map (cD.π.app j))
  obtain ⟨j, g, hg1, hg2⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation E t
    (pullback.snd X.hom jK) cE hcE a ha
  -- the Néron extension on the stage `Y = Spec Bⱼ ×_C W`
  let Y := D.obj j
  let g' : pullback Y.hom jK ⟶ pullback X.hom jK := g
  have hg2' : g' ≫ pullback.snd X.hom jK = pullback.snd Y.hom jK := hg2
  obtain ⟨f0, hf0, hpf⟩ := GapBLR.neron_ext hX Y (pullback.fst Y.hom jK) (pullback.snd Y.hom jK)
    (IsPullback.of_hasPullback _ _) (g' ≫ pullback.fst X.hom jK)
    (by rw [Category.assoc, pullback.condition, ← Category.assoc, hg2'])
  let f0' : pullback (toC B hB C hC j) W.hom ⟶ X.left := f0
  have hf0' : f0' ≫ X.hom = pullback.fst (toC B hB C hC j) W.hom ≫ ej B hB j := hf0.trans (hDhom j)
  let ψV : V ⟶ pullback (toC B hB C hC j) W.hom :=
    pullback.lift (v ≫ πB B hB j) φ (by rw [Category.assoc, πB_toC, Hφ.w])
  refine ⟨ψV ≫ f0', ?_, ?_⟩
  · rw [Category.assoc, hf0', ← Category.assoc, pullback.lift_fst, Category.assoc, πB_ej]
  -- the inverse comparison `V ×_{R₁} K₁ → P`
  have hβ : (pullback.fst v kK₁ ≫ e.hom) ≫ h2 =
      (pullback.snd v kK₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap K K₁))) ≫ jK := by
    show (pullback.fst v kK₁ ≫ e.hom) ≫ (pullback.snd (πC C) W.hom ≫ W.hom ≫ eC) = _
    rw [Category.assoc, ← Category.assoc e.hom, he4, ← Category.assoc φ, Hφ.w, Category.assoc,
      πC_eC, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc, specK₁_comp,
      specK_comp]
  let β : pullback v kK₁ ⟶ P := pullback.lift _ _ hβ
  have hβ1 : β ≫ pullback.fst h2 jK = pullback.fst v kK₁ ≫ e.hom := pullback.lift_fst _ _ _
  have hβ2 : β ≫ pullback.snd h2 jK = pullback.snd v kK₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap K K₁)) :=
    pullback.lift_snd _ _ _
  have hα1 : α ≫ pullback.fst v kK₁ = pullback.fst h2 jK ≫ e.inv := pullback.lift_fst _ _ _
  have hα2 : α ≫ pullback.snd v kK₁ = κ := pullback.lift_snd _ _ _
  have hβα : β ≫ α = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hα1, ← Category.assoc, hβ1, Category.assoc, e.hom_inv_id, Category.comp_id,
        Category.id_comp]
    · rw [Category.assoc, hα2, Category.id_comp]
      apply hsq.hom_ext
      · rw [Category.assoc, hκ1, ← Category.assoc, hβ1, Category.assoc, he3, pullback.condition]
      · rw [Category.assoc, hκ2, hβ2]
  -- the cone map at `j`
  let cDj : pullback (πC C) W.hom ⟶ pullback (toC B hB C hC j) W.hom :=
    pullback.lift (pullback.fst (πC C) W.hom ≫ πB B hB j) (pullback.snd (πC C) W.hom)
      (by rw [Category.assoc, πB_toC, pullback.condition])
  have hcDj : (cD.π.app j).left = cDj := rfl
  let cEj : P ⟶ pullback Y.hom jK := cE.π.app j
  have hcEj : cEj ≫ pullback.fst Y.hom jK = pullback.fst h2 jK ≫ cDj := by
    have : cEj ≫ pullback.fst Y.hom jK = pullback.fst h2 jK ≫ (cD.π.app j).left :=
      pullback.lift_fst _ _ _
    exact this
  have heψ : e.hom ≫ cDj = ψV := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, he3, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, he4, pullback.lift_snd]
  have k1 : pullback.fst v kK₁ ≫ ψV = β ≫ cEj ≫ pullback.fst Y.hom jK := by
    rw [hcEj, ← heψ, ← Category.assoc]
    exact (congrArg (· ≫ cDj) hβ1.symm).trans (Category.assoc _ _ _)
  have k2 : pullback.fst Y.hom jK ≫ f0' = g' ≫ pullback.fst X.hom jK := hpf
  let a' : P ⟶ pullback X.hom jK := a
  have hg1' : cEj ≫ g' = a' := hg1
  have ha1 : a' ≫ pullback.fst X.hom jK = α ≫ b := pullback.lift_fst _ _ _
  calc pullback.fst v kK₁ ≫ ψV ≫ f0' = (pullback.fst v kK₁ ≫ ψV) ≫ f0' := (Category.assoc _ _ _).symm
    _ = β ≫ cEj ≫ (pullback.fst Y.hom jK ≫ f0') := 
        (congrArg (· ≫ f0') k1).trans ((Category.assoc _ _ _).trans (congrArg (β ≫ ·) (Category.assoc _ _ _)))
    _ = β ≫ (cEj ≫ g') ≫ pullback.fst X.hom jK := by rw [k2, Category.assoc]
    _ = (β ≫ α) ≫ b := by rw [hg1', ha1, Category.assoc]
    _ = b := by rw [hβα, Category.id_comp]

end Descend

/-! ## Ind-smooth algebras -/

/-- **Ind-smoothness**: every finite subset of `R₁` lies in an `R`-subalgebra of `R₁` that is smooth over `R`. -/
def IndSmooth (R R₁ : Type) [CommRing R] [CommRing R₁] [Algebra R R₁] : Prop :=
  ∀ s : Finset R₁, ∃ B : Subalgebra R R₁, Algebra.Smooth R B ∧ (s : Set R₁) ⊆ B

section Index

variable {R R₁ : Type} [CommRing R] [CommRing R₁] [Algebra R R₁]

/-- The smooth `R`-subalgebras of `R₁`. -/
abbrev SIdx (R R₁ : Type) [CommRing R] [CommRing R₁] [Algebra R R₁] : Type :=
  {B : Subalgebra R R₁ // Algebra.Smooth R B}

theorem SIdx.exists_ge (hind : IndSmooth R R₁) (a b : SIdx R R₁) :
    ∃ c : SIdx R R₁, a ≤ c ∧ b ≤ c := by
  classical
  have fg : ∀ x : SIdx R R₁, ∃ t : Finset R₁, Algebra.adjoin R (t : Set R₁) = x.1 := fun x => by
    haveI := x.2
    have h1 : (⊤ : Subalgebra R x.1).FG := Algebra.FiniteType.out
    exact (Subalgebra.fg_top x.1).mp h1
  obtain ⟨ta, hta⟩ := fg a
  obtain ⟨tb, htb⟩ := fg b
  obtain ⟨c, hc, hsub⟩ := hind (ta ∪ tb)
  refine ⟨⟨c, hc⟩, ?_, ?_⟩
  · show a.1 ≤ c
    rw [← hta]
    exact Algebra.adjoin_le (fun x hx => hsub (by simp [hx]))
  · show b.1 ≤ c
    rw [← htb]
    exact Algebra.adjoin_le (fun x hx => hsub (by simp [hx]))

theorem SIdx.isDirected (hind : IndSmooth R R₁) : IsDirectedOrder (SIdx R R₁) :=
  ⟨SIdx.exists_ge hind⟩

theorem SIdx.nonempty (hind : IndSmooth R R₁) : Nonempty (SIdx R R₁) := by
  obtain ⟨B, hB, -⟩ := hind ∅
  exact ⟨⟨B, hB⟩⟩

theorem SIdx.cov (hind : IndSmooth R R₁) (x : R₁) : ∃ i : SIdx R R₁, x ∈ i.1 := by
  obtain ⟨B, hB, hx⟩ := hind {x}
  exact ⟨⟨B, hB⟩, hx (by simp)⟩

theorem SIdx'.isDirected (hind : IndSmooth R R₁) (i : SIdx R R₁) : IsDirectedOrder {j : SIdx R R₁ // i ≤ j} :=
  ⟨fun a b => by
    obtain ⟨c, hac, hbc⟩ := SIdx.exists_ge hind a.1 b.1
    exact ⟨⟨c, le_trans a.2 hac⟩, hac, hbc⟩⟩

theorem SIdx'.cov (hind : IndSmooth R R₁) (i : SIdx R R₁) (x : R₁) :
    ∃ j : {j : SIdx R R₁ // i ≤ j}, x ∈ j.1.1 := by
  obtain ⟨k, hk⟩ := SIdx.cov hind x
  obtain ⟨c, hic, hkc⟩ := SIdx.exists_ge hind i k
  exact ⟨⟨c, hic⟩, hkc hk⟩

end Index

/-! ## The Néron property after ind-smooth base change -/

section Main

variable {R R₁ K K₁ : Type} [CommRing R] [CommRing R₁] [Field K] [Field K₁] [Algebra R R₁] [Algebra R K]
  [Algebra R₁ K₁] [Algebra K K₁] [Algebra R K₁] [IsScalarTower R R₁ K₁] [IsScalarTower R K K₁]

/-- **Local existence** for a smooth affine `R₁`-scheme. -/
theorem local_ext (hind : IndSmooth R R₁)
    (hsq : IsPullback (Spec.map (CommRingCat.ofHom (algebraMap R₁ K₁)))
      (Spec.map (CommRingCat.ofHom (algebraMap K K₁)))
      (Spec.map (CommRingCat.ofHom (algebraMap R R₁))) (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    {X : Over (Spec (CommRingCat.of R))} (hX : CToPrinted.IsNeronModelOver R K X)
    (V : Scheme.{0}) [IsAffine V] (v : V ⟶ Spec (CommRingCat.of R₁)) [Smooth v]
    (b : pullback v (Spec.map (CommRingCat.ofHom (algebraMap R₁ K₁))) ⟶ X.left)
    (hb : b ≫ X.hom = pullback.snd v (Spec.map (CommRingCat.ofHom (algebraMap R₁ K₁))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R K₁))) :
    ∃ g : V ⟶ X.left, g ≫ X.hom = v ≫ Spec.map (CommRingCat.ofHom (algebraMap R R₁)) ∧
      pullback.fst v (Spec.map (CommRingCat.ofHom (algebraMap R₁ K₁))) ≫ g = b := by
  haveI := SIdx.isDirected hind
  haveI := SIdx.nonempty hind
  obtain ⟨i, W, φ, hW, hWq, hWs, Hφ⟩ := exists_spread (B := fun j : SIdx R R₁ => j.1)
    (fun _ _ h => h) (SIdx.cov hind) V v
  let C := i.unop.1
  let W' : Over (Spec (CommRingCat.of C)) := W
  haveI : Smooth W'.hom := hW
  haveI : QuasiCompact W'.hom := hWq
  haveI : QuasiSeparated W'.hom := hWs
  haveI := SIdx'.isDirected hind i.unop
  haveI : Nonempty {j : SIdx R R₁ // i.unop ≤ j} := ⟨⟨i.unop, le_rfl⟩⟩
  exact descend_ext (B := fun j : {j : SIdx R R₁ // i.unop ≤ j} => j.1.1) (fun _ _ h => h) C
    (fun j => j.2) (fun j => j.1.2) (SIdx'.cov hind i.unop) hsq hX W' V v φ Hφ b hb

/-- **Existence of extensions** for an arbitrary smooth `R₁`-scheme. -/
theorem glue_ext (hind : IndSmooth R R₁) (hinj : Function.Injective (algebraMap R₁ K₁))
    (hsq : IsPullback (Spec.map (CommRingCat.ofHom (algebraMap R₁ K₁)))
      (Spec.map (CommRingCat.ofHom (algebraMap K K₁)))
      (Spec.map (CommRingCat.ofHom (algebraMap R R₁))) (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    {X : Over (Spec (CommRingCat.of R))} (hX : CToPrinted.IsNeronModelOver R K X)
    (Y : Scheme.{0}) (y : Y ⟶ Spec (CommRingCat.of R₁)) [Smooth y]
    (b : pullback y (Spec.map (CommRingCat.ofHom (algebraMap R₁ K₁))) ⟶ X.left)
    (hb : b ≫ X.hom = pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R₁ K₁))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R K₁))) :
    ∃ g : Y ⟶ X.left, g ≫ X.hom = y ≫ Spec.map (CommRingCat.ofHom (algebraMap R R₁)) ∧
      pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap R₁ K₁))) ≫ g = b := by
  haveI : IsSeparated X.hom := hX.2.1
  let 𝒰 := Y.affineCover
  have hm : ∀ i, (pullback.lift (pullback.fst (𝒰.f i ≫ y) (Spec.map (CommRingCat.ofHom (algebraMap R₁ K₁))) ≫
      𝒰.f i) (pullback.snd _ _) (by rw [Category.assoc]; exact pullback.condition) ≫ b) ≫ X.hom =
      pullback.snd (𝒰.f i ≫ y) (Spec.map (CommRingCat.ofHom (algebraMap R₁ K₁))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R K₁)) := fun i => by
    rw [Category.assoc, hb, ← Category.assoc, pullback.lift_snd]
  choose g hg1 hg2 using fun i => local_ext hind hsq hX (𝒰.X i) (𝒰.f i ≫ y) _ (hm i)
  exact GapBLR.glue_cover R₁ hinj X _ y b 𝒰 g hg1 hg2

/-- **Néron models commute with ind-smooth base change.** If every finite subset of `R₁` lies in a smooth
`R`-subalgebra and `Spec K₁ = Spec R₁ ×_R Spec K` (with `R₁ ⊆ K₁`), the base change of a Néron model over `R`
is a Néron model over `R₁`. -/
theorem isNeronModelOver_indSmooth (hind : IndSmooth R R₁) (hinj : Function.Injective (algebraMap R₁ K₁))
    (hsq : IsPullback (Spec.map (CommRingCat.ofHom (algebraMap R₁ K₁)))
      (Spec.map (CommRingCat.ofHom (algebraMap K K₁)))
      (Spec.map (CommRingCat.ofHom (algebraMap R R₁))) (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    {X : Over (Spec (CommRingCat.of R))} (hX : CToPrinted.IsNeronModelOver R K X) :
    CToPrinted.IsNeronModelOver R₁ K₁
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))).obj X) := by
  have hX' := hX
  obtain ⟨hsm, hsep, hlft, hqc, -⟩ := hX'
  let jR := Spec.map (CommRingCat.ofHom (algebraMap R R₁))
  let kK := Spec.map (CommRingCat.ofHom (algebraMap R₁ K₁))
  have hk : kK ≫ jR = Spec.map (CommRingCat.ofHom (algebraMap R K₁)) := specK₁_comp
  refine ⟨show Smooth (pullback.snd X.hom jR) from inferInstance,
    show IsSeparated (pullback.snd X.hom jR) from inferInstance,
    show LocallyOfFiniteType (pullback.snd X.hom jR) from inferInstance,
    show QuasiCompact (pullback.snd X.hom jR) from inferInstance, fun Y _ => ⟨?_, ?_⟩⟩
  · intro f₁ f₂ h
    have w₁ : f₁.left ≫ pullback.snd X.hom jR = Y.hom := Over.w f₁
    have w₂ : f₂.left ≫ pullback.snd X.hom jR = Y.hom := Over.w f₂
    have key : f₁.left ≫ pullback.fst X.hom jR = f₂.left ≫ pullback.fst X.hom jR := by
      refine GapBLR.uqA R₁ hinj X Y.hom
        (pullback.fst Y.hom kK) (pullback.snd Y.hom kK) (IsPullback.of_hasPullback _ _) _ _ ?_ ?_
      · rw [Category.assoc, pullback.condition, ← Category.assoc, w₁, Category.assoc, pullback.condition,
          ← Category.assoc, w₂]
      · have h1 := congrArg (fun t => t.left ≫ pullback.fst _ _ ≫ pullback.fst _ _) h
        simpa only [Over.pullback_map_left, pullback.lift_fst_assoc, Category.assoc] using h1
    apply Over.OverMorphism.ext
    exact pullback.hom_ext key (w₁.trans w₂.symm)
  · intro h
    have hw : h.left ≫ pullback.snd (pullback.snd X.hom jR) kK = pullback.snd Y.hom kK := Over.w h
    let a := h.left ≫ pullback.fst (pullback.snd X.hom jR) kK ≫ pullback.fst X.hom jR
    have ha : a ≫ X.hom = pullback.snd Y.hom kK ≫ Spec.map (CommRingCat.ofHom (algebraMap R K₁)) := by
      simp only [a, Category.assoc]
      rw [pullback.condition, pullback.condition_assoc, ← Category.assoc, hw, hk]
    obtain ⟨g, hg1, hg2⟩ := glue_ext hind hinj hsq hX Y.left Y.hom a ha
    refine ⟨Over.homMk (pullback.lift g Y.hom hg1) (pullback.lift_snd _ _ _), ?_⟩
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [Over.pullback_map_left, Over.homMk_left, Category.assoc, pullback.lift_fst]
        exact hg2
      · simp only [Over.pullback_map_left, Over.homMk_left, Category.assoc, pullback.lift_fst,
          pullback.lift_snd]
        exact pullback.condition.trans ((congrArg (· ≫ kK) hw).symm.trans ((Category.assoc _ _ _).trans
          (congrArg (h.left ≫ ·) pullback.condition.symm)))
    · simp only [Over.pullback_map_left, Over.homMk_left, pullback.lift_snd]
      exact hw.symm

end Main

end NeronSH

/-! ## Part C: the chain's `NeronBaseChangeUnramifiedDVR` and the field -/

namespace NeronSH

open ReductSplit ReductGlue

section Final

variable {K K' : Type} [Field K] [Field K'] [Algebra K K'] {O : ValuationSubring K}
  {O' : ValuationSubring K'} (hO : O'.comap (algebraMap K K') = O)

/-- `K' = O' ⊗_O K` (as a localization of `O'` at the image of `O ∖ 0`). -/
theorem isLocalization_K' [IsDiscreteValuationRing O] [IsDiscreteValuationRing O']
    (hunr : ∀ ϖ : O, Irreducible ϖ → Irreducible (comapHom hO ϖ)) :
    letI : Algebra O O' := (comapHom hO).toAlgebra
    IsLocalization (Algebra.algebraMapSubmonoid O' (nonZeroDivisors O)) K' := by
  letI : Algebra O O' := (comapHom hO).toAlgebra
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, a, ha, rfl⟩
    refine isUnit_iff_ne_zero.mpr ?_
    change algebraMap K K' (a : K) ≠ 0
    rw [map_ne_zero]
    exact fun h => nonZeroDivisors.ne_zero ha (Subtype.ext h)
  · intro z
    by_cases hz : z ∈ O'
    · exact ⟨⟨⟨z, hz⟩, 1⟩, by simp⟩
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
    have hπ' := hunr π hπ
    have hz0 : z ≠ 0 := fun h => hz (h ▸ O'.zero_mem)
    have hzi : z⁻¹ ∈ O' := (O'.mem_or_inv_mem z).resolve_left hz
    have hzi0 : (⟨z⁻¹, hzi⟩ : O') ≠ 0 := fun h => inv_ne_zero hz0 (congrArg Subtype.val h)
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hzi0 hπ'
    have hπn : π ^ n ∈ nonZeroDivisors O :=
      mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n hπ.ne_zero)
    refine ⟨⟨(↑u⁻¹ : O'), ⟨algebraMap O O' (π ^ n), π ^ n, hπn, rfl⟩⟩, ?_⟩
    show z * ((comapHom hO (π ^ n) : O') : K') = ((↑u⁻¹ : O') : K')
    rw [map_pow, SubmonoidClass.coe_pow]
    have e1 : z⁻¹ = ((u : O') : K') * ((comapHom hO π : O') : K') ^ n := by
      have := congrArg (fun w : O' => (w : K')) hu
      simpa using this
    have e2 : ((u : O') : K') * ((↑u⁻¹ : O') : K') = 1 := by
      exact congrArg (fun w : O' => (w : K')) u.mul_inv
    calc z * ((comapHom hO π : O') : K') ^ n
        = z * (((↑u⁻¹ : O') : K') * ((u : O') : K') * ((comapHom hO π : O') : K') ^ n) := by
          rw [mul_comm ((↑u⁻¹ : O') : K'), e2, one_mul]
      _ = ((↑u⁻¹ : O') : K') * (z * z⁻¹) := by rw [e1]; ring
      _ = ((↑u⁻¹ : O') : K') := by rw [mul_inv_cancel₀ hz0, mul_one]
  · intro x y h
    exact ⟨1, by rw [Subtype.ext h]⟩

theorem isPullback_spec [IsDiscreteValuationRing O] [IsDiscreteValuationRing O']
    (hunr : ∀ ϖ : O, Irreducible ϖ → Irreducible (comapHom hO ϖ)) :
    letI : Algebra O O' := (comapHom hO).toAlgebra
    IsPullback (Spec.map (CommRingCat.ofHom (algebraMap O' K')))
      (Spec.map (CommRingCat.ofHom (algebraMap K K')))
      (Spec.map (CommRingCat.ofHom (algebraMap O O'))) (Spec.map (CommRingCat.ofHom (algebraMap O K))) := by
  letI : Algebra O O' := (comapHom hO).toAlgebra
  letI : Algebra O K' := ((algebraMap K K').comp (algebraMap O K)).toAlgebra
  haveI : IsScalarTower O O' K' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower O K K' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI := isLocalization_K' hO hunr
  haveI : Algebra.IsPushout O O' K K' := Algebra.isPushout_of_isLocalization (nonZeroDivisors O) K O' K'
  exact isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_iff_isPushout.mpr inferInstance)

end Final

/-- The kernel's Néron property of a group model over a valuation ring is the printed one of its scheme. -/
theorem isNeronModelOver_of_groupModelO {K : Type} [Field K] {A : PkgI3.AbVar K} {O : ValuationSubring K}
    (𝒩 : GroupModelO A O) (h : 𝒩.IsNeronModel) : CToPrinted.IsNeronModelOver O K 𝒩.G := by
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, fun Y _ => ?_⟩
  have hb := h Y
  refine ⟨fun a b hab => hb.1 ?_, fun g => ?_⟩
  · simp only at hab ⊢
    rw [hab]
  · obtain ⟨f, hf⟩ := hb.2 (g ≫ 𝒩.gen.hom)
    refine ⟨f, ?_⟩
    simp only at hf ⊢
    exact (cancel_mono 𝒩.gen.hom).mp hf

/-- **BLR 7.2 Thm. 1, proved** (the chain's `ReductGlue.NeronBaseChangeUnramifiedDVR`): for an extension of DVRs
`O ⊆ O'` with `K'/K` separable algebraic, ramification index `1` and separable residue extension, the base change
of a Néron model is a Néron model. -/
theorem neronBaseChangeUnramifiedDVR_proof : NeronBaseChangeUnramifiedDVR := by
  intro K _ O _ K' _ _ O' _ hO hsep hunr hres A 𝒩 h𝒩
  letI : Algebra O O' := (comapHom hO).toAlgebra
  letI : Algebra O K' := ((algebraMap K K').comp (algebraMap O K)).toAlgebra
  haveI : IsScalarTower O O' K' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower O K K' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsLocalHom (algebraMap O O') := comapHom_isLocalHom hO
  haveI : Algebra.IsSeparable (ResidueField O) (ResidueField O') := by
    have e : (inferInstance : Algebra (ResidueField O) (ResidueField O')) = (resMap hO).toAlgebra := by
      apply Algebra.algebra_ext
      intro x
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
      rw [IsLocalRing.ResidueField.algebraMap_residue]
      exact (resMap_residue hO a).symm
    have h' : @Algebra.IsSeparable _ _ _ _ (resMap hO).toAlgebra := hres
    rwa [← e] at h'
  have hind : IndSmooth O O' := fun s => by
    obtain ⟨B, hB, hs⟩ := exists_etale_subalgebra K O' hunr s
    exact ⟨B, inferInstance, hs⟩
  have hinj : Function.Injective (algebraMap O' K') := Subtype.val_injective
  have h1 := isNeronModelOver_indSmooth hind hinj (isPullback_spec hO hunr)
    (isNeronModelOver_of_groupModelO 𝒩 h𝒩)
  obtain ⟨_, _, _, _, h3⟩ := h1
  intro Y _
  have hb := h3 Y
  refine ⟨fun a b hab => hb.1 ?_, fun g => ?_⟩
  · simp only at hab ⊢
    exact (cancel_mono (bcDVR hO 𝒩).gen.hom).mp hab
  · obtain ⟨f, hf⟩ := hb.2 (g ≫ (bcDVR hO 𝒩).gen.inv)
    refine ⟨f, ?_⟩
    have hf' : (Over.pullback (jO O')).map f = g ≫ (bcDVR hO 𝒩).gen.inv := hf
    exact (congrArg (· ≫ (bcDVR hO 𝒩).gen.hom) hf').trans (by simp)

/-- **The field `neronBaseChangeStrictHenselization`, proved** (BLR §1.2 Prop. 2 / §7.2 Thm. 1). -/
theorem neronBaseChangeStrictHenselization_proof : GapSHPair.NeronBaseChangeStrictHenselization :=
  GapSHPair.neronBaseChangeStrictHenselization_of_unramified neronBaseChangeUnramifiedDVR_proof



end NeronSH

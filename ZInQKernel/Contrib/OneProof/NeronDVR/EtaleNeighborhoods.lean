import ZInQKernel.Contrib.OneProof.NeronDedekind.Near
import ZInQKernel.Contrib.OneProof.NeronBaseChangeStrictHenselization
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Étale DVR neighborhoods in an unramified extension

For a DVR extension preserving uniformizers, with separable fraction and
residue field extensions, the stages `NeronSH.Dn` are étale DVRs. Their images
are an increasing family of subalgebras with union the extension ring. The
base and extension-ring maps are faithfully flat. The corresponding generic
fibres are spectra of fraction fields, with Cartesian squares at both maps.
-/

noncomputable section

open IsLocalRing
open CategoryTheory Limits AlgebraicGeometry

namespace NeronDVR

/-- In a Dedekind domain, inverting an element that vanishes at all maximal
ideals except `p` presents localization at `p`. -/
theorem isLocalizationAway_atPrime_of_maximal
    {D : Type} [CommRing D] [IsDedekindDomain D]
    (p : Ideal D) [p.IsMaximal] (f : D) (hf : f ∉ p)
    (hother : ∀ q : Ideal D, q.IsMaximal → q ≠ p → f ∈ q) :
    IsLocalization.Away f (Localization.AtPrime p) := by
  apply (IsLocalization.iff_of_le_of_exists_dvd
    (S := Localization.AtPrime p) (Submonoid.powers f) p.primeCompl
    (Submonoid.powers_le.mpr hf) ?_).mpr inferInstance
  intro r hr
  by_contra h
  have hdisj : Disjoint (Ideal.span {r} : Set D) (Submonoid.powers f : Set D) := by
    rw [Set.disjoint_right]
    exact fun z hz hzr => h ⟨z, hz, Ideal.mem_span_singleton.mp hzr⟩
  obtain ⟨q, hq, hrq, hqf⟩ :=
    Ideal.exists_le_prime_disjoint (Ideal.span {r}) (Submonoid.powers f) hdisj
  have hfq : f ∉ q := Set.disjoint_right.mp hqf (Submonoid.mem_powers f)
  have hqp : q ≤ p := by
    by_cases hq0 : q = ⊥
    · exact hq0 ▸ bot_le
    · have hqmax := hq.isMaximal hq0
      have : q = p := by
        by_contra hqp
        exact hfq (hother q hqmax hqp)
      exact this.le
  exact hr (hqp (hrq (Ideal.subset_span (Set.mem_singleton r))))

/-- In a DVR it suffices to invert an element mapping to a uniformizer
to obtain the fraction field. -/
theorem isLocalization_of_uniformizer_image
    (A B F : Type) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] [Field F] [Algebra A B] [Algebra B F] [IsFractionRing B F]
    (hinj : Function.Injective (algebraMap A B)) (π : A)
    (hπ : Irreducible (algebraMap A B π)) :
    IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) F := by
  apply (IsLocalization.iff_of_le_of_exists_dvd (S := F)
    (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) (nonZeroDivisors B) ?_ ?_).mpr inferInstance
  · rintro _ ⟨a, ha, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero (fun h => nonZeroDivisors.ne_zero ha
      (hinj (h.trans (RingHom.map_zero (algebraMap A B)).symm)))
  · intro b hb
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (nonZeroDivisors.ne_zero hb) hπ
    have hp : π ≠ 0 := fun hp => hπ.ne_zero (by rw [hp, map_zero])
    refine ⟨(algebraMap A B π) ^ n, ⟨π ^ n, mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ hp),
      map_pow _ _ _⟩, ⟨(↑u⁻¹ : B), ?_⟩⟩
    calc
      (algebraMap A B π) ^ n = (↑u * (↑u⁻¹ : B)) * (algebraMap A B π) ^ n := by simp
      _ = b * (↑u⁻¹ : B) := by rw [hu]; ac_rfl

section FractionSquare

variable (A B K L : Type) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
  [Field K] [Field L] [Algebra A B] [Algebra A K] [Algebra B L]
  [IsFractionRing A K] [IsFractionRing B L]

noncomputable abbrev fractionSquareLift (hinj : Function.Injective (algebraMap A B)) : K →+* L :=
  IsFractionRing.lift (K := K) (g := (algebraMap B L).comp (algebraMap A B))
    (fun _ _ h => hinj (IsFractionRing.injective B L h))

omit [IsDomain A] [IsDomain B] in
theorem fractionSquareLift_algebraMap (hinj : Function.Injective (algebraMap A B)) (x : A) :
    fractionSquareLift A B K L hinj (algebraMap A K x) = algebraMap B L (algebraMap A B x) :=
  IsFractionRing.lift_algebraMap (g := (algebraMap B L).comp (algebraMap A B))
    (fun _ _ h => hinj (IsFractionRing.injective B L h)) x

/-- A uniformizer in the image identifies the fraction field with the
base change of fraction fields. -/
theorem isPullback_fractionSquare [IsDiscreteValuationRing B]
    (hinj : Function.Injective (algebraMap A B)) (π : A) (hπ : Irreducible (algebraMap A B π)) :
    IsPullback (Spec.map (CommRingCat.ofHom (algebraMap B L)))
      (Spec.map (CommRingCat.ofHom (fractionSquareLift A B K L hinj)))
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (Spec.map (CommRingCat.ofHom (algebraMap A K))) := by
  let _ : Algebra K L := (fractionSquareLift A B K L hinj).toAlgebra
  let _ : Algebra A L := ((algebraMap B L).comp (algebraMap A B)).toAlgebra
  have : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq fun x =>
    (fractionSquareLift_algebraMap A B K L hinj x).symm
  have := isLocalization_of_uniformizer_image A B L hinj π hπ
  have := Algebra.isPushout_of_isLocalization (nonZeroDivisors A) K B L
  exact isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_iff_isPushout.mpr inferInstance)

end FractionSquare

end NeronDVR

namespace NeronSH

section
variable {O K K' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
  [IsFractionRing O K] [Field K'] [Algebra K K'] [Algebra O K'] [IsScalarTower O K K']
  (O' : ValuationSubring K') [Algebra O O'] [IsScalarTower O O' K']
  [Algebra.IsSeparable K K'] [IsLocalHom (algebraMap O O')]
  (hunr : ∀ π : O, Irreducible π → Irreducible (algebraMap O O' π))

include hunr in
theorem Dn_isPrincipalOpen (s : Finset O') :
    ∃ f : Df O K O' s, f ∉ nI O K O' s ∧ IsLocalization.Away f (Dn O K O' s) := by
  let D := Df O K O' s
  let p := nI O K O' s
  have hp : p.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := O) p (by
      rw [← Ideal.LiesOver.over (P := p) (p := maximalIdeal O)]
      infer_instance)
  have hpn : p ≠ ⊥ := nI_ne_bot (O := O) (K := K) O' hunr s
  have hnfield : ¬ IsField D := fun hf =>
    hpn ((Ideal.IsMaximal.eq_of_le (Ring.isField_iff_maximal_bot.mp hf) hp.ne_top bot_le).symm)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  let k := algebraMap O D π
  have hk : k ≠ 0 := fun hz =>
    hπ.ne_zero (algebraMap_Df_injective (O := O) (K := K) O' s (hz.trans (map_zero _).symm))
  obtain ⟨f, hf, hother⟩ := NeronExtDedekind.exists_avoid hnfield p k hk
  refine ⟨f, hf, NeronDVR.isLocalizationAway_atPrime_of_maximal p f hf (fun q hq hqp => ?_)⟩
  have hu : q.under O = maximalIdeal O :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := O) q)
  apply hother q hq hqp
  change π ∈ q.under O
  rw [hu]
  exact IsLocalRing.mem_maximalIdeal _ |>.mpr hπ.not_isUnit

variable [Algebra.IsSeparable (ResidueField O) (ResidueField O')]

include hunr in
theorem etale_Dn (s : Finset O') : Algebra.Etale O (Dn O K O' s) := by
  obtain ⟨f, _, hf⟩ := Dn_isPrincipalOpen (O := O) (K := K) O' hunr s
  have : Algebra.FinitePresentation (Df O K O' s) (Dn O K O' s) :=
    IsLocalization.Away.finitePresentation (S := Dn O K O' s) f
  have : Algebra.FinitePresentation O (Dn O K O' s) :=
    Algebra.FinitePresentation.trans O (Df O K O' s) (Dn O K O' s)
  have : Algebra.IsUnramifiedAt O (nI O K O' s) := isUnramifiedAt_nI (O := O) (K := K) O' hunr s
  exact ⟨Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat (nI O K O' s), inferInstance⟩

include hunr in
theorem faithfullyFlat_Dn (s : Finset O') : Module.FaithfullyFlat O (Dn O K O' s) := by
  have : Algebra.Etale O (Dn O K O' s) := etale_Dn (O := O) (K := K) O' hunr s
  have : IsLocalHom (algebraMap O (Dn O K O' s)) :=
    isLocalHom_algebraMap_Dn (O := O) (K := K) O' s
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom (A := O) (B := Dn O K O' s)

omit [Algebra.IsSeparable (ResidueField O) (ResidueField O')] in
theorem injective_ψ (s : Finset O') : Function.Injective (ψ O K O' s) := by
  have hzero (z : Dn O K O' s) (hz : ψ O K O' s z = 0) : z = 0 := by
    obtain ⟨⟨c, t⟩, rfl⟩ := IsLocalization.mk'_surjective (nI O K O' s).primeCompl z
    change ψ O K O' s (IsLocalization.mk' (Dn O K O' s) c t) = 0 at hz
    change IsLocalization.mk' (Dn O K O' s) c t = 0
    have h := ψ_mk' (O := O) (K := K) O' s c t
    rw [hz, zero_mul] at h
    have hc : c = 0 := ι_injective (O := O) (K := K) O' s (by rw [← h, map_zero])
    rw [hc, IsLocalization.mk'_zero]
  intro x y he
  apply sub_eq_zero.mp
  apply hzero
  exact ((ψ O K O' s).map_sub x y).trans (sub_eq_zero.mpr he)

omit [Algebra.IsSeparable (ResidueField O) (ResidueField O')] in
include hunr in
theorem faithfullyFlat_ψ (s : Finset O') :
    letI := (ψ O K O' s).toAlgebra
    Module.FaithfullyFlat (Dn O K O' s) O' := by
  let _ : Algebra (Dn O K O' s) O' := (ψ O K O' s).toAlgebra
  have : IsLocalHom (algebraMap (Dn O K O' s) O') :=
    isLocalHom_ψ (O := O) (K := K) O' s
  have : IsDiscreteValuationRing (Dn O K O' s) := isDVR_Dn (O := O) (K := K) O' hunr s
  have : Module.IsTorsionFree (Dn O K O' s) O' :=
    (Module.isTorsionFree_iff_algebraMap_injective (R := Dn O K O' s) (A := O')).mpr
      (injective_ψ (O := O) (K := K) O' s)
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

omit [Algebra.IsSeparable (ResidueField O) (ResidueField O')] in
theorem isScalarTower_ψ (s : Finset O') :
    let _ : Algebra (Dn O K O' s) O' := (ψ O K O' s).toAlgebra
    IsScalarTower O (Dn O K O' s) O' := by
  let _ : Algebra (Dn O K O' s) O' := (ψ O K O' s).toAlgebra
  exact IsScalarTower.of_algebraMap_eq fun x => (ψ_algebraMap_O (O := O) (K := K) O' s x).symm

include hunr in
theorem subset_range_ψa (s : Finset O') : (s : Set O') ⊆ (ψa O K O' s).range := by
  intro x hx
  obtain ⟨c, t, ht, hct⟩ := exists_rep (O := O) (K := K) O' hunr s x hx
  let b : (nI O K O' s).primeCompl := ⟨t, ht⟩
  refine ⟨IsLocalization.mk' (Dn O K O' s) c b, ?_⟩
  have hunit : IsUnit (ι O K O' s t) := IsLocalRing.notMem_maximalIdeal.mp ht
  apply mul_right_cancel₀ hunit.ne_zero
  exact (ψ_mk' (O := O) (K := K) O' s c b).trans hct.symm

omit [Algebra.IsSeparable (ResidueField O) (ResidueField O')] in
theorem monotone_range_ψa : Monotone fun s : Finset O' => (ψa O K O' s).range := by
  intro s t hst
  have hL : Lf K O' s ≤ Lf K O' t := IntermediateField.adjoin.mono K _ _
    (Set.image_mono (show (s : Set O') ⊆ (t : Set O') from hst))
  let j₀ : Lf K O' s →ₐ[O] Lf K O' t := (IntermediateField.inclusion hL).restrictScalars O
  let j : Df O K O' s →ₐ[O] Df O K O' t :=
    (j₀.comp (Df O K O' s).val).codRestrict (Df O K O' t) fun x => IsIntegral.map j₀ x.2
  have hj (x : Df O K O' s) : ι O K O' t (j x) = ι O K O' s x := Subtype.ext rfl
  have hcompl : (nI O K O' s).primeCompl ≤ (nI O K O' t).primeCompl.comap j.toRingHom := by
    intro x hx
    change ι O K O' t (j x) ∉ maximalIdeal O'
    rw [hj]
    exact hx
  let jLoc : Dn O K O' s →+* Dn O K O' t := IsLocalization.map (Dn O K O' t) j.toRingHom hcompl
  have hcomp : (ψ O K O' t).comp jLoc = ψ O K O' s := by
    apply IsLocalization.ringHom_ext (nI O K O' s).primeCompl
    apply RingHom.ext
    intro x
    simp only [RingHom.comp_apply]
    rw [show jLoc (algebraMap (Df O K O' s) (Dn O K O' s) x) =
      algebraMap (Df O K O' t) (Dn O K O' t) (j x) from IsLocalization.map_eq hcompl x,
      ψ_algebraMap, ψ_algebraMap, hj]
  rintro x ⟨y, rfl⟩
  exact ⟨jLoc y, RingHom.congr_fun hcomp y⟩

include hunr in
theorem iSup_range_ψa_eq_top : (⨆ s : Finset O', (ψa O K O' s).range) = ⊤ := by
  apply top_unique
  intro x _
  classical
  exact (le_iSup (fun s : Finset O' => (ψa O K O' s).range) {x})
    (subset_range_ψa (O := O) (K := K) O' hunr {x} (Finset.mem_singleton_self x))

section FractionField

omit [Algebra.IsSeparable (ResidueField O) (ResidueField O')] in
theorem algebraMap_Dn_injective (s : Finset O') : Function.Injective (algebraMap O (Dn O K O' s)) := by
  rw [IsScalarTower.algebraMap_eq O (Df O K O' s) (Dn O K O' s)]
  exact (IsLocalization.injective (Dn O K O' s)
    (Ideal.primeCompl_le_nonZeroDivisors (nI O K O' s))).comp
    (algebraMap_Df_injective (O := O) (K := K) O' s)

omit [IsFractionRing O K] [Algebra.IsSeparable K K'] [IsLocalHom (algebraMap O O')]
  [Algebra.IsSeparable (ResidueField O) (ResidueField O')] in
theorem isDomain_Dn (s : Finset O') : IsDomain (Dn O K O' s) :=
  IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors (nI O K O' s))

omit [Algebra.IsSeparable (ResidueField O) (ResidueField O')] in
abbrev StageFraction (s : Finset O') := FractionRing (Dn O K O' s)

omit [Algebra.IsSeparable (ResidueField O) (ResidueField O')] in
noncomputable abbrev stageFractionAlgebra (s : Finset O') :
    Algebra (Dn O K O' s) (StageFraction (O := O) (K := K) O' s) :=
  OreLocalization.instAlgebra (R := Dn O K O' s) (S := nonZeroDivisors (Dn O K O' s))
    (R₀ := Dn O K O' s)

omit [IsFractionRing O K] [Algebra.IsSeparable K K'] [IsLocalHom (algebraMap O O')]
  [Algebra.IsSeparable (ResidueField O) (ResidueField O')] in
theorem stageIsFractionRing (s : Finset O') :
    let _ := stageFractionAlgebra (O := O) (K := K) O' s
    IsFractionRing (Dn O K O' s) (StageFraction (O := O) (K := K) O' s) :=
  Localization.isLocalization (M := nonZeroDivisors (Dn O K O' s))

omit [Algebra.IsSeparable (ResidueField O) (ResidueField O')] in
noncomputable abbrev stageFractionField (s : Finset O') :
    Field (StageFraction (O := O) (K := K) O' s) :=
  let _ := isDomain_Dn (O := O) (K := K) O' s
  FractionRing.field (Dn O K O' s)

omit [Algebra.IsSeparable (ResidueField O) (ResidueField O')] in
noncomputable abbrev stageBaseMap (s : Finset O') : K →+* StageFraction (O := O) (K := K) O' s :=
  let _ := isDomain_Dn (O := O) (K := K) O' s
  let _ := stageFractionField (O := O) (K := K) O' s
  let _ := stageFractionAlgebra (O := O) (K := K) O' s
  have := stageIsFractionRing (O := O) (K := K) O' s
  NeronDVR.fractionSquareLift O (Dn O K O' s) K (StageFraction (O := O) (K := K) O' s)
    (algebraMap_Dn_injective (O := O) (K := K) O' s)

omit [Algebra.IsSeparable (ResidueField O) (ResidueField O')] in
noncomputable abbrev stageStrictMap (s : Finset O') : StageFraction (O := O) (K := K) O' s →+* K' :=
  let _ := isDomain_Dn (O := O) (K := K) O' s
  let _ := stageFractionField (O := O) (K := K) O' s
  let _ := stageFractionAlgebra (O := O) (K := K) O' s
  have := stageIsFractionRing (O := O) (K := K) O' s
  let _ : Algebra (Dn O K O' s) O' := (ψ O K O' s).toAlgebra
  NeronDVR.fractionSquareLift (Dn O K O' s) O' (StageFraction (O := O) (K := K) O' s) K'
    (injective_ψ (O := O) (K := K) O' s)

omit [Algebra.IsSeparable (ResidueField O) (ResidueField O')] in
include hunr in
theorem isPullback_stage_base (s : Finset O') :
    let _ := stageFractionAlgebra (O := O) (K := K) O' s
    IsPullback (Spec.map (CommRingCat.ofHom (R := Dn O K O' s)
        (S := StageFraction (O := O) (K := K) O' s)
        (algebraMap (Dn O K O' s) (StageFraction (O := O) (K := K) O' s))))
      (Spec.map (CommRingCat.ofHom (R := K) (S := StageFraction (O := O) (K := K) O' s)
        (stageBaseMap (O := O) (K := K) O' s)))
      (Spec.map (CommRingCat.ofHom (R := O) (S := Dn O K O' s) (algebraMap O (Dn O K O' s))))
      (Spec.map (CommRingCat.ofHom (algebraMap O K))) := by
  let R := Dn O K O' s
  let F := StageFraction (O := O) (K := K) O' s
  let _ : Algebra R F := stageFractionAlgebra (O := O) (K := K) O' s
  have : IsFractionRing R F := stageIsFractionRing (O := O) (K := K) O' s
  have : IsDomain R := isDomain_Dn (O := O) (K := K) O' s
  let _ : Field F := stageFractionField (O := O) (K := K) O' s
  have : IsDiscreteValuationRing R := isDVR_Dn (O := O) (K := K) O' hunr s
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hπn : Irreducible (algebraMap O R π) := by
    apply Irreducible.of_map (f := ψ O K O' s)
    rw [ψ_algebraMap_O]
    exact hunr π hπ
  exact NeronDVR.isPullback_fractionSquare O R K F
    (algebraMap_Dn_injective (O := O) (K := K) O' s) π hπn

omit [Algebra.IsSeparable (ResidueField O) (ResidueField O')] in
include hunr in
theorem isPullback_stage_strict [IsDiscreteValuationRing O'] (s : Finset O') :
    let _ := stageFractionAlgebra (O := O) (K := K) O' s
    IsPullback (Spec.map (CommRingCat.ofHom (algebraMap O' K')))
      (Spec.map (CommRingCat.ofHom (R := StageFraction (O := O) (K := K) O' s) (S := K')
        (stageStrictMap (O := O) (K := K) O' s)))
      (Spec.map (CommRingCat.ofHom (R := Dn O K O' s) (S := O') (ψ O K O' s)))
      (Spec.map (CommRingCat.ofHom (R := Dn O K O' s) (S := StageFraction (O := O) (K := K) O' s)
        (algebraMap (Dn O K O' s) (StageFraction (O := O) (K := K) O' s)))) := by
  let R := Dn O K O' s
  let F := StageFraction (O := O) (K := K) O' s
  let _ : Algebra R F := stageFractionAlgebra (O := O) (K := K) O' s
  have : IsFractionRing R F := stageIsFractionRing (O := O) (K := K) O' s
  have : IsDomain R := isDomain_Dn (O := O) (K := K) O' s
  let _ : Field F := stageFractionField (O := O) (K := K) O' s
  let _ : Algebra R O' := (ψ O K O' s).toAlgebra
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hπ' : Irreducible (ψ O K O' s (algebraMap O R π)) := by
    rw [ψ_algebraMap_O]
    exact hunr π hπ
  exact NeronDVR.isPullback_fractionSquare R O' F K'
    (injective_ψ (O := O) (K := K) O' s) (algebraMap O R π) hπ'

end FractionField

end

end NeronSH

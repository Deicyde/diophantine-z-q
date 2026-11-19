/-
# H5 / NOS round 2, lane 3 (`Spreadout/`): the local étale DVR stage at a rational closed point

New glue (no vendored source in this file). Ownership:

* finite-spectrum construction (a): this file;
* the single-element localization at a prime of a ring with finite spectrum (b, c): lane 5's
  stable `ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective.exists_away_isLocalization_atPrime`
  (`GoodDescent/Effective/PrimeLocalization.lean`, sha256 02cd73b4…), consumed read-only;
* local / étale / DVR / faithfully flat (d), the special fibre (e) and the factorization of the
  actual stage legs (f): this file;
* the localized DVR theorem: H4's `Port.IsDiscreteValuationRing.of_formallyUnramified`
  (`CloudR2Raynaud/StrictHenselization/Port/UnramifiedDVR.lean`, a port of AxiomMath/Stacks
  c496df0d, Apache-2.0), consumed read-only;
* the whole-special-fibre isomorphism of a refined rational-pointed étale neighbourhood: lane 5's
  stable `GoodDescent.OrdinaryStages.exists_stageRefinement`, consumed read-only.

Mathematics.  `O` is a DVR and `B` an étale `O`-algebra; neither `B` nor any localization of it
is assumed to be a domain, local or a DVR.
(a) `Spec B` is finite: `B` is quasi-finite over `O` (Mathlib: essentially of finite type and
    formally unramified), and `Spec O = {⊥, 𝔪}`.
(d) If `Localization.Away s` is the localization of `B` at a prime `q` over `𝔪`, it is local, the
    map from `O` is local, it is étale and faithfully flat over `O`, it is a DVR in which every
    uniformizer of `O` is a uniformizer, and its unique closed-fibre point is its closed point.
(e) If `q = ker aug` for an `O`-augmentation `aug : B → κ(O)`, then `aug` extends to `B_s`, and
    the WHOLE special fibre of `Spec B_s → Spec O` is `Spec κ(O)`. Lane 5's refined neighbourhood
    of `Spec B_s` contains the closed point, hence every point, so its open immersion is an
    isomorphism, and the fibre isomorphism transports to `Spec B_s` itself.
(f) Every `O`-algebra map `α : B → P` to a local ring with `α⁻¹(𝔪_P) = q` factors uniquely
    through `B_s`. This includes the actual ordinary stage legs `pres.ι.app j`, whose
    augmentation is `residuePointAlgHom e he ∘ ι_j` with kernel `ι_j⁻¹(𝔪_P)`.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2Raynaud.StrictHenselization.Port.UnramifiedDVR
import ZInQKernel.Contrib.CloudR2Raynaud.StrictHenselization.OrdinaryPresentation
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.PrimeLocalization
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.StageRefinement

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

namespace ZInQ.Contrib.CloudR2NOS.Spreadout.LocalStage

/-! ### (a) Finite spectra -/

section FiniteSpec

variable (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- A prime of a DVR is `⊥` or the maximal ideal. -/
theorem eq_bot_or_eq_maximalIdeal (p : Ideal O) [p.IsPrime] : p = ⊥ ∨ p = maximalIdeal O := by
  by_cases hp : p = ⊥
  · exact Or.inl hp
  · right
    haveI : p.IsMaximal := IsPrime.to_maximal_ideal hp
    exact IsLocalRing.eq_maximalIdeal this

/-- The spectrum of a DVR is finite. -/
theorem finite_primeSpectrum_of_dvr : Finite (PrimeSpectrum O) := by
  refine Finite.of_injective (fun p : PrimeSpectrum O => p.asIdeal = ⊥) (fun p q hpq => ?_)
  have hne : maximalIdeal O ≠ ⊥ := IsDiscreteValuationRing.not_a_field O
  ext1
  rcases eq_bot_or_eq_maximalIdeal O p.asIdeal with hp | hp <;>
    rcases eq_bot_or_eq_maximalIdeal O q.asIdeal with hq | hq
  · rw [hp, hq]
  · exact absurd (hq.symm.trans (cast hpq hp)) hne
  · exact absurd (hp.symm.trans (cast hpq.symm hq)) hne
  · rw [hp, hq]

/-- **(a)** The spectrum of an étale algebra over a DVR is finite. -/
theorem finite_primeSpectrum_of_etale (B : Type u) [CommRing B] [Algebra O B]
    [Algebra.Etale O B] : Finite (PrimeSpectrum B) := by
  haveI := finite_primeSpectrum_of_dvr O
  exact Algebra.QuasiFinite.finite_primeSpectrum O B

end FiniteSpec

/-! ### (d) The localization at a prime over the closed point -/

section Local

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {B : Type u} [CommRing B] [Algebra O B] [Algebra.Etale O B]

/-- The structure map to the localization at a prime over the closed point is local. -/
theorem isLocalHom_of_atPrime (q : Ideal B) [q.IsPrime] [q.LiesOver (maximalIdeal O)] (s : B)
    [IsLocalization.AtPrime (Localization.Away s) q] :
    IsLocalHom (algebraMap O (Localization.Away s)) := by
  haveI : IsLocalRing (Localization.Away s) := IsLocalization.AtPrime.isLocalRing _ q
  apply ((local_hom_TFAE (algebraMap O (Localization.Away s))).out 4 1).mp
  intro r hr
  rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply O B (Localization.Away s)]
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.Away s) q _).mpr
    ((Ideal.mem_of_liesOver q (maximalIdeal O) r).mp hr)

/-- **(d)** The single-element localization `B_s` of `B` at a prime `q` over the closed point is
a local étale, faithfully flat DVR over `O`. Every uniformizer of `O` is a uniformizer of `B_s`,
its closed point lies over `q`, and it is the ONLY point of the special fibre. -/
theorem localStage (q : Ideal B) [q.IsPrime] [q.LiesOver (maximalIdeal O)] (s : B)
    [IsLocalization.AtPrime (Localization.Away s) q] :
    ∃ (_ : IsLocalRing (Localization.Away s)) (_ : IsDomain (Localization.Away s)),
      IsDiscreteValuationRing (Localization.Away s) ∧
      IsLocalHom (algebraMap O (Localization.Away s)) ∧
      Algebra.Etale O (Localization.Away s) ∧
      Module.FaithfullyFlat O (Localization.Away s) ∧
      (∀ ϖ : O, Irreducible ϖ → Irreducible (algebraMap O (Localization.Away s) ϖ) ∧
        maximalIdeal (Localization.Away s) =
          Ideal.span {algebraMap O (Localization.Away s) ϖ}) ∧
      (maximalIdeal (Localization.Away s)).comap (algebraMap B (Localization.Away s)) = q ∧
      ∀ P : Ideal (Localization.Away s), P.IsPrime →
        P.comap (algebraMap O (Localization.Away s)) = maximalIdeal O →
          P = maximalIdeal (Localization.Away s) := by
  haveI hloc : IsLocalRing (Localization.Away s) := IsLocalization.AtPrime.isLocalRing _ q
  haveI hlh : IsLocalHom (algebraMap O (Localization.Away s)) := isLocalHom_of_atPrime q s
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨hdom, hdvr, -, -⟩ :=
    ZInQ.Contrib.CloudR2Raynaud.StrictHenselization.Port.IsDiscreteValuationRing.of_formallyUnramified
      (A := O) (S := Localization.Away s) hϖ
  refine ⟨hloc, hdom, hdvr, hlh, inferInstance, Module.FaithfullyFlat.of_flat_of_isLocalHom,
    ?_, ?_, ?_⟩
  · intro ϖ' hϖ'
    obtain ⟨-, -, hirr, hmax⟩ :=
      ZInQ.Contrib.CloudR2Raynaud.StrictHenselization.Port.IsDiscreteValuationRing.of_formallyUnramified
        (A := O) (S := Localization.Away s) hϖ'
    exact ⟨hirr, hmax⟩
  · exact IsLocalization.AtPrime.under_maximalIdeal (Localization.Away s) q
  · intro P hP hPO
    exact Algebra.QuasiFinite.eq_of_le_of_under_eq (R := O) P (maximalIdeal _)
      (le_maximalIdeal hP.ne_top) (by
        change P.comap _ = (maximalIdeal _).comap _
        rw [hPO, IsLocalRing.maximalIdeal_comap])

end Local

/-! ### (f) Factorization of maps to local rings -/

section Factor

variable {O : Type u} [CommRing O] {B : Type u} [CommRing B] [Algebra O B]

/-- **(f)** An `O`-algebra map `α : B → P` to a local ring that sends `s` outside the maximal
ideal factors uniquely through `B_s`. -/
theorem existsUnique_factor_away {P : Type u} [CommRing P] [IsLocalRing P] [Algebra O P]
    (α : B →ₐ[O] P) (s : B) (hs : s ∉ (maximalIdeal P).comap α.toRingHom) :
    ∃! β : Localization.Away s →ₐ[O] P,
      β.comp (IsScalarTower.toAlgHom O B (Localization.Away s)) = α := by
  have hunit : ∀ y : Submonoid.powers s, IsUnit (α y) := by
    rintro ⟨_, n, rfl⟩
    rw [map_pow]
    exact (notMem_maximalIdeal.mp hs).pow n
  refine ⟨IsLocalization.liftAlgHom (M := Submonoid.powers s) (f := α) hunit, ?_, ?_⟩
  · ext b
    simp [IsLocalization.lift_eq]
  · intro β hβ
    apply AlgHom.toRingHom_injective
    apply IsLocalization.ringHom_ext (Submonoid.powers s)
    ext b
    have h1 := congrArg (fun φ : B →ₐ[O] P => φ b) hβ
    simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at h1
    simp [h1, IsLocalization.lift_eq]

end Factor

/-! ### (e) The rational point and the whole special fibre -/

section Rational

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {B : Type u} [CommRing B] [Algebra O B] (aug : B →ₐ[O] ResidueField O)

/-- The kernel of an `O`-augmentation to the field `κ(O)` is prime. -/
instance isPrime_ker_aug : (RingHom.ker aug.toRingHom).IsPrime := RingHom.ker_isPrime _

/-- The kernel of an `O`-augmentation to `κ(O)` lies over the closed point. -/
theorem ker_liesOver : (RingHom.ker aug.toRingHom).LiesOver (maximalIdeal O) := by
  refine ⟨?_⟩
  change maximalIdeal O = (RingHom.ker aug.toRingHom).comap (algebraMap O B)
  rw [RingHom.comap_ker]
  have h : aug.toRingHom.comp (algebraMap O B) = residue O := by
    ext r
    exact (aug.commutes r).trans (RingHom.congr_fun (ResidueField.algebraMap_eq O) r)
  rw [h, ker_residue]

/-- The extension of the augmentation to `B_s`, for `s` outside its kernel. -/
def augAway (s : B) (hs : s ∉ RingHom.ker aug.toRingHom) :
    Localization.Away s →ₐ[O] ResidueField O :=
  IsLocalization.liftAlgHom (M := Submonoid.powers s) (f := aug) (by
    rintro ⟨_, n, rfl⟩
    rw [map_pow]
    exact (isUnit_iff_ne_zero.mpr fun h => hs (RingHom.mem_ker.mpr h)).pow n)

theorem augAway_comp (s : B) (hs : s ∉ RingHom.ker aug.toRingHom) :
    (augAway aug s hs).comp (IsScalarTower.toAlgHom O B (Localization.Away s)) = aug := by
  ext b
  simp [augAway, IsLocalization.lift_eq]

theorem augAway_surjective (s : B) (hs : s ∉ RingHom.ker aug.toRingHom) :
    Function.Surjective (augAway aug s hs) := by
  intro z
  obtain ⟨r, rfl⟩ := residue_surjective z
  refine ⟨algebraMap O (Localization.Away s) r, ?_⟩
  rw [AlgHom.commutes, ResidueField.algebraMap_eq]

/-- Transport of a fibre isomorphism along an isomorphism of the source. -/
theorem isIso_fiberToSpecResidueField_of_isIso_comp {X' X S : Scheme.{u}} (e : X' ⟶ X) [IsIso e]
    (p : X ⟶ S) (z : S) [IsIso ((e ≫ p).fiberToSpecResidueField z)] :
    IsIso (p.fiberToSpecResidueField z) := by
  let φ : (e ≫ p).fiber z ⟶ p.fiber z :=
    pullback.map (e ≫ p) (S.fromSpecResidueField z) p (S.fromSpecResidueField z) e (𝟙 _) (𝟙 _)
      (by simp) (by simp)
  haveI : IsIso φ := pullback.map_isIso _ _ _ _ _ _ _ _ _
  have hφ : φ ≫ p.fiberToSpecResidueField z = (e ≫ p).fiberToSpecResidueField z :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  haveI : IsIso (φ ≫ p.fiberToSpecResidueField z) := by
    rw [hφ]
    infer_instance
  exact IsIso.of_isIso_comp_left φ _

/-- **(e)** For `q = ker aug`, the WHOLE special fibre of `Spec B_s → Spec O` is `Spec κ(O)`. -/
theorem isIso_fiber_away [Algebra.Etale O B] (s : B)
    [IsLocalization.AtPrime (Localization.Away s) (RingHom.ker aug.toRingHom)]
    (hs : s ∉ RingHom.ker aug.toRingHom) :
    IsIso ((GoodDescent.OrdinaryStages.stageBase O (Localization.Away s)).fiberToSpecResidueField
      (closedPoint O)) := by
  haveI : IsLocalRing (Localization.Away s) :=
    IsLocalization.AtPrime.isLocalRing _ (RingHom.ker aug.toRingHom)
  obtain ⟨r⟩ := GoodDescent.OrdinaryStages.exists_stageRefinement (R := O)
    (B := Localization.Away s) (augAway aug s hs)
  -- the refined neighbourhood contains the closed point of `Spec B_s`
  have hker : (RingHom.ker (augAway aug s hs).toRingHom).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ (augAway_surjective aug s hs)
  let pt : Spec (CommRingCat.of (ResidueField O)) := closedPoint (ResidueField O)
  have hpt : (GoodDescent.OrdinaryStages.stagePoint (augAway aug s hs)) pt =
      closedPoint (Localization.Away s) := by
    rw [GoodDescent.OrdinaryStages.stagePoint, Spec.map_apply]
    refine PrimeSpectrum.ext ?_
    change pt.asIdeal.comap (augAway aug s hs).toRingHom = maximalIdeal _
    have hle : RingHom.ker (augAway aug s hs).toRingHom ≤
        pt.asIdeal.comap (augAway aug s hs).toRingHom := fun x hx => by
      rw [Ideal.mem_comap, RingHom.mem_ker.mp hx]
      exact pt.asIdeal.zero_mem
    have heq := hker.eq_of_le (Ideal.comap_isPrime _ pt.asIdeal).ne_top hle
    rw [← heq]
    exact IsLocalRing.eq_maximalIdeal hker
  have hmem : closedPoint (Localization.Away s) ∈ r.V := by
    have h1 : r.V.ι (r.point pt) = closedPoint (Localization.Away s) := by
      rw [← hpt, ← r.point_inclusion]
      rfl
    rw [← h1]
    exact (Scheme.Opens.range_ι r.V).subset (Set.mem_range_self _)
  have hall : ∀ x : Spec (CommRingCat.of (Localization.Away s)), x ∈ r.V := fun x =>
    (specializes_closedPoint x).mem_open r.V.isOpen hmem
  haveI : IsIso r.V.ι := (isIso_iff_isOpenImmersion_and_surjective r.V.ι).mpr
    ⟨inferInstance, ⟨fun x => by
      have : x ∈ Set.range r.V.ι := by rw [Scheme.Opens.range_ι]; exact hall x
      exact this⟩⟩
  haveI := r.wholeFibre
  exact isIso_fiberToSpecResidueField_of_isIso_comp r.V.ι _ _

end Rational

/-! ### Assembly over the actual finite étale stages -/

section Assembly

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **The local étale DVR stage at the rational point of an actual finite étale stage.** For an
étale `O`-algebra `B` with an `O`-augmentation `aug : B → κ(O)`, there is `s ∉ ker aug` such that
`B_s` is the localization at `ker aug`, a local étale faithfully flat DVR over `O` whose whole
special fibre is `Spec κ(O)`, with an extension of `aug`. Every `O`-algebra map to a local ring
`P` that pulls `𝔪_P` back to `ker aug` factors uniquely through `B_s`. -/
theorem exists_localStage (B : Type u) [CommRing B] [Algebra O B] [Algebra.Etale O B]
    (aug : B →ₐ[O] ResidueField O) :
    ∃ s : B, s ∉ RingHom.ker aug.toRingHom ∧
      IsLocalization.AtPrime (Localization.Away s) (RingHom.ker aug.toRingHom) ∧
      (∃ (_ : IsLocalRing (Localization.Away s)) (_ : IsDomain (Localization.Away s)),
        IsDiscreteValuationRing (Localization.Away s) ∧
        IsLocalHom (algebraMap O (Localization.Away s)) ∧
        Algebra.Etale O (Localization.Away s) ∧
        Module.FaithfullyFlat O (Localization.Away s) ∧
        (∀ ϖ : O, Irreducible ϖ → Irreducible (algebraMap O (Localization.Away s) ϖ) ∧
          maximalIdeal (Localization.Away s) =
            Ideal.span {algebraMap O (Localization.Away s) ϖ}) ∧
        IsIso ((GoodDescent.OrdinaryStages.stageBase O
          (Localization.Away s)).fiberToSpecResidueField (closedPoint O))) ∧
      (∃ augS : Localization.Away s →ₐ[O] ResidueField O,
        augS.comp (IsScalarTower.toAlgHom O B (Localization.Away s)) = aug) ∧
      ∀ {P : Type u} [CommRing P] [IsLocalRing P] [Algebra O P] (α : B →ₐ[O] P),
        (maximalIdeal P).comap α.toRingHom = RingHom.ker aug.toRingHom →
        ∃! β : Localization.Away s →ₐ[O] P,
          β.comp (IsScalarTower.toAlgHom O B (Localization.Away s)) = α := by
  haveI : Finite (PrimeSpectrum B) := finite_primeSpectrum_of_etale O B
  haveI : (RingHom.ker aug.toRingHom).LiesOver (maximalIdeal O) := ker_liesOver aug
  obtain ⟨s, hs, hloc⟩ :=
    GoodDescent.Effective.exists_away_isLocalization_atPrime B (RingHom.ker aug.toRingHom)
  haveI := hloc
  obtain ⟨h1, h2, hdvr, hlh, het, hff, hunif, -, -⟩ :=
    localStage (O := O) (RingHom.ker aug.toRingHom) s
  refine ⟨s, hs, hloc, ⟨h1, h2, hdvr, hlh, het, hff, hunif, isIso_fiber_away aug s hs⟩,
    ⟨augAway aug s hs, augAway_comp aug s hs⟩, ?_⟩
  intro P _ _ _ α hα
  exact existsUnique_factor_away α s (by rw [hα]; exact hs)

/-- The kernel of an augmentation through a local ring, via a residue point whose kernel is the
maximal ideal, is the pull-back of the maximal ideal. -/
theorem ker_comp_eq_comap {B P : Type u} [CommRing B] [Algebra O B] [CommRing P] [IsLocalRing P]
    [Algebra O P] (ψ : P →ₐ[O] ResidueField O) (hψ : RingHom.ker ψ.toRingHom = maximalIdeal P)
    (α : B →ₐ[O] P) :
    RingHom.ker (ψ.comp α).toRingHom = (maximalIdeal P).comap α.toRingHom := by
  rw [← hψ, RingHom.comap_ker]
  rfl

/-- H4's ordinary residue point has kernel the maximal ideal. -/
theorem ker_residuePointAlgHom {P : Type u} [CommRing P] [IsLocalRing P] [Algebra O P]
    (e : ResidueField O ≃+* ResidueField P)
    (he : ∀ r : O, e (residue O r) = residue P (algebraMap O P r)) :
    RingHom.ker (ZInQ.Contrib.CloudR2Raynaud.StrictHenselization.Ordinary.residuePointAlgHom
      e he).toRingHom = maximalIdeal P := by
  ext x
  change e.symm (residue P x) = 0 ↔ x ∈ maximalIdeal P
  rw [map_eq_zero_iff _ e.symm.injective, residue_eq_zero_iff]

/-- **The actual ordinary stage legs.** For H4's actual pointed étale presentation of the
ordinary henselization `P` (stage augmentations `aug j = residuePointAlgHom e he ∘ ι_j`), every
raw finite étale stage has a local étale DVR stage `B_s` at its rational point, through which the
actual leg `ι_j` factors uniquely. -/
theorem exists_localStage_of_leg {P : Type u} [CommRing P] [IsLocalRing P] [Algebra O P]
    (e : ResidueField O ≃+* ResidueField P)
    (he : ∀ r : O, e (residue O r) = residue P (algebraMap O P r))
    (B : Type u) [CommRing B] [Algebra O B] [Algebra.Etale O B] (ι : B →ₐ[O] P) :
    ∃ s : B, IsUnit (ι s) ∧
      IsLocalization.AtPrime (Localization.Away s) ((maximalIdeal P).comap ι.toRingHom) ∧
      (∃ (_ : IsLocalRing (Localization.Away s)) (_ : IsDomain (Localization.Away s)),
        IsDiscreteValuationRing (Localization.Away s) ∧
        Algebra.Etale O (Localization.Away s) ∧
        Module.FaithfullyFlat O (Localization.Away s) ∧
        IsIso ((GoodDescent.OrdinaryStages.stageBase O
          (Localization.Away s)).fiberToSpecResidueField (closedPoint O))) ∧
      ∃! β : Localization.Away s →ₐ[O] P,
        β.comp (IsScalarTower.toAlgHom O B (Localization.Away s)) = ι := by
  let aug := (ZInQ.Contrib.CloudR2Raynaud.StrictHenselization.Ordinary.residuePointAlgHom
    e he).comp ι
  have hker : RingHom.ker aug.toRingHom = (maximalIdeal P).comap ι.toRingHom :=
    ker_comp_eq_comap _ (ker_residuePointAlgHom e he) ι
  obtain ⟨s, hs, hloc, ⟨h1, h2, hdvr, -, het, hff, -, hfib⟩, -, hfac⟩ := exists_localStage B aug
  have hloc' : IsLocalization.AtPrime (Localization.Away s)
      ((maximalIdeal P).comap ι.toRingHom) := by
    convert hloc using 2
    exact hker.symm
  refine ⟨s, ?_, hloc', ⟨h1, h2, hdvr, het, hff, hfib⟩, hfac ι hker.symm⟩
  rw [hker] at hs
  exact notMem_maximalIdeal.mp hs

end Assembly

end ZInQ.Contrib.CloudR2NOS.Spreadout.LocalStage

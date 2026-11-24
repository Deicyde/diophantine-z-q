import ZInQKernel.Contrib.OneProof.SZThm33.DescentKernelPairs

/-! Finite-stage descent of a semiabelian quotient over an arbitrary field.
The effective descent construction adapts Jack McCarthy's `ChevalleyFree.lean`.
The kernel-pair condition here uses torsion on the possibly nonreduced overlap. -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ.HeightSplit ZInQ.ChevFree ZInQ.SemiAbDescend DictModels.RaynaudOr

set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SZRaynaud

section FiniteStage

variable {k : Type} [Field k] {U : Over (Spec (CommRingCat.of k))} [GrpObj U]
  {B' : PkgI3.AbVar (AlgebraicClosure k)}
  {k₁ : Type} [Field k₁] [Algebra k k₁] [Algebra k₁ (AlgebraicClosure k)]
  [IsScalarTower k k₁ (AlgebraicClosure k)]

theorem descend_quotient_finite_stage [FiniteDimensional k k₁] [Algebra.IsAlgebraic k₁ (AlgebraicClosure k)]
    (hqcU : QuasiCompact U.hom)
    (π' : (Over.pullback (sφ (φbar k))).obj U ⟶ B'.X)
    (hπ : letI := B'.grp; letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
      IsMonHom π')
    (hfl : Flat π'.left) (hsu : Surjective π'.left) (r : ℕ)
    (e : letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
      ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R],
      (Fin r → Rˣ) →* (algPt (AlgebraicClosure k) R ⟶ (Over.pullback (sφ (φbar k))).obj U))
    (he_inj : ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R], Function.Injective (e R))
    (he_ker : letI := B'.grp; letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
      ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R]
      (u : algPt (AlgebraicClosure k) R ⟶ (Over.pullback (sφ (φbar k))).obj U),
      u ≫ π' = 1 ↔ u ∈ (e R).range)
    (he_nat : ∀ (R S : Type) [CommRing R] [Algebra (AlgebraicClosure k) R] [CommRing S]
      [Algebra (AlgebraicClosure k) S] (f : R →ₐ[AlgebraicClosure k] S) (t : Fin r → Rˣ),
      e S (fun i => Units.map (f : R →* S) (t i)) = algPtMap f ≫ e R t)
    (X₁ : Over (Spec (CommRingCat.of k₁))) (π₁ : (Over.pullback (qq k k₁)).obj U ⟶ X₁)
    (c : B'.X.left ⟶ X₁.left) (hc : IsPullback c B'.X.hom X₁.hom (q₂ k k₁))
    (hcompat : π'.left ≫ c = rr U k₁ ≫ π₁.left) :
    ∃ (B : PkgI3.AbVar k) (π : U ⟶ B.X),
      letI : GrpObj ((Over.pullback (sφ (φbar k))).obj B.X) := Functor.grpObjObj
      IsMonHom π ∧ Flat π.left ∧ Surjective π.left ∧
      ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R]
        (u : algPt (AlgebraicClosure k) R ⟶ (Over.pullback (sφ (φbar k))).obj U),
        letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
        u ≫ (Over.pullback (sφ (φbar k))).map π = 1 ↔ u ≫ π' = 1 := by
  letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
  letI := B'.grp
  haveI := hπ
  haveI := hqcU
  haveI := hfl
  haveI := hsu
  haveI := B'.proper
  haveI := B'.smooth
  haveI := B'.geomInt
  -- (1) `π'` is smooth
  have hker := isSmoothConnAffineKer_of_torus π' r e he_inj he_ker he_nat
  haveI : QuasiCompact π'.left := by
    haveI : QuasiCompact (π'.left ≫ B'.X.hom) := by
      rw [Over.w π']; change QuasiCompact (pullback.snd U.hom _); infer_instance
    exact QuasiCompact.of_comp π'.left B'.X.hom
  have hsmπ' : Smooth π'.left := by
    have hP := (isPullback_shear π').map (Over.forget _)
    have hfst : Smooth ((Over.forget _).map (fst ((Over.pullback (sφ (φbar k))).obj U) (kerObj π'))) := by
      haveI := hker.1
      change Smooth (pullback.fst _ (kerObj π').hom); infer_instance
    exact MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hP ⟨⟨hsu, hfl⟩, (inferInstance : QuasiCompact π'.left)⟩ hfst
  -- (2) `π₁` and `X₁`
  have sqπ := isPullback_π' π' π₁ c hc hcompat
  have hq₂ := fieldMap_fpqc' k₁ (AlgebraicClosure k)
  have hcQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) c :=
    ⟨⟨MorphismProperty.of_isPullback (P := @Surjective) hc.flip hq₂.1.1,
      MorphismProperty.of_isPullback (P := @Flat) hc.flip hq₂.1.2⟩,
      MorphismProperty.of_isPullback (P := @QuasiCompact) hc.flip hq₂.2⟩
  haveI : Smooth π₁.left := MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) sqπ hcQ hsmπ'
  haveI : Surjective π₁.left := MorphismProperty.of_isPullback_of_descendsAlong (P := @Surjective)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) sqπ hcQ hsu
  obtain ⟨hX₁p, hX₁s, hX₁g⟩ := abVar_props_of_field_pullback B' hc
  haveI := hX₁p
  haveI := hX₁s
  haveI := hX₁g
  haveI : QuasiCompact π₁.left := by
    haveI : QuasiCompact (π₁.left ≫ X₁.hom) := by
      rw [Over.w π₁]; change QuasiCompact (pullback.snd U.hom _); infer_instance
    exact QuasiCompact.of_comp π₁.left X₁.hom
  -- (3) group structure on `X₁`
  letI : GrpObj ((Over.pullback (qq k k₁)).obj U) := Functor.grpObjObj
  let θ₁ : (Over.pullback (q₂ k k₁)).obj X₁ ≅ B'.X := Over.isoMk hc.isoPullback.symm (by simp)
  have hθ₁eq : (Over.pullback (q₂ k k₁)).map π₁ ≫ θ₁.hom = Ecomp U k₁ ≫ π' := by
    apply Over.OverMorphism.ext
    apply hc.hom_ext
    · simp only [Over.comp_left, Category.assoc, θ₁, Over.isoMk_hom_left, Iso.symm_hom,
        IsPullback.isoPullback_inv_fst, Over.pullback_map_left, pullback.lift_fst]
      rw [hcompat, ← Category.assoc, Ecomp_left_rr]
      rfl
    · rw [Over.w, Over.w]
  have hθ₁ : letI : GrpObj ((Over.pullback (q₂ k k₁)).obj ((Over.pullback (qq k k₁)).obj U)) :=
      Functor.grpObjObj
      IsMonHom ((Over.pullback (q₂ k k₁)).map π₁ ≫ θ₁.hom) := by
    letI : GrpObj ((Over.pullback (q₂ k k₁)).obj ((Over.pullback (qq k k₁)).obj U)) := Functor.grpObjObj
    rw [hθ₁eq]
    haveI := isMonHom_Ecomp (U := U) (k₁ := k₁)
    infer_instance
  obtain ⟨GX₁, hπ₁m⟩ := exists_grpObj π₁ (cong_of_faithful (Over.pullback (q₂ k k₁)) π₁ θ₁ hθ₁)
  -- (4) `KI` and finiteness
  haveI : IsFinite (qq k k₁) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  obtain ⟨hqfl, hqsu⟩ := fpqc_specField k k₁
  haveI : Flat (qq k k₁) := hqfl
  haveI : Surjective (qq k k₁) := hqsu
  haveI : LocallyOfFinitePresentation (qq k k₁) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
    exact RingHom.FinitePresentation.of_finiteType.mp
      ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp
        (inferInstanceAs (LocallyOfFiniteType (qq k k₁))))
  have hKI := KI_of_toric_kernel π' hπ r e he_ker he_nat X₁ π₁ c hc hcompat
  have hfin := @finite_affine_of_grp k₁ _ X₁ GX₁ _ _ _
  -- (5) descent
  obtain ⟨B₀, d, πr, hsq, hfac, hover⟩ := exists_descent hKI hfin
  let πo : U ⟶ B₀ := Over.homMk πr hover
  have sq2 : IsPullback π₁.left (pullback.fst U.hom (qq k k₁)) d πr := by
    refine IsPullback.of_right (h₁₂ := X₁.hom) (h₂₂ := B₀.hom) (v₁₃ := qq k k₁) ?_ hfac.symm hsq.flip
    rw [Over.w π₁, hover]
    exact (IsPullback.of_hasPullback U.hom (qq k k₁)).flip
  have hq := fieldMap_fpqc' k k₁
  have hdQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) d :=
    ⟨⟨MorphismProperty.of_isPullback (P := @Surjective) hsq.flip hq.1.1,
      MorphismProperty.of_isPullback (P := @Flat) hsq.flip hq.1.2⟩,
      MorphismProperty.of_isPullback (P := @QuasiCompact) hsq.flip hq.2⟩
  haveI : Smooth πr := MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) sq2 hdQ inferInstance
  haveI : Surjective πr := MorphismProperty.of_isPullback_of_descendsAlong (P := @Surjective)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) sq2 hdQ inferInstance
  let X₁v : PkgI3.AbVar k₁ := @PkgI3.AbVar.mk k₁ _ X₁ GX₁ _ _ _
  obtain ⟨hBp, hBs, hBg⟩ := abVar_props_of_field_pullback (X := B₀) X₁v hsq
  haveI := hBp
  haveI := hBs
  haveI := hBg
  haveI : QuasiCompact πo.left := by
    haveI : QuasiCompact (πr ≫ B₀.hom) := by rw [hover]; infer_instance
    exact QuasiCompact.of_comp πr B₀.hom
  haveI : Flat πo.left := (inferInstance : Flat πr)
  haveI : Surjective πo.left := (inferInstance : Surjective πr)
  -- (6) comparison with `B'`
  have hpaste : IsPullback (c ≫ d) B'.X.hom B₀.hom (sφ (φbar k)) := by
    have := hc.paste_horiz hsq
    rwa [q₂_qq] at this
  let Θ : (Over.pullback (sφ (φbar k))).obj B₀ ≅ B'.X := Over.isoMk hpaste.isoPullback.symm (by simp)
  have hΘ : (Over.pullback (sφ (φbar k))).map πo ≫ Θ.hom = π' := by
    apply Over.OverMorphism.ext
    apply hpaste.hom_ext
    · simp only [Over.comp_left, Category.assoc, Θ, Over.isoMk_hom_left, Iso.symm_hom]
      rw [IsPullback.isoPullback_inv_fst, ← Category.assoc π'.left, hcompat, Category.assoc, ← hfac,
        ← Category.assoc]
      simp only [Over.pullback_map_left, pullback.lift_fst, πo, Over.homMk_left]
      congr 1
    · rw [Over.w, Over.w]
  have hθB : IsMonHom ((Over.pullback (sφ (φbar k))).map πo ≫ Θ.hom) := by rw [hΘ]; exact hπ
  obtain ⟨GB₀, hπom⟩ := exists_grpObj πo (cong_of_faithful (Over.pullback (sφ (φbar k))) πo Θ hθB)
  let B : PkgI3.AbVar k := @PkgI3.AbVar.mk k _ B₀ GB₀ _ _ _
  refine ⟨B, πo, hπom, inferInstance, inferInstance, ?_⟩
  -- (7) the kernel condition
  letI : GrpObj ((Over.pullback (sφ (φbar k))).obj B.X) := Functor.grpObjObj
  intro R _ _ u
  have h1 : (Over.pullback (sφ (φbar k))).map πo = π' ≫ Θ.inv := by
    rw [← hΘ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hη : (η[(Over.pullback (sφ (φbar k))).obj B.X] : 𝟙_ _ ⟶ _) = η[B'.X] ≫ Θ.inv := by
    haveI : IsMonHom ((Over.pullback (sφ (φbar k))).map πo) := inferInstance
    rw [← IsMonHom.one_hom ((Over.pullback (sφ (φbar k))).map πo), h1, ← Category.assoc,
      IsMonHom.one_hom π']
  have hone : (1 : algPt (AlgebraicClosure k) R ⟶ (Over.pullback (sφ (φbar k))).obj B.X) =
      (1 : algPt (AlgebraicClosure k) R ⟶ B'.X) ≫ Θ.inv := by
    rw [Hom.one_def, Hom.one_def, Category.assoc, hη]
  rw [h1, hone, ← Category.assoc, cancel_mono]

end FiniteStage

/- The finite-stage assembly above specializes to the geometric closure. -/
theorem descend_semiabelian_quotient :
  ∀ (k : Type) [Field k] (U : Over (Spec (CommRingCat.of k))) [GrpObj U],
    Smooth U.hom → QuasiCompact U.hom → ConnectedSpace U.left →
    letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
    ∀ (B' : PkgI3.AbVar (AlgebraicClosure k)) (π' : (Over.pullback (sφ (φbar k))).obj U ⟶ B'.X),
      IsMonHom π' → Flat π'.left → Surjective π'.left →
      ∀ (r : ℕ) (e : ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R],
          (Fin r → Rˣ) →* (algPt (AlgebraicClosure k) R ⟶ (Over.pullback (sφ (φbar k))).obj U)),
        (∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R], Function.Injective (e R)) →
        (∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R]
          (u : algPt (AlgebraicClosure k) R ⟶ (Over.pullback (sφ (φbar k))).obj U),
          u ≫ π' = 1 ↔ u ∈ (e R).range) →
        (∀ (R S : Type) [CommRing R] [Algebra (AlgebraicClosure k) R] [CommRing S]
          [Algebra (AlgebraicClosure k) S] (f : R →ₐ[AlgebraicClosure k] S) (t : Fin r → Rˣ),
          e S (fun i => Units.map (f : R →* S) (t i)) = algPtMap f ≫ e R t) →
        ∃ (B : PkgI3.AbVar k) (π : U ⟶ B.X),
          letI : GrpObj ((Over.pullback (sφ (φbar k))).obj B.X) := Functor.grpObjObj
          IsMonHom π ∧ Flat π.left ∧ Surjective π.left ∧
          ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R]
            (u : algPt (AlgebraicClosure k) R ⟶ (Over.pullback (sφ (φbar k))).obj U),
            u ≫ (Over.pullback (sφ (φbar k))).map π = 1 ↔ u ≫ π' = 1 := by
  intro k _ U _ hsm hqc hconn B' π' hπ hfl hsu r e he_inj he_ker he_nat
  haveI := hsm
  haveI := hqc
  haveI : LocallyOfFiniteType U.hom := inferInstance
  obtain ⟨k₁, hfd, X₁, π₁, c, hc, hcompat⟩ := spread U B' π'
  haveI := hfd
  haveI : Algebra.IsAlgebraic k₁ (AlgebraicClosure k) := Algebra.IsAlgebraic.tower_top (K := k) k₁
  exact descend_quotient_finite_stage hqc π' hπ hfl hsu r e he_inj he_ker he_nat X₁ π₁ c hc hcompat

#print axioms descend_quotient_finite_stage
#print axioms descend_semiabelian_quotient

end SZRaynaud

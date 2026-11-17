import ZInQKernel.Contrib.OneProof.NeronExtLocal
import ZInQKernel.Contrib.OneProof.NeronExtAb
import ZInQKernel.Contrib.CloudW01Spread.StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.ClosedImmersion

/-! # neron-ext: spreading out a separated smooth scheme over `R_𝔭` -/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry
open NumberField

namespace NeronExt

open GapBLR ZInQ.Contrib.SpreadOut

section Sep

/-- `X ×_Z T → T` is separated iff the base change of the diagonal of `X → Z` is a closed immersion. -/
theorem isSeparated_pb_iff {Z T : Scheme.{0}} (π : T ⟶ Z) (X : Over Z) :
    IsClosedImmersion ((Over.pullback π).map
      (Over.homMk (pullback.diagonal X.hom) (by simp) :
        Over.mk X.hom ⟶ Over.mk (pullback.snd X.hom X.hom ≫ X.hom))).left ↔
      IsSeparated ((Over.pullback π).obj (Over.mk X.hom)).hom := by
  have e1 : ((Over.pullback π).obj (Over.mk X.hom)).hom =
      (pullbackSymmetry X.hom π).hom ≫ pullback.fst π X.hom := by
    simp
  have hd := diagonal_pullback_fst π X.hom
  rw [e1, MorphismProperty.cancel_left_of_respectsIso (P := @IsSeparated)]
  constructor
  · intro h
    refine ⟨?_⟩
    rw [hd]
    infer_instance
  · intro h
    have h1 := h.isClosedImmersion_diagonal
    rw [hd] at h1
    have h2 : IsClosedImmersion (((Over.pullback π).map
      (Over.homMk (pullback.diagonal X.hom) (by simp) :
        Over.mk X.hom ⟶ Over.mk (pullback.snd X.hom X.hom ≫ X.hom))).left ≫
          (diagonalObjPullbackFstIso π X.hom).inv) :=
      (MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion) _ _).mp h1
    exact (MorphismProperty.cancel_right_of_respectsIso (P := @IsClosedImmersion) _ _).mp h2

theorem isSeparated_of_iso {S : Scheme.{0}} {X Y : Over S} (e : X ≅ Y) [IsSeparated Y.hom] :
    IsSeparated X.hom := by
  rw [← Over.w e.hom]
  haveI : IsIso e.hom.left := ⟨e.inv.left, by rw [← Over.comp_left, e.hom_inv_id]; rfl,
    by rw [← Over.comp_left, e.inv_hom_id]; rfl⟩
  infer_instance

end Sep

/-- Base change along equal maps. -/
noncomputable def pbCongr {A B : Scheme.{0}} {f g : A ⟶ B} (h : f = g) (X : Over B) :
    (Over.pullback f).obj X ≅ (Over.pullback g).obj X := by
  subst h; exact Iso.refl _

section SpreadSep

variable {R : Type} [CommRing R] {𝔭 : Ideal R} [𝔭.IsPrime] (R𝔭 : Type) [CommRing R𝔭] [Algebra R R𝔭]
  [IsLocalization.AtPrime R𝔭 𝔭]

/-- **Spreading out a smooth separated quasi-compact `R_𝔭`-scheme** to some `R[1/s]`, `s ∉ 𝔭`
(EGA IV 8.8.2 (ii), 17.7.8 (ii) proved in `CloudW01Spread`, and the descent of closed immersions,
Stacks 01ZP, proved in `CloudW01Spread/StacksFrontier`, applied to the diagonal). -/
theorem exists_spread_sep (V : Over (Spec (CommRingCat.of R𝔭))) [Smooth V.hom] [IsSeparated V.hom]
    [QuasiCompact V.hom] :
    ∃ (a : (GapBLR.Idx 𝔭)ᵒᵖ) (W : Over ((specDiag 𝔭).obj a)), Smooth W.hom ∧ IsSeparated W.hom ∧
      QuasiCompact W.hom ∧ Nonempty ((Over.pullback ((specCone 𝔭 R𝔭).π.app a)).obj W ≅ V) := by
  let D := specDiag 𝔭
  let c := specCone 𝔭 R𝔭
  have hc : IsLimit c := specConeIsLimit 𝔭 R𝔭
  obtain ⟨i, Xi, hl, hq, hs, ⟨e⟩⟩ := EGAIV_8_8_2_ii_proof (GapBLR.Idx 𝔭) D c hc V inferInstance
    inferInstance inferInstance
  haveI := hl; haveI := hq; haveI := hs
  have hsm : Smooth ((Over.pullback (c.π.app i)).obj Xi).hom := smooth_of_iso e
  obtain ⟨j₁, a₁, hj₁⟩ := EGAIV_17_7_8_ii_proof (GapBLR.Idx 𝔭) D c hc i Xi hl hq hs hsm
  -- separatedness, via the diagonal
  haveI : CompactSpace Xi.left := QuasiCompact.compactSpace_of_compactSpace Xi.hom
  haveI : QuasiSeparatedSpace Xi.left := quasiSeparatedSpace_of_quasiSeparated Xi.hom
  let Y₀ : Over (D.obj i) := Over.mk (pullback.snd Xi.hom Xi.hom ≫ Xi.hom)
  haveI : QuasiCompact Y₀.hom := show QuasiCompact (pullback.snd Xi.hom Xi.hom ≫ Xi.hom) from inferInstance
  haveI : QuasiSeparated Y₀.hom :=
    show QuasiSeparated (pullback.snd Xi.hom Xi.hom ≫ Xi.hom) from inferInstance
  haveI : CompactSpace Y₀.left := QuasiCompact.compactSpace_of_compactSpace Y₀.hom
  haveI : QuasiSeparatedSpace Y₀.left := quasiSeparatedSpace_of_quasiSeparated Y₀.hom
  haveI : CompactSpace (Over.mk Xi.hom).left := ‹CompactSpace Xi.left›
  haveI : QuasiSeparatedSpace (Over.mk Xi.hom).left := ‹QuasiSeparatedSpace Xi.left›
  let f₀ : Over.mk Xi.hom ⟶ Y₀ := Over.homMk (pullback.diagonal Xi.hom) (by simp [Y₀])
  haveI : LocallyOfFiniteType f₀.left := by
    have : f₀.left ≫ pullback.fst Xi.hom Xi.hom = 𝟙 _ := by simp [f₀]
    haveI : LocallyOfFiniteType (f₀.left ≫ pullback.fst Xi.hom Xi.hom) := by
      rw [this]; infer_instance
    exact locallyOfFiniteType_of_comp f₀.left (pullback.fst Xi.hom Xi.hom)
  haveI : IsSeparated ((Over.pullback (c.π.app i)).obj (Over.mk Xi.hom)).hom :=
    isSeparated_of_iso e
  haveI : IsClosedImmersion ((Over.pullback (c.π.app i)).map f₀).left :=
    (isSeparated_pb_iff (c.π.app i) Xi).mpr inferInstance
  obtain ⟨j₂, a₂, hj₂⟩ := exists_isClosedImmersion_baseChange_of_isLimit D c hc i
    (Over.mk Xi.hom) Y₀ f₀
  have hsep₂ : IsSeparated ((Over.pullback (D.map a₂)).obj (Over.mk Xi.hom)).hom :=
    (isSeparated_pb_iff (D.map a₂) Xi).mp hj₂
  -- a common stage
  obtain ⟨k, b₁, b₂, -⟩ := IsCofiltered.cospan a₁ a₂
  let b : k ⟶ i := b₁ ≫ a₁
  have hb : b₂ ≫ a₂ = b := Subsingleton.elim _ _
  let W : Over (D.obj k) := (Over.pullback (D.map b)).obj Xi
  have eW₁ : W ≅ (Over.pullback (D.map b₁)).obj ((Over.pullback (D.map a₁)).obj Xi) :=
    eqToIso (by simp only [W, b, Functor.map_comp]) ≪≫ (Over.pullbackComp _ _).app Xi
  have eW₂ : W ≅ (Over.pullback (D.map b₂)).obj ((Over.pullback (D.map a₂)).obj (Over.mk Xi.hom)) :=
    eqToIso (by simp only [W, ← hb, Functor.map_comp]; rfl) ≪≫ (Over.pullbackComp _ _).app _
  refine ⟨k, W, ?_, ?_, ?_, ⟨?_⟩⟩
  · haveI : Smooth ((Over.pullback (D.map a₁)).obj Xi).hom := hj₁
    haveI : Smooth ((Over.pullback (D.map b₁)).obj ((Over.pullback (D.map a₁)).obj Xi)).hom :=
      show Smooth (pullback.snd _ _) from inferInstance
    exact smooth_of_iso eW₁
  · haveI := hsep₂
    haveI : IsSeparated ((Over.pullback (D.map b₂)).obj
        ((Over.pullback (D.map a₂)).obj (Over.mk Xi.hom))).hom :=
      show IsSeparated (pullback.snd _ _) from inferInstance
    exact isSeparated_of_iso eW₂
  · show QuasiCompact (pullback.snd _ _)
    infer_instance
  · exact (Over.pullbackComp (c.π.app k) (D.map b)).symm.app Xi ≪≫ pbCongr (c.w b) Xi ≪≫ e

end SpreadSep

/-! ## Spreading a morphism of generic fibres -/

section SpreadGen

variable {L : Type} [Field L] [NumberField L]

theorem isLocalization_bot : IsLocalization.AtPrime L (⊥ : Ideal (𝓞 L)) := by
  have h : (⊥ : Ideal (𝓞 L)).primeCompl = nonZeroDivisors (𝓞 L) := by
    ext x
    simp [Ideal.primeCompl, mem_nonZeroDivisors_iff_ne_zero]
  unfold IsLocalization.AtPrime
  rw [h]
  infer_instance

/-- The generic stages `Spec 𝓞_L[1/s]`, `s ≠ 0`. -/
abbrev GIdx (L : Type) [Field L] [NumberField L] := (GapBLR.Idx (⊥ : Ideal (𝓞 L)))ᵒᵖ

/-- The open `D(s) ⊆ Spec 𝓞_L` of a generic stage. -/
noncomputable def Dg (s : GIdx L) : (S L).Opens := (ej s).opensRange

theorem mem_Dg {s : GIdx L} {x : S L} :
    x ∈ Dg s ↔ s.unop.s ∉ (PrimeSpectrum.asIdeal (R := 𝓞 L) x) := by
  have hrange := Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of (𝓞 L)) s.unop.s
  exact (Eq.to_iff (congrArg (x ∈ ·) hrange)).trans (PrimeSpectrum.mem_basicOpen _ _)

theorem jL_preimage_Dg (s : GIdx L) : (jL L) ⁻¹ᵁ Dg s = ⊤ := by
  let q : PrimeSpectrum L := ⟨⊥, Ideal.isPrime_bot⟩
  apply jL_preimage_eq_top L
  refine ⟨jL L q, mem_Dg.2 ?_⟩
  intro hs
  have h1 : algebraMap (𝓞 L) L s.unop.s ∈ q.asIdeal := hs
  have h2 : algebraMap (𝓞 L) L s.unop.s = 0 := h1
  exact s.unop.hs ((FaithfulSMul.algebraMap_injective (𝓞 L) L) (h2.trans (map_zero _).symm) ▸
    (Ideal.zero_mem _))

theorem isAffineHom_bcDiag_map {R : Type} [CommRing R] {𝔭 : Ideal R} [𝔭.IsPrime] {V : Scheme.{0}}
    (v : V ⟶ Spec (CommRingCat.of R)) {i j : (GapBLR.Idx 𝔭)ᵒᵖ} (f : i ⟶ j) :
    IsAffineHom ((bcDiag 𝔭 v).map f) := by
  let m : pullback (ej i) v ⟶ pullback (ej j) v := (bcDiag 𝔭 v).map f
  have hm : m = pullback.lift (pullback.fst (ej i) v ≫ (specDiag 𝔭).map f) (pullback.snd (ej i) v)
      (by rw [Category.assoc, map_ej, pullback.condition]) := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      simp [m, overDiag]
    · rw [pullback.lift_snd]
      simp [m, overDiag]
  have houter : IsPullback (m ≫ pullback.snd (ej j) v) (pullback.fst (ej i) v) v
      ((specDiag 𝔭).map f ≫ ej j) := by
    rw [map_ej, hm, pullback.lift_snd]
    exact (IsPullback.of_hasPullback (ej i) v).flip
  have hsq : m ≫ pullback.fst (ej j) v = pullback.fst (ej i) v ≫ (specDiag 𝔭).map f := by
    rw [hm, pullback.lift_fst]
  have hleft := IsPullback.of_right houter hsq (IsPullback.of_hasPullback (ej j) v).flip
  exact MorphismProperty.of_isPullback hleft.flip (inferInstance : IsAffineHom ((specDiag 𝔭).map f))

/-- **Spreading out a morphism of generic fibres** (Stacks 01ZC, Mathlib's
`Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`, over `Spec L = lim Spec 𝓞_L[1/s]`). -/
theorem spread_generic (V X : Over (S L)) [QuasiCompact V.hom] [QuasiSeparated V.hom]
    [LocallyOfFinitePresentation X.hom] (a : (gf L).obj V ⟶ (gf L).obj X) :
    ∃ (s : GIdx L) (g : res V (Dg s) ⟶ X), (gf L).map g = (gf L).map (resι V (Dg s)) ≫ a := by
  haveI := isLocalization_bot (L := L)
  let v := V.hom
  let 𝔭 : Ideal (𝓞 L) := ⊥
  let jR := Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L))
  haveI : CompactSpace V.left := QuasiCompact.compactSpace_of_compactSpace V.hom
  haveI : QuasiSeparatedSpace V.left := quasiSeparatedSpace_of_quasiSeparated V.hom
  haveI : ∀ {i j : GIdx L} (f : i ⟶ j), IsAffineHom ((bcDiag 𝔭 v).map f) := fun f =>
    isAffineHom_bcDiag_map v f
  haveI : ∀ i : GIdx L, CompactSpace ((bcDiag 𝔭 v).obj i) := fun i => by
    change CompactSpace ↥(pullback (ej i) V.hom)
    infer_instance
  haveI : ∀ i : GIdx L, QuasiSeparatedSpace ((bcDiag 𝔭 v).obj i) := fun i => by
    change QuasiSeparatedSpace ↥(pullback (ej i) V.hom)
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.snd (ej i) V.hom ≫ V.hom)
  let a' : pullback jR v ⟶ X.left :=
    (pullbackSymmetry jR v).hom ≫ a.left ≫ pullback.fst X.hom (jL L)
  have hwa : a.left ≫ pullback.snd X.hom (jL L) = pullback.snd V.hom (jL L) := Over.w a
  have ha'X : a' ≫ X.hom = pullback.fst jR v ≫ jR := by
    simp only [a', Category.assoc]
    rw [pullback.condition, ← Category.assoc a.left, hwa, pullbackSymmetry_hom_comp_snd_assoc]
  have ha' : (bcCone 𝔭 L v).π ≫ bcT 𝔭 v = (Functor.const _).map (a' ≫ X.hom) := by
    ext i
    rw [ha'X]
    show ((bcCone 𝔭 L v).π.app i ≫ pullback.snd (ej i) v) ≫ v = _
    rw [bcπ_snd, ← pullback.condition]
    rfl
  obtain ⟨s, g, hg1, hg2⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (bcDiag 𝔭 v) (bcT 𝔭 v) X.hom (bcCone 𝔭 L v) (bcConeIsLimit 𝔭 L v) a' ha'
  let g' : pullback (ej s) v ⟶ X.left := g
  have hg2' : g' ≫ X.hom = pullback.snd (ej s) v ≫ v := hg2
  have hg1' : bcπ 𝔭 L v s ≫ g' = a' := hg1
  -- `V ∩ v⁻¹ D(s) ≅ D(s) ×_{𝓞_L} V`
  let ι := (V.hom ⁻¹ᵁ Dg s).ι
  have hrange : Set.range ι = Set.range (pullback.snd (ej s) v) := by
    rw [Scheme.Opens.range_ι, IsOpenImmersion.range_pullbackSnd]
    rfl
  let θ := IsOpenImmersion.isoOfRangeEq ι (pullback.snd (ej s) v) hrange
  have hθ : θ.hom ≫ pullback.snd (ej s) v = ι := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  let G : res V (Dg s) ⟶ X := Over.homMk (θ.hom ≫ g') (by
    show (θ.hom ≫ g') ≫ X.hom = ι ≫ V.hom
    rw [Category.assoc, hg2', ← Category.assoc, hθ])
  refine ⟨s, G, ?_⟩
  -- compare on the generic fibre
  let P := pullback (res V (Dg s)).hom (jL L)
  let m : P ⟶ pullback jR v :=
    pullback.lift (pullback.snd _ _) (pullback.fst _ _ ≫ ι) (by
      show _ = (pullback.fst (ι ≫ V.hom) (jL L) ≫ ι) ≫ V.hom
      rw [Category.assoc, pullback.condition]
      rfl)
  have hm1 : m ≫ (pullbackSymmetry jR v).hom = pullback.lift (pullback.fst _ _ ≫ ι) (pullback.snd _ _)
      (by show (pullback.fst (ι ≫ V.hom) (jL L) ≫ ι) ≫ V.hom = _
          rw [Category.assoc, pullback.condition]
          rfl) := by
    apply pullback.hom_ext <;> simp [m]
  have hm2 : m ≫ bcπ 𝔭 L v s = pullback.fst _ _ ≫ θ.hom := by
    apply pullback.hom_ext
    · rw [← cancel_mono (ej s)]
      have l0 : bcπ 𝔭 L v s ≫ pullback.fst (ej s) v ≫ ej s = pullback.fst jR v ≫ jR :=
        (pullback.lift_fst_assoc _ _ _ _).trans ((Category.assoc _ _ _).trans
          (congrArg (pullback.fst jR v ≫ ·) (toP_ej L s)))
      simp only [Category.assoc]
      rw [l0, show pullback.fst (ej s) v ≫ ej s = pullback.snd (ej s) v ≫ v from pullback.condition,
        ← Category.assoc θ.hom, hθ, ← Category.assoc m, pullback.lift_fst]
      show pullback.snd (ι ≫ V.hom) (jL L) ≫ jL L = pullback.fst (ι ≫ V.hom) (jL L) ≫ ι ≫ V.hom
      exact pullback.condition.symm
    · simp only [Category.assoc, hθ]
      rw [show bcπ 𝔭 L v s ≫ pullback.snd (ej s) v = pullback.snd jR v from bcπ_snd 𝔭 L v s]
      simp [m]
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.comp_left, Over.pullback_map_left, pullback.lift_fst, Category.assoc,
      pullback.lift_fst_assoc]
    show pullback.fst _ _ ≫ θ.hom ≫ g' = _
    rw [← Category.assoc, ← hm2, Category.assoc, hg1']
    simp only [a', ← Category.assoc]
    rw [hm1]
    rfl
  · simp only [Over.comp_left, Over.pullback_map_left, pullback.lift_snd, Category.assoc]
    rw [hwa]
    simp

end SpreadGen

end NeronExt

#print axioms NeronExt.spread_generic
#print axioms NeronExt.exists_spread_sep

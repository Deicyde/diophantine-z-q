import ZInQKernel.Contrib.OneProof.NeronDedekind.Glue
import ZInQKernel.Contrib.OneProof.NeronExtSpread

/-! # Spreading out a morphism of generic fibres over a domain

This is the domain-general form of `NeronExt.spread_generic`. The affine transition-map lemma and
spreading out of smooth separated schemes at an arbitrary prime are already ring-generic in
`NeronExtSpread`. Here the localization is at the zero prime, so the limit is the fraction field.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry GapBLR

namespace NeronExtDedekind

variable {D : Type} [CommRing D] [IsDomain D] {L : Type} [Field L] [Algebra D L]
  [IsFractionRing D L]

theorem isLocalization_bot : IsLocalization.AtPrime L (⊥ : Ideal D) := by
  have h : (⊥ : Ideal D).primeCompl = nonZeroDivisors D := by
    ext x
    simp [Ideal.primeCompl, mem_nonZeroDivisors_iff_ne_zero]
  unfold IsLocalization.AtPrime
  rw [h]
  infer_instance

/-- The generic stages `Spec D[1/s]` with `s ≠ 0`. -/
abbrev GIdx (D : Type) [CommRing D] := (GapBLR.Idx (⊥ : Ideal D))ᵒᵖ

theorem ne_zero_of_idx (s : GIdx D) : s.unop.s ≠ 0 :=
  fun h => s.unop.hs (h ▸ Ideal.zero_mem _)

/-- The open `D(s) ⊆ Spec D` of a generic stage. -/
noncomputable def Dg (s : GIdx D) : (S D).Opens := (ej s).opensRange

theorem mem_Dg {s : GIdx D} {x : S D} :
    x ∈ Dg s ↔ s.unop.s ∉ (PrimeSpectrum.asIdeal (R := D) x) := by
  have hrange := Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of D) s.unop.s
  exact (Eq.to_iff (congrArg (x ∈ ·) hrange)).trans (PrimeSpectrum.mem_basicOpen _ _)

/-- **Spreading out a morphism of generic fibres** (Stacks 01ZC, Mathlib's
`Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`, over `Spec L = lim Spec D[1/s]`). -/
theorem spread_generic (V X : Over (S D)) [QuasiCompact V.hom] [QuasiSeparated V.hom]
    [LocallyOfFinitePresentation X.hom] (a : (gf D L).obj V ⟶ (gf D L).obj X) :
    ∃ (s : GIdx D) (g : res V (Dg s) ⟶ X), (gf D L).map g = (gf D L).map (resι V (Dg s)) ≫ a := by
  haveI := isLocalization_bot (D := D) (L := L)
  let v := V.hom
  let 𝔭 : Ideal D := ⊥
  let jR := Spec.map (CommRingCat.ofHom (algebraMap D L))
  haveI : CompactSpace V.left := QuasiCompact.compactSpace_of_compactSpace V.hom
  haveI : QuasiSeparatedSpace V.left := quasiSeparatedSpace_of_quasiSeparated V.hom
  haveI : ∀ {i j : GIdx D} (f : i ⟶ j), IsAffineHom ((bcDiag 𝔭 v).map f) := fun f =>
    NeronExt.isAffineHom_bcDiag_map v f
  haveI : ∀ i : GIdx D, CompactSpace ((bcDiag 𝔭 v).obj i) := fun i => by
    change CompactSpace ↥(pullback (ej i) V.hom)
    infer_instance
  haveI : ∀ i : GIdx D, QuasiSeparatedSpace ((bcDiag 𝔭 v).obj i) := fun i => by
    change QuasiSeparatedSpace ↥(pullback (ej i) V.hom)
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.snd (ej i) V.hom ≫ V.hom)
  let a' : pullback jR v ⟶ X.left :=
    (pullbackSymmetry jR v).hom ≫ a.left ≫ pullback.fst X.hom (jL D L)
  have hwa : a.left ≫ pullback.snd X.hom (jL D L) = pullback.snd V.hom (jL D L) := Over.w a
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
  -- Identify the restriction of `V` with `D(s) ×_D V`.
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
  let P := pullback (res V (Dg s)).hom (jL D L)
  let m : P ⟶ pullback jR v :=
    pullback.lift (pullback.snd _ _) (pullback.fst _ _ ≫ ι) (by
      show _ = (pullback.fst (ι ≫ V.hom) (jL D L) ≫ ι) ≫ V.hom
      rw [Category.assoc, pullback.condition]
      rfl)
  have hm1 : m ≫ (pullbackSymmetry jR v).hom = pullback.lift (pullback.fst _ _ ≫ ι) (pullback.snd _ _)
      (by show (pullback.fst (ι ≫ V.hom) (jL D L) ≫ ι) ≫ V.hom = _
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
      show pullback.snd (ι ≫ V.hom) (jL D L) ≫ jL D L = pullback.fst (ι ≫ V.hom) (jL D L) ≫ ι ≫ V.hom
      exact pullback.condition.symm
    · simp only [Category.assoc, hθ]
      rw [show bcπ 𝔭 L v s ≫ pullback.snd (ej s) v = pullback.snd jR v from bcπ_snd 𝔭 L v s]
      simp [m]
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.comp_left, Over.pullback_map_left, pullback.lift_fst, Category.assoc]
    show pullback.fst _ _ ≫ θ.hom ≫ g' = _
    rw [← Category.assoc, ← hm2, Category.assoc, hg1']
    simp only [a', ← Category.assoc]
    rw [hm1]
    rfl
  · simp only [Over.comp_left, Over.pullback_map_left, pullback.lift_snd, Category.assoc]
    rw [hwa]
    simp

end NeronExtDedekind

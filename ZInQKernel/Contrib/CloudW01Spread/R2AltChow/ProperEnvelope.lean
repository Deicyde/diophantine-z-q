/-
Copyright (c) 2026 AxiomMath contributors and the H65 proof campaign.
Released under Apache 2.0; see ../LICENSE and ../H65_NOTICE.md.

Adapted from AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b:
  StacksFrontier/AlgebraicGeometry/ChowNoetherian/RelativeProduct.lean
  StacksFrontier/AlgebraicGeometry/ChowNoetherian/Basic.lean
  StacksFrontier/AlgebraicGeometry/Limits/ChowLemma.lean

Modification notice (2026-11-14): retain the finite product of projective
spaces as a proper envelope instead of compressing it by a Segre embedding.
The dense-affine-cover, chart-image and proper-gluing arguments are retained.
All new declarations have the exclusive R2AltChow namespace. No original
supplier, fixed proposition, library definition or pin is modified.
-/
module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import ZInQKernel.Contrib.CloudW01Spread.ProperVendor.StacksFrontier.AlgebraicGeometry.AffineSpaceImmersion.Chow

/-!
# Chow modification into a proper envelope, without Segre

For properness descent it is unnecessary to immerse the modification into
one projective space: immersion into a scheme proper over the base suffices.
The finite fibre product of the chart projective spaces is already proper.
This file proves that weaker *intermediate conclusion*, unconditionally over
a Noetherian base. The unchanged H65 proposition is proved separately from it.
-/

set_option linter.style.haveILetI false

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u v

namespace ZInQ.Contrib.CloudW01Spread.R2AltChow

/-- A proper, surjective modification immersed over the base into a proper
scheme. This is a proved intermediate interface, not an assumed Chow axiom. -/
def HasProperEnvelope {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∃ (P : Scheme.{u}) (q : P ⟶ S) (X' : Scheme.{u}) (π : X' ⟶ X) (i : X' ⟶ P),
    IsProper q ∧ IsProper π ∧ Surjective π ∧ IsImmersion i ∧ π ≫ f = i ≫ q

variable {X S : Scheme.{u}}

/-- A finite nonempty list of projective charts has a proper fibre-product
envelope. Unlike the original projective-envelope lemma this needs no Segre
embedding or line-bundle construction. -/
theorem exists_properChartEnvelope {f : X ⟶ S} {I : Type v} (n : I → ℕ)
    (j : ∀ i, X ⟶ H65ProjectiveSpace (n i) S) (hj : ∀ i, IsImmersion (j i))
    (hcomm : ∀ i, j i ≫ (H65ProjectiveSpace (n i) S ↘ S) = f) :
    ∀ l : List I, l ≠ [] →
      ∃ (P : Scheme.{u}) (q : P ⟶ S) (a : X ⟶ P),
        IsProper q ∧ IsImmersion a ∧ a ≫ q = f ∧
          ∀ i ∈ l, ∃ ri : P ⟶ H65ProjectiveSpace (n i) S,
            ri ≫ (H65ProjectiveSpace (n i) S ↘ S) = q ∧ a ≫ ri = j i := by
  intro l
  induction l with
  | nil => simp
  | cons i₀ rest ih =>
      intro _
      cases rest with
      | nil =>
          refine ⟨H65ProjectiveSpace (n i₀) S, H65ProjectiveSpace (n i₀) S ↘ S, j i₀,
            inferInstance, hj i₀, hcomm i₀, fun i hi => ?_⟩
          obtain rfl : i = i₀ := by simpa using hi
          exact ⟨𝟙 _, Category.id_comp _, Category.comp_id _⟩
      | cons i₁ tail =>
          obtain ⟨P, q, a, hq, _, haq, hr⟩ := ih (List.cons_ne_nil _ _)
          letI : IsProper q := hq
          let p : H65ProjectiveSpace (n i₀) S ⟶ S := H65ProjectiveSpace (n i₀) S ↘ S
          haveI : IsProper p := by dsimp [p]; infer_instance
          let a' : X ⟶ pullback p q := pullback.lift (j i₀) a ((hcomm i₀).trans haq.symm)
          have ha'fst : a' ≫ pullback.fst p q = j i₀ := pullback.lift_fst _ _ _
          have ha'snd : a' ≫ pullback.snd p q = a := pullback.lift_snd _ _ _
          refine ⟨pullback p q, pullback.fst p q ≫ p, a', inferInstance, ?_, ?_, ?_⟩
          · haveI : IsImmersion (a' ≫ pullback.fst p q) := ha'fst ▸ hj i₀
            exact IsImmersion.of_comp a' (pullback.fst p q)
          · rw [← Category.assoc, ha'fst, hcomm i₀]
          · intro i hi
            obtain rfl | h := List.mem_cons.mp hi
            · exact ⟨pullback.fst p q, rfl, ha'fst⟩
            · obtain ⟨ri, hri, hari⟩ := hr i h
              exact ⟨pullback.snd p q ≫ ri, by rw [Category.assoc, hri, pullback.condition],
                by rw [← Category.assoc, ha'snd, hari]⟩

/-- The finite-index form of the preceding proper-envelope construction. -/
theorem exists_properChartEnvelope_of_finite {f : X ⟶ S} {I : Type v}
    [Finite I] [Nonempty I] (n : I → ℕ) (j : ∀ i, X ⟶ H65ProjectiveSpace (n i) S)
    (hj : ∀ i, IsImmersion (j i))
    (hcomm : ∀ i, j i ≫ (H65ProjectiveSpace (n i) S ↘ S) = f) :
    ∃ (P : Scheme.{u}) (q : P ⟶ S) (a : X ⟶ P),
      IsProper q ∧ IsImmersion a ∧ a ≫ q = f ∧
        ∀ i, ∃ ri : P ⟶ H65ProjectiveSpace (n i) S,
          ri ≫ (H65ProjectiveSpace (n i) S ↘ S) = q ∧ a ≫ ri = j i := by
  classical
  letI : Fintype I := Fintype.ofFinite I
  have hne : (Finset.univ : Finset I).toList ≠ [] := by
    simp [Finset.toList_eq_nil, Finset.univ_nonempty.ne_empty]
  obtain ⟨P, q, a, hq, ha, haq, hr⟩ := exists_properChartEnvelope n j hj hcomm _ hne
  exact ⟨P, q, a, hq, ha, haq, fun i => hr i (by simp)⟩

/-- The proper-envelope modification exists over every Noetherian base.
The proof is the actual Noetherian Chow construction, with its finite product
left uncompressed. No properness of the unknown source stage is assumed. -/
theorem hasProperEnvelope_of_noetherian (f : X ⟶ S) [IsNoetherian S]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] : HasProperEnvelope f := by
  classical
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  haveI : IsNoetherian X := ⟨⟩
  obtain ⟨F, U, hAffine, hcover, hSubset, hdense⟩ := exists_finite_dense_affine_open_cover (X := X)
  haveI : NoetherianSpace U.toScheme := U.ι.isOpenEmbedding.isInducing.noetherianSpace
  by_cases hF : F.Nonempty
  · let I := {V : X.Opens // V ∈ F}
    haveI : Nonempty I := by
      obtain ⟨V, hV⟩ := hF
      exact ⟨⟨V, hV⟩⟩
    haveI hNoeth : ∀ V : I, NoetherianSpace V.val.toScheme :=
      fun V => V.val.ι.isOpenEmbedding.isInducing.noetherianSpace
    have hcharts (V : I) : ∃ (n : ℕ) (i : V.val.toScheme ⟶ H65ProjectiveSpace n S),
        IsImmersion i ∧ i ≫ (H65ProjectiveSpace n S ↘ S) = V.val.ι ≫ f := by
      haveI : IsAffine V.val.toScheme := hAffine V.val V.property
      exact AlgebraicGeometry.hasAffineProjectiveChart S V.val.toScheme (V.val.ι ≫ f)
    choose n j hj hcomm using hcharts
    haveI hjI : ∀ V, IsImmersion (j V) := hj
    have hAimm (V : I) : IsImmersion (X.homOfLE (hSubset V.val V.property) ≫ j V) := by
      infer_instance
    have hAcomm (V : I) :
        (X.homOfLE (hSubset V.val V.property) ≫ j V) ≫ (H65ProjectiveSpace (n V) S ↘ S) =
          U.ι ≫ f := by
      rw [Category.assoc, hcomm, Scheme.homOfLE_ι_assoc]
    obtain ⟨P, q, a, hqproper, ha, haq, hr⟩ :=
      exists_properChartEnvelope_of_finite (f := U.ι ≫ f) n
        (fun V => X.homOfLE (hSubset V.val V.property) ≫ j V) hAimm hAcomm
    haveI : IsProper q := hqproper
    haveI : IsImmersion a := ha
    haveI : IsSchemeTheoreticallyDominant a.toImage := isSchemeTheoreticallyDominant_toImage a
    choose r hrq har using hr
    have hlocal (V : I) := exists_chart_of_image f q U V.val (hSubset V.val V.property) a (n V)
      (j V) (hcomm V) (r V) (hrq V) (har V)
    choose W k p s hk hp hsk hsp hkbase using hlocal
    haveI : ∀ V, IsOpenImmersion (k V) := hk
    haveI : ∀ V, IsProper (p V) := hp
    obtain ⟨Y, i, π, t, hi, hπ, hiq, hti, htπ, _⟩ :=
      exists_modification_of_dense_charts f (a.imageι ≫ q) U a.toImage
        (fun V : I => V.val)
        (fun x => by
          obtain ⟨V, hV, hxV⟩ := hcover x
          exact ⟨⟨V, hV⟩, hxV⟩)
        (fun V => hSubset V.val V.property) W k p s hsk hsp hkbase
    haveI : IsOpenImmersion i := hi
    haveI : IsProper π := hπ
    refine ⟨P, q, Y, π, i ≫ a.imageι, hqproper, hπ,
      surjective_of_isProper_of_dense_section π U t htπ hdense, inferInstance, ?_⟩
    rw [← hiq, Category.assoc]
  · haveI : IsEmpty X := ⟨fun x => by
      obtain ⟨V, hV, _⟩ := hcover x
      exact hF ⟨V, hV⟩⟩
    haveI : IsAffine X := inferInstance
    obtain ⟨m, e, he, hecomm⟩ := AlgebraicGeometry.hasAffineProjectiveChart S X f
    exact ⟨H65ProjectiveSpace m S, H65ProjectiveSpace m S ↘ S, X, 𝟙 X, e,
      inferInstance, inferInstance, inferInstance, he, by rw [Category.id_comp, hecomm]⟩

/-- Pull back a proper-envelope modification along a closed immersion of its
source. Used below only for the isomorphism furnished by finite-presentation
descent. -/
theorem HasProperEnvelope.of_isClosedImmersion {X Y S : Scheme.{u}} {j : X ⟶ Y} {g : Y ⟶ S}
    {f : X ⟶ S} [IsClosedImmersion j] (hf : j ≫ g = f) (hg : HasProperEnvelope g) :
    HasProperEnvelope f := by
  obtain ⟨P, q, Y', πY, iY, hq, hπY, hsurjY, hiY, hcommY⟩ := hg
  letI : IsProper q := hq
  letI : IsProper πY := hπY
  letI : Surjective πY := hsurjY
  letI : IsImmersion iY := hiY
  refine ⟨P, q, pullback j πY, pullback.fst j πY, pullback.snd j πY ≫ iY,
    hq, inferInstance, inferInstance, inferInstance, ?_⟩
  rw [← hf, pullback.condition_assoc, hcommY, Category.assoc]

/-- A proper-envelope modification is stable under arbitrary base change of
the entire diagram. -/
theorem HasProperEnvelope.of_isPullback {X S X' S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S}
    {f' : X' ⟶ S'} {p : X' ⟶ X} (hsq : IsPullback p f' f g) (hf : HasProperEnvelope f) :
    HasProperEnvelope f' := by
  obtain ⟨P, q, Y, π, i, hq, hπ, hsurj, himm, hcomm⟩ := hf
  letI : IsProper q := hq
  letI : IsProper π := hπ
  letI : Surjective π := hsurj
  letI : IsImmersion i := himm
  have hYsq : IsPullback (pullback.fst π p) (pullback.snd π p) π p :=
    IsPullback.of_hasPullback π p
  have hs : IsPullback (pullback.snd π p ≫ f') (pullback.fst π p) g (π ≫ f) :=
    hYsq.flip.paste_horiz hsq.flip
  rw [hcomm] at hs
  have t : IsPullback (pullback.snd q g) (pullback.fst q g) g q :=
    (IsPullback.of_hasPullback q g).flip
  let j : pullback π p ⟶ pullback q g :=
    t.lift (pullback.snd π p ≫ f') (pullback.fst π p ≫ i) (by rw [hs.w, Category.assoc])
  haveI : IsImmersion j :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsImmersion)
      (IsPullback.of_right' hs t).flip himm
  refine ⟨pullback q g, pullback.snd q g, pullback π p, pullback.snd π p, j,
    inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  exact (t.lift_fst _ _ _).symm

end ZInQ.Contrib.CloudW01Spread.R2AltChow

end

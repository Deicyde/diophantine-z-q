/-
Copyright (c) 2026 H5/NOS Round-2 lane4 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

H5 Step-2 small obligations for C3's B2 assembly (`Step2B2/Assembly.lean` 0c147c08; statements
used verbatim through the import), PROVED natively. SOURCE ONLY, UNCOMPILED. Native HELD.
Universe u, default options.

* `pairedSupportUnion`: Mathlib `IdealSheafData.support_mul` and `support_comap`.
* `sectionDichotomySupport`: C2 `pulledSectionHom_zeroLocus` (zero ideal of the pulled section is
  `s.zeroLocus.comap i`) with Mathlib `support_comap`; the zero map has zero ideal `⊥` (W07
  `Hom.zeroLocus_eq_bot_iff`), support everything; an ISOMORPHISM has zero ideal `⊤`
  (`zeroLocus_eq_top_of_isIso`: its local coefficient against free generators is a unit, W07
  `IsFreeGenerator.app_hom`, `exists_unit_smul_eq`), support empty.
* `infinitePointsOfNotFinite`: closed points of `C` give distinct rational points of `A` in
  `range i` (Mathlib `pointOfClosedPoint`); if these were finitely many, the Jacobson space `C`
  (`LocallyOfFiniteType.jacobsonSpace`) would have a closed finite set of closed points, hence be
  finite, hence `i ≫ A.X.hom` locally quasi-finite and (proper) finite.
Truth: all TRUE (these are the proofs).
-/
import ZInQKernel.Contrib.CloudR2NOS.Step2B2.Assembly
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.Step2Small.MumfordSmall

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped CategoryTheory.MonObj AlgebraicGeometry.Scheme.Modules

namespace ZInQ.Contrib.CloudR2NOS.ClosedSection.Step2Small

/-- **`PairedSupportUnion` proved.** -/
theorem pairedSupportUnion : ZInQ.Contrib.CloudR2NOS.Step2B2.PairedSupportUnion.{u} := by
  intro X D f g
  simp only [Scheme.IdealSheafData.support_mul, Scheme.IdealSheafData.support_comap,
    TopologicalSpace.Closeds.coe_sup, TopologicalSpace.Closeds.coe_preimage]
  rfl

/-- An isomorphism of invertible modules has zero ideal `⊤`. -/
theorem zeroLocus_eq_top_of_isIso {X : Scheme.{u}} {M N : X.Modules} [M.IsInvertible]
    [N.IsInvertible] (φ : M ⟶ N) [IsIso φ] : φ.zeroLocus = ⊤ := by
  have hunit : ∀ (V : X.affineOpens) (eM : Γ(M, V.1)), Scheme.Modules.IsFreeGenerator eM →
      ∀ eN : Γ(N, V.1), Scheme.Modules.IsFreeGenerator eN → ∀ b : Γ(X, V.1),
        φ.app V.1 eM = b • eN → IsUnit b := by
    intro V eM heM eN heN b hb
    have hφe : Scheme.Modules.IsFreeGenerator (φ.app V.1 eM) :=
      Scheme.Modules.IsFreeGenerator.app_hom (asIso φ) heM
    obtain ⟨w, hw⟩ := heN.exists_unit_smul_eq hφe
    have hbw : b = w.1 := heN.smul_left_injective (hb.symm.trans hw)
    rw [hbw]
    exact w.isUnit
  refine Scheme.IdealSheafData.ext (funext fun U => ?_)
  rw [Scheme.Modules.Hom.ideal_zeroLocus_eq, Scheme.IdealSheafData.ideal_top, Pi.top_apply]
  refine eq_top_iff.2 fun a _ => (Scheme.Modules.Hom.mem_zeroLocusIdeal_iff φ a).2 ?_
  intro V h eM heM eN heN b hb
  rw [Ideal.span_singleton_eq_top.2 (hunit V eM heM eN heN b hb)]
  exact Submodule.mem_top

/-- **`SectionDichotomySupport` proved.** -/
theorem sectionDichotomySupport :
    ZInQ.Contrib.CloudR2NOS.Step2B2.SectionDichotomySupport.{u} := by
  intro X C i M _ s
  have hzl := H5OriginalDVR.Lane2.NativeDivisorKernel.pulledSectionHom_zeroLocus i M s
  have hsupp : ((s.zeroLocus.comap i).support : Set C) =
      i ⁻¹' (s.zeroLocus.support : Set X) := by
    rw [Scheme.IdealSheafData.support_comap]
    rfl
  constructor
  · intro h0
    have hbot : (H5OriginalDVR.Lane2.NativeDivisorKernel.pulledSectionHom i M s).zeroLocus = ⊥ :=
      (Scheme.Modules.Hom.zeroLocus_eq_bot_iff _).2 h0
    rw [hzl] at hbot
    rintro _ ⟨c, rfl⟩
    have hmem : c ∈ ((s.zeroLocus.comap i).support : Set C) := by
      rw [hbot, Scheme.IdealSheafData.support_bot]
      trivial
    rw [hsupp] at hmem
    exact hmem
  · intro hiso
    haveI := hiso
    have htop := zeroLocus_eq_top_of_isIso
      (H5OriginalDVR.Lane2.NativeDivisorKernel.pulledSectionHom i M s)
    rw [hzl] at htop
    ext y
    refine ⟨fun ⟨⟨c, hc⟩, hy⟩ => ?_, fun h => by simp at h⟩
    have hmem : c ∈ ((s.zeroLocus.comap i).support : Set C) := by
      rw [hsupp]
      show i c ∈ _
      rw [hc]
      exact hy
    rw [htop, Scheme.IdealSheafData.support_top] at hmem
    simp at hmem

/-- **`InfinitePointsOfNotFinite` proved.** -/
theorem infinitePointsOfNotFinite :
    ZInQ.Contrib.CloudR2NOS.Step2B2.InfinitePointsOfNotFinite.{u} := by
  intro K _ _ A C i _ hprop hnf
  haveI := hprop
  by_contra hfin
  rw [Set.not_infinite] at hfin
  apply hnf
  haveI : JacobsonSpace C := LocallyOfFiniteType.jacobsonSpace (i ≫ A.X.hom)
  -- closed points of `C` give distinct rational points of `A` in `range i`
  let toPt : closedPoints C → (𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X) := fun c =>
    Over.homMk (pointOfClosedPoint (i ≫ A.X.hom) c.1 c.2 ≫ i)
      (by rw [Category.assoc]; exact pointOfClosedPoint_comp (i ≫ A.X.hom) c.1 c.2)
  have htoPt_apply : ∀ c : closedPoints C,
      (toPt c).left (IsLocalRing.closedPoint K) = i c.1 := fun c => by
    show i (pointOfClosedPoint (i ≫ A.X.hom) c.1 c.2 (IsLocalRing.closedPoint K)) = i c.1
    rw [pointOfClosedPoint_apply]
  haveI := hfin.to_subtype
  haveI : Finite (closedPoints C) := by
    refine Finite.of_injective (β := {x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X |
        x.left (IsLocalRing.closedPoint K) ∈ Set.range i})
      (fun c => ⟨toPt c, ⟨c.1, (htoPt_apply c).symm⟩⟩) ?_
    intro c c' h
    have h1 := congrArg (fun x : {x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X |
        x.left (IsLocalRing.closedPoint K) ∈ Set.range i} =>
      x.1.left (IsLocalRing.closedPoint K)) h
    simp only [htoPt_apply] at h1
    exact Subtype.ext (i.isClosedEmbedding.injective h1)
  -- a finite set of closed points is closed, and dense in the Jacobson space `C`
  have hcl : IsClosed (closedPoints C) := by
    have := (Set.toFinite (closedPoints C)).isClosed_biUnion
      (f := fun c : C => ({c} : Set C)) (fun c hc => hc)
    rwa [Set.biUnion_of_singleton] at this
  have huniv : closedPoints C = Set.univ := by
    have h := JacobsonSpace.closure_inter_closedPoints_eq_closure
      (isClosed_univ : IsClosed (Set.univ : Set C)).isLocallyClosed
    rwa [Set.univ_inter, hcl.closure_eq, closure_univ] at h
  haveI : Finite C := by
    have h : (Set.univ : Set C).Finite := huniv ▸ Set.toFinite (closedPoints C)
    exact Set.finite_univ_iff.1 h
  haveI : LocallyQuasiFinite (i ≫ A.X.hom) :=
    LocallyQuasiFinite.of_finite_preimage_singleton _ fun _ => Set.toFinite _
  exact IsFinite.of_isProper_of_locallyQuasiFinite (i ≫ A.X.hom)

end ZInQ.Contrib.CloudR2NOS.ClosedSection.Step2Small

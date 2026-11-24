import ZInQKernel.HDecomp.Objects
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-! # neron-c: the injective half of the Néron mapping property for abelian schemes

Task neron-c (2026-11-13). Leaf T3 = I2-NMP is the kernel's `PkgI2.NeronMappingAbelianScheme`:
for abelian schemes `𝒜, ℬ` over a DVR `O ⊆ K`, restriction to the generic fibre is a bijection
`Hom_O(𝒜, ℬ) → Hom_K(𝒜_K, ℬ_K)`. This file proves the injective half outright from Mathlib
(`𝒜 → Spec O` is flat, `Spec K → Spec O` is scheme-theoretically dominant, so its base change
`𝒜_K → 𝒜` is scheme-theoretically dominant; `ℬ` is separated), and reduces T3 to the surjective
half `NeronMappingAbelianSchemeSurj` (BLR §1.2 Prop. 8, the extension statement). -/

namespace ZInQ.Contrib.NeronC

open CategoryTheory AlgebraicGeometry Limits

universe u

/-- Two morphisms that agree over a separated `s : Y ⟶ Z` and after a scheme-theoretically
dominant `ι` are equal. (The version of Mathlib's `ext_of_isDominant_of_isSeparated` with
`IsSchemeTheoreticallyDominant ι` in place of `IsReduced X` and `IsDominant ι`.) -/
lemma ext_of_isSchemeTheoreticallyDominant_of_isSeparated {W X Y Z : Scheme.{u}} {f g : X ⟶ Y}
    (s : Y ⟶ Z) [IsSeparated s] (h : f ≫ s = g ≫ s)
    (ι : W ⟶ X) [IsSchemeTheoreticallyDominant ι] (hU : ι ≫ f = ι ≫ g) : f = g := by
  let X' : Over Z := Over.mk (f ≫ s)
  let Y' : Over Z := Over.mk s
  let U' : Over Z := Over.mk (ι ≫ f ≫ s)
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g
  let ι' : U' ⟶ X' := Over.homMk ι
  have : IsSeparated Y'.hom := ‹_›
  have hl : ι' ≫ f' = ι' ≫ g' := by ext1; exact hU
  have hker : (equalizer.ι f' g').left.ker = ⊥ := by
    rw [eq_bot_iff, ← ι.ker_eq_bot]
    refine le_trans (Scheme.Hom.le_ker_comp (equalizer.lift ι' hl).left _) (le_of_eq ?_)
    rw [← Over.comp_left, equalizer.lift_ι]; rfl
  have := (IsClosedImmersion.isIso_iff_ker_eq_bot (f := (equalizer.ι f' g').left)).mpr hker
  rw [← cancel_epi (equalizer.ι f' g').left]
  congrm $(equalizer.condition f' g').left

/-- Base change along a quasi-compact scheme-theoretically dominant `j : T ⟶ S` is injective on
morphisms from a flat `S`-scheme to a separated one. -/
lemma pullback_map_injective {S T : Scheme.{u}} (j : T ⟶ S) [IsSchemeTheoreticallyDominant j]
    [QuasiCompact j] (X Y : Over S) [Flat X.hom] [IsSeparated Y.hom] :
    Function.Injective (fun f : X ⟶ Y => (Over.pullback j).map f) := by
  intro f g hfg
  simp only at hfg
  have h1 : pullback.fst X.hom j ≫ f.left = pullback.fst X.hom j ≫ g.left := by
    have e1 : ((Over.pullback j).map f).left ≫ pullback.fst Y.hom j =
        pullback.fst X.hom j ≫ f.left := by simp
    have e2 : ((Over.pullback j).map g).left ≫ pullback.fst Y.hom j =
        pullback.fst X.hom j ≫ g.left := by simp
    rw [← e1, ← e2, hfg]
  ext1
  exact ext_of_isSchemeTheoreticallyDominant_of_isSeparated Y.hom (by simp)
    (pullback.fst X.hom j) h1

/-- `Spec` of an injective ring map out of a reduced ring is scheme-theoretically dominant. -/
lemma isSchemeTheoreticallyDominant_spec_map {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (hφ : Function.Injective φ) [IsReduced R] :
    IsSchemeTheoreticallyDominant (Spec.map φ) := by
  have : IsDominant (Spec.map φ) := by
    rw [isDominant_iff]
    change DenseRange (PrimeSpectrum.comap φ.hom)
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical]
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hφ]
    exact bot_le
  exact IsSchemeTheoreticallyDominant.of_isDominant _

/-- **The injective half of T3** (proved): restriction to the generic fibre is injective on
morphisms of abelian schemes over a DVR `O ⊆ K` (in fact for any flat source and separated
target over any subring `O` of `K`). -/
theorem neronMappingAbelianScheme_injective (K : Type u) [Field K] (O : ValuationSubring K)
    [IsDiscreteValuationRing O]
    (𝒜 ℬ : Grp (Over (Spec (.of O)))) [PkgI2.IsAbelianScheme 𝒜] [PkgI2.IsAbelianScheme ℬ] :
    Function.Injective (fun f : 𝒜.X ⟶ ℬ.X =>
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O K)))).map f) := by
  have : Smooth 𝒜.X.hom := PkgI2.IsAbelianScheme.smooth
  have : IsProper ℬ.X.hom := PkgI2.IsAbelianScheme.proper
  have : IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom (algebraMap O K))) :=
    isSchemeTheoreticallyDominant_spec_map _ (FaithfulSMul.algebraMap_injective O K)
  exact pullback_map_injective _ 𝒜.X ℬ.X

/-- **`NeronMappingAbelianSchemeSurj` (LEAF; published).** The surjective half of leaf T3
(I2-NMP): for abelian schemes `𝒜, ℬ` over the DVR `O ⊆ K`, every `K`-morphism `𝒜_K → ℬ_K` of the
generic fibres extends to an `O`-morphism `𝒜 → ℬ`. Source: Bosch–Lütkebohmert–Raynaud, *Néron
models* (1990), §1.2, Prop. 8 (an abelian scheme over a Dedekind scheme is the Néron model of its
generic fibre), applied with the smooth test scheme `𝒜` (BLR §1.2, Def. 1); the proof there is the
valuative criterion of properness at the codimension-one points of `𝒜` plus Weil's extension
theorem (BLR §4.4, Thm. 1). Locators UNVERIFIED (no network). Strictly weaker than T3. -/
def NeronMappingAbelianSchemeSurj : Prop :=
  ∀ (K : Type u) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (𝒜 ℬ : Grp (Over (Spec (.of O)))) [PkgI2.IsAbelianScheme 𝒜] [PkgI2.IsAbelianScheme ℬ],
    Function.Surjective (fun f : 𝒜.X ⟶ ℬ.X =>
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O K)))).map f)

/-- **T3 from its surjective half.** -/
theorem neronMappingAbelianScheme_of_surj (h : NeronMappingAbelianSchemeSurj.{u}) :
    PkgI2.NeronMappingAbelianScheme.{u} := fun K _ O _ 𝒜 ℬ _ _ =>
  ⟨neronMappingAbelianScheme_injective K O 𝒜 ℬ, h K O 𝒜 ℬ⟩

/-- Conversely T3 gives its surjective half (so the reduction loses nothing). -/
theorem neronMappingAbelianSchemeSurj_of_nmp (h : PkgI2.NeronMappingAbelianScheme.{u}) :
    NeronMappingAbelianSchemeSurj.{u} := fun K _ O _ 𝒜 ℬ _ _ => (h K O 𝒜 ℬ).2

end ZInQ.Contrib.NeronC

#print axioms ZInQ.Contrib.NeronC.ext_of_isSchemeTheoreticallyDominant_of_isSeparated
#print axioms ZInQ.Contrib.NeronC.pullback_map_injective
#print axioms ZInQ.Contrib.NeronC.neronMappingAbelianScheme_injective
#print axioms ZInQ.Contrib.NeronC.neronMappingAbelianScheme_of_surj

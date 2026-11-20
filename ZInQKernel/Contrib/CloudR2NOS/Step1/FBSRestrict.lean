/-
H5 lane3 Step 1: FBS restriction (Parent check (1)) and G6, reduced to FBS primitives.
2026-11-17. v2, interface v2: `FBSUnitFinite` and G6 take the internal `[IsProperIntegralGroup Y]`.
v1 69f9bc78 is in history/. New file. SOURCE-ONLY, UNCOMPILED. Universe u, any characteristic.

FBS is the prefixed FLT/Source `FiniteBySections` (lead binding 02:39Z):
`∃ n (𝔓 : M.ProjPresentation f n), IsFinite 𝔓.toProj`. The `ProjPresentation` fields are `σ`,
`toProj`, `toProj_π`, `frame` and `app_ratio_smul`.

PROVED here, modulo compile:
* `fbs_pullback`: FBS pulls back along a closed immersion. The pulled-back presentation has
  `toProj` equal to the composite `j ≫ 𝔓.toProj`, which is finite as finite ∘ closed immersion.
* `nontrivialTranslateFromR3` (G6), from R3 and the FBS primitives below.

Explicit UNPROVED primitives (each true, stated exactly):
* `ProjPresentationPullback`: a presentation pulls back along ANY morphism `j`, with
  `toProj' = j ≫ toProj`.
  - Sections: `σ' i := (pullbackUnit j N).app ⊤ (σ i)`.
  - Frames: pulled-back free generators are free generators, via W07 FreeGenerator(Pullback)
    `isFreeGenerator_iff_isIso` and `pullbackObjUnitIso`.
  - Ratios: smul-compatibility of section pullback, W07 SectionsBaseChange
    `presheaf_map_pullbackSection_smul`, with `(j ≫ toProj).app = j.app ∘ toProj.app`.
* `FBSIsoInvariant`: transport of a presentation along an isomorphism of modules.
* `FBSNonzeroSection`: on a nonempty scheme, a presentation has a nonzero section. Some `σ i` is a
  frame on a nonempty open.
* `FBSUnitFinite`: `O_Y` FBS on an abelian variety forces `Y` finite. `Γ(O_Y) = K` by (i) in
  PicZeroSections, so `toProj` is constant and finite.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step1.Interfaces

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.MonObj AlgebraicGeometry.Scheme.Modules

namespace ZInQ.Contrib.CloudR2NOS.Step1

/-- Primitive (UNPROVED): pullback of a `ProjPresentation` along any morphism, with composite
section map. -/
def ProjPresentationPullback : Prop :=
  ∀ {R : Type u} [CommRing R] {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (j : Y ⟶ X)
    (N : X.Modules) (n : ℕ)
    (𝔓 : ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.ProjPresentation N f n),
    ∃ 𝔓' : ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.ProjPresentation
        ((Scheme.Modules.pullback j).obj N) (j ≫ f) n,
      𝔓'.toProj = j ≫ 𝔓.toProj

/-- Primitive (UNPROVED): FBS is invariant under isomorphism of modules. -/
def FBSIsoInvariant : Prop :=
  ∀ {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) (L L' : X.Modules),
    Nonempty (L ≅ L') → FBS L f → FBS L' f

/-- Primitive (UNPROVED): an FBS module on a nonempty scheme has a nonzero global section. -/
def FBSNonzeroSection : Prop :=
  ∀ {K : Type u} [Field K] {X : Scheme.{u}} [Nonempty X] (f : X ⟶ Spec (CommRingCat.of K))
    (L : X.Modules), FBS L f → ¬ Subsingleton (L.H 0)

/-- Primitive (UNPROVED): the structure sheaf of an abelian variety is FBS only if the variety is
finite. -/
def FBSUnitFinite : Prop :=
  ∀ {K : Type u} [Field K] [IsAlgClosed K] (Y : Grp (Over (Spec (CommRingCat.of K))))
    [IsProperIntegralGroup Y], FBS (𝟙_ Y.X.left.Modules) Y.X.hom → IsFinite Y.X.hom

/-- Parent check (1): FBS restricts along a closed immersion. -/
theorem fbs_pullback (hPB : ProjPresentationPullback.{u}) {K : Type u} [Field K]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) (j : Y ⟶ X) [IsClosedImmersion j]
    (N : X.Modules) (h : FBS N f) : FBS ((Scheme.Modules.pullback j).obj N) (j ≫ f) := by
  obtain ⟨n, 𝔓, hfin⟩ := h
  obtain ⟨𝔓', h'⟩ := hPB f j N n 𝔓
  refine ⟨n, 𝔓', ?_⟩
  rw [h']
  infer_instance

/-- G6, PROVED from R3 and the FBS primitives. -/
theorem nontrivialTranslateFromR3 (hPB : ProjPresentationPullback.{u})
    (hIso : FBSIsoInvariant.{u}) (hUF : FBSUnitFinite.{u}) (hNZ : FBSNonzeroSection.{u}) :
    NontrivialTranslateFromR3.{u} := by
  intro hR3 K _ _ A Y _ _ j _ hjc hfin N _ hN
  by_contra hall
  push_neg at hall
  haveI := hjc
  have hFBS : FBS ((Scheme.Modules.pullback j.left).obj N) Y.X.hom := by
    have h := fbs_pullback hPB A.X.hom j.left N hN
    rwa [Over.w j] at h
  by_cases htriv : Nonempty ((Scheme.Modules.pullback j.left).obj N ≅ 𝟙_ Y.X.left.Modules)
  · exact hfin (hUF Y (hIso Y.X.hom _ _ htriv hFBS))
  · haveI : Nonempty Y.X.left :=
      ⟨(η[Y.X] : Pt K ⟶ Y.X).left.base
        (Nonempty.some (inferInstance : Nonempty (Spec (CommRingCat.of K))))⟩
    exact hNZ Y.X.hom _ hFBS (hR3 Y _ hall htriv)

end ZInQ.Contrib.CloudR2NOS.Step1

/-
H5 lane3 Step 2, B3 `NativeFBSFieldDescent` (Step2DelegatedInterfaces 4d5c8dce): PROVED from
C4's native presentation and quasi-finite machinery (single producers, exact names) plus FOUR
small native obligations. 2026-11-17. New file. SOURCE-ONLY, UNCOMPILED. Universe u.

Producers (C4, lane4-suppliedmodel-converse/patches/ZInQKernel/Contrib/CloudR2NOS/ClosedSection/,
each by exact SHA):
* `PresentationBasics.presentationOfIso` (G7; a03eb73c…): transport along `N̄^b ≅ p^*(N^b)`.
* `pullbackTensorPowIso` (NativePower 8ebb826e…): `p^*(N^b) ≅ (p^*N)^b`.
* `framesNearOfPullback` (G4; FramesDescend b987e0da…): generation descends along `p`.
* `presentationOfFramesNear` (G5; ProjOfFrames 83a207f8…): a presentation over `k` with the chosen
  sections.
* `FLTA…ProjPresentation.exists_baseChange_of_isPullback` (FLTA/BaseChange 9e92a6ee…): its base
  change to `K` is a pullback square of section maps.
* `FLTA…ProjPresentation.locallyQuasiFinite_of_forall_exists_eq_sum_smul` (FLTA/LQFSumSmul
  13ea18bf…): the base-changed map is LQF because the given finite presentation's sections are
  `K`-combinations of the pulled basis.
* `FLTA…Scheme.Hom.quasiFiniteAt_of_isPullback_of_locallyQuasiFinite` (FLTA/QFAtPullback c0f93f15…):
  quasi-finiteness descends to `k`.
* Mathlib `IsFinite.of_isProper_of_locallyQuasiFinite` and
  `Scheme.Hom.quasiFiniteLocus_eq_top_iff`: proper plus LQF gives finite.

Small obligations (TRUE):
* `PulledSectionsSpan`: `H⁰(A, L)` is finite over `k` (`A` proper). Its pulled-back basis spans
  `H⁰(Ā, p^*L)` over `K` (W07 `H.baseChange`, flat base change of `H⁰`). If `H⁰ = 0`, take `s = 0`.
* `FramesNearOfSum`: if a `Γ`-combination of sections of an invertible module frames near `x`,
  so does one of its summands (a sum of non-units in a local ring is a non-unit).
* `PresentationFramesEverywhere`: every point lies in some `D₊(X_i)`, so some `σ_i` frames near it
  (the presentation's frame field; C4 `PresChart.exists_mem_basicOpen_X`).
* `ProjSpaceMapSurjective`: `ℙ^m_K → ℙ^m_k` is a base change of the surjective `Spec K → Spec k`.
-/
import Step2DelegatedInterfaces
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.PresentationBasics
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.NativePower
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.FramesDescend
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.ProjOfFrames
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.FLTA.BaseChange
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.FLTA.LQFSumSmul
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.FLTA.QFAtPullback

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped AlgebraicGeometry.Scheme.Modules

namespace ZInQ.Contrib.CloudR2NOS.Step2B3

local notation "Pres" =>
  ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.ProjPresentation

/-- (TRUE) The pulled-back finite family of sections spans `H⁰` after a field extension. -/
def PulledSectionsSpan : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] (L : X.Modules) [L.IsInvertible],
    ∃ (m : ℕ) (s : Fin (m + 1) → Γ(L, ⊤)), ∀ τ : Γ((Scheme.Modules.pullback
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj L, ⊤),
      ∃ c : Fin (m + 1) → K, τ = ∑ j, ((pullback.snd f (Spec.map (CommRingCat.ofHom
          (algebraMap k K)))).appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv (c j))) •
        ZInQ.Contrib.CloudR2NOS.ClosedSection.pullbackSection
          (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) (s j)

/-- (TRUE) A framing combination has a framing summand. -/
def FramesNearOfSum : Prop :=
  ∀ {X : Scheme.{u}} (M : X.Modules) [M.IsInvertible] {m : ℕ} (a : Fin (m + 1) → Γ(X, ⊤))
    (t : Fin (m + 1) → Γ(M, ⊤)) (x : X),
    ZInQ.Contrib.CloudR2NOS.ClosedSection.FramesNear M (∑ j, a j • t j) x →
      ∃ j, ZInQ.Contrib.CloudR2NOS.ClosedSection.FramesNear M (t j) x

/-- (TRUE) Some section of a presentation frames near every point. -/
def PresentationFramesEverywhere : Prop :=
  ∀ {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
    {M : X.Modules} {N : ℕ} (𝔓 : Pres M f N) (x : X),
    ∃ i, ZInQ.Contrib.CloudR2NOS.ClosedSection.FramesNear M (𝔓.σ i) x

/-- (TRUE) The projective-space base-change map of a field extension is surjective. -/
def ProjSpaceMapSurjective : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] (m : ℕ),
    Function.Surjective
      (ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.map k K m).base

/-- B3, PROVED from C4's producers and the four obligations. -/
theorem nativeFBSFieldDescent (hSpan : PulledSectionsSpan.{u}) (hSum : FramesNearOfSum.{u})
    (hPF : PresentationFramesEverywhere.{u}) (hSurj : ProjSpaceMapSurjective.{u}) :
    H5OriginalDVR.Lane2.Step2DelegatedInterfaces.NativeFBSFieldDescent.{u} := by
  intro k K _ _ _ A _ N _ b hb
  intro hFBS
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let p := pullback.fst A.X.hom g
  let f' := pullback.snd A.X.hom g
  haveI : IsProper A.X.hom := PkgI2.IsAbelianVariety.proper
  let L := Scheme.Modules.tensorPow N b
  obtain ⟨d, 𝔓K, hfin⟩ := hFBS
  -- transport the geometric presentation to `p^*(N^b)`
  obtain ⟨𝔓M, htoProj, -⟩ := ZInQ.Contrib.CloudR2NOS.ClosedSection.PresentationBasics.presentationOfIso
    𝔓K (ZInQ.Contrib.CloudR2NOS.ClosedSection.pullbackTensorPowIso p N b).symm
  -- an original-`k` family of sections whose pullbacks span
  obtain ⟨m, s, hs⟩ := hSpan A.X.hom L
  -- the family generates `L` on `A`
  have hframes : ∀ x : A.X.left, ∃ j, ZInQ.Contrib.CloudR2NOS.ClosedSection.FramesNear L (s j) x := by
    intro x
    obtain ⟨x', hx'⟩ : ∃ x', p.base x' = x := (inferInstance : Surjective p).surj x
    obtain ⟨i, hi⟩ := hPF 𝔓M x'
    obtain ⟨c, hc⟩ := hs (𝔓M.σ i)
    rw [hc] at hi
    obtain ⟨j, hj⟩ := hSum _ _ _ x' hi
    exact ⟨j, hx' ▸ ZInQ.Contrib.CloudR2NOS.ClosedSection.framesNearOfPullback p L (s j) x' hj⟩
  -- the original-`k` presentation with those sections
  obtain ⟨𝔓k, hσk⟩ := ZInQ.Contrib.CloudR2NOS.ClosedSection.presentationOfFramesNear A.X.hom L m s hframes
  -- its base change to `K`
  obtain ⟨𝔓', hσ', -, hpb⟩ :=
    ZInQ.Contrib.CloudR2NOS.ClosedSection.FLTA.AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_baseChange_of_isPullback
      (IsPullback.of_hasPullback A.X.hom g) 𝔓k
  -- the base-changed map is LQF, because the given finite map's sections are combinations
  haveI : LocallyQuasiFinite 𝔓M.toProj := by
    rw [htoProj]
    infer_instance
  haveI : LocallyQuasiFinite 𝔓'.toProj :=
    ZInQ.Contrib.CloudR2NOS.ClosedSection.FLTA.AlgebraicGeometry.Scheme.Modules.ProjPresentation.locallyQuasiFinite_of_forall_exists_eq_sum_smul
      𝔓M 𝔓' (fun i => by
        obtain ⟨c, hc⟩ := hs (𝔓M.σ i)
        refine ⟨c, hc.trans ?_⟩
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hσ' j, hσk]
        rfl)
  -- descent of quasi-finiteness to `k`, then properness gives finiteness
  haveI : IsProper (𝔓k.toProj ≫ ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.π k m) := by
    rw [𝔓k.toProj_π]
    infer_instance
  haveI : LocallyOfFiniteType 𝔓k.toProj :=
    LocallyOfFiniteType.of_comp 𝔓k.toProj
      (ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.π k m)
  haveI : LocallyQuasiFinite 𝔓k.toProj := by
    rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff]
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨y', hy'⟩ := hSurj (k := k) (K := K) m (𝔓k.toProj.base x)
    exact ZInQ.Contrib.CloudR2NOS.ClosedSection.FLTA.AlgebraicGeometry.Scheme.Hom.quasiFiniteAt_of_isPullback_of_locallyQuasiFinite
      hpb y' x hy'.symm
  haveI : IsProper 𝔓k.toProj :=
    IsProper.of_comp 𝔓k.toProj
      (ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.π k m)
  exact ⟨m, 𝔓k, IsFinite.of_isProper_of_locallyQuasiFinite (f := 𝔓k.toProj)⟩

end ZInQ.Contrib.CloudR2NOS.Step2B3

/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
import ZInQKernel.HDecomp.QM.Leaves
import Mathlib.AlgebraicGeometry.RelativeGluing
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# W13 dictionary D7, step 4: gluing a family of QM data over the affine opens of a scheme

A `LocalFamily M` is, for every affine open `U` of `M`:
* a scheme `X U → U`;
* transition maps `τ : X U ⟶ X V` for `U ≤ V`, strictly functorial, whose squares over
  `U ⟶ V` are pullbacks;
* compatible endomorphisms `iota a` and sections `sec a`;
* `X U → U` proper and smooth of relative dimension `2`.

Mathlib's relative gluing (`Scheme.Cover.RelativeGluingData` over `M.directedAffineCover`, Stacks
01LH) glues the `X U` to `𝒜 → M` with `X U ≅ 𝒜 ×_M U`. The endomorphisms and sections glue by
`glueMorphismsOfLocallyDirected`, and properness and smoothness of relative dimension `2` are local
on the target. The result is a kernel `LeafQM.AV.QMFamily M` with its comparison lemmas. Nothing
here is assumed beyond the fields of the structure.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB2Shimura.Dictionary.D7

open CategoryTheory AlgebraicGeometry Limits

universe u

variable (M : Scheme.{0})

/-- Local QM data over the affine opens of `M` (see the module docstring). -/
structure LocalFamily where
  X : M.affineOpens → Scheme.{0}
  p : ∀ U : M.affineOpens, X U ⟶ (U.1 : Scheme.{0})
  τ : ∀ {U V : M.affineOpens}, U ≤ V → (X U ⟶ X V)
  τ_id : ∀ U, τ (le_refl U) = 𝟙 (X U)
  τ_comp : ∀ {U V W : M.affineOpens} (h₁ : U ≤ V) (h₂ : V ≤ W), τ h₁ ≫ τ h₂ = τ (h₁.trans h₂)
  pb : ∀ {U V : M.affineOpens} (h : U ≤ V), IsPullback (τ h) (p U) (p V) (M.homOfLE h)
  iota : LeafQM.O → ∀ U, X U ⟶ X U
  iota_p : ∀ a U, iota a U ≫ p U = p U
  iota_τ : ∀ a {U V : M.affineOpens} (h : U ≤ V), τ h ≫ iota a V = iota a U ≫ τ h
  sec : LeafQM.O → ∀ U : M.affineOpens, (U.1 : Scheme.{0}) ⟶ X U
  sec_p : ∀ a U, sec a U ≫ p U = 𝟙 _
  sec_τ : ∀ a {U V : M.affineOpens} (h : U ≤ V), sec a U ≫ τ h = M.homOfLE h ≫ sec a V
  proper : ∀ U, IsProper (p U)
  smooth : ∀ U, SmoothOfRelativeDimension 2 (p U)

namespace LocalFamily

variable {M} (F : LocalFamily M)

/-- The cover of `M` by all affine opens (Mathlib, locally directed). -/
abbrev 𝒰 : M.OpenCover := M.directedAffineCover

/-- The diagram of the `X U`. -/
def functor : (𝒰 (M := M)).I₀ ⥤ Scheme.{0} where
  obj U := F.X U
  map h := F.τ (leOfHom h)
  map_id U := F.τ_id U
  map_comp h₁ h₂ := (F.τ_comp (leOfHom h₁) (leOfHom h₂)).symm

lemma trans_eq {U V : (𝒰 (M := M)).I₀} (h : U ⟶ V) :
    (𝒰 (M := M)).trans h = M.homOfLE (leOfHom h) := by
  rw [show h = homOfLE (leOfHom h) from Subsingleton.elim _ _]
  rfl

/-- The structure maps `X U ⟶ U` as a natural transformation. -/
def natTrans : F.functor ⟶ (𝒰 (M := M)).functorOfLocallyDirected where
  app U := F.p U
  naturality U V h := by
    change F.τ (leOfHom h) ≫ F.p V = F.p U ≫ (𝒰 (M := M)).trans h
    rw [trans_eq]
    exact (F.pb (leOfHom h)).w

lemma equifibered : F.natTrans.Equifibered := by
  intro U V h
  change IsPullback (F.τ (leOfHom h)) (F.p U) (F.p V) ((𝒰 (M := M)).trans h)
  rw [trans_eq]
  exact F.pb (leOfHom h)

/-- The relative gluing datum. -/
def gluingData : (𝒰 (M := M)).RelativeGluingData where
  functor := F.functor
  natTrans := F.natTrans
  equifibered := F.equifibered

/-- The glued scheme. -/
abbrev glued : Scheme.{0} := F.gluingData.glued

/-- The structure map of the glued scheme. -/
abbrev toBase : F.glued ⟶ M := F.gluingData.toBase

/-- The inclusion of `X U` into the glued scheme. -/
abbrev ι (U : M.affineOpens) : F.X U ⟶ F.glued := colimit.ι F.gluingData.functor U

lemma ι_toBase (U : M.affineOpens) : F.ι U ≫ F.toBase = F.p U ≫ U.1.ι :=
  F.gluingData.ι_toBase U

/-- `X U` is the restriction of the glued scheme to `U`. -/
lemma isPullback_ι (U : M.affineOpens) : IsPullback (F.p U) (F.ι U) U.1.ι F.toBase :=
  F.gluingData.isPullback_natTrans_ι_toBase U

lemma τ_ι {U V : M.affineOpens} (h : U ≤ V) : F.τ h ≫ F.ι V = F.ι U :=
  colimit.w F.gluingData.functor (homOfLE h)

lemma iota_compat (a : LeafQM.O) {U V : M.affineOpens} (h : U ≤ V) :
    F.τ h ≫ F.iota a V ≫ F.ι V = F.iota a U ≫ F.ι U := by
  rw [← Category.assoc, F.iota_τ, Category.assoc, F.τ_ι]

lemma sec_compat (a : LeafQM.O) {U V : M.affineOpens} (h : U ≤ V) :
    M.homOfLE h ≫ F.sec a V ≫ F.ι V = F.sec a U ≫ F.ι U := by
  rw [← Category.assoc, ← F.sec_τ, Category.assoc, F.τ_ι]

/-- The glued endomorphism `iota a`. -/
def iotaG (a : LeafQM.O) : F.glued ⟶ F.glued :=
  F.gluingData.cover.glueMorphismsOfLocallyDirected (fun U => F.iota a U ≫ F.ι U)
    (fun {U V} h => F.iota_compat a (leOfHom h))

lemma ι_iotaG (a : LeafQM.O) (U : M.affineOpens) : F.ι U ≫ F.iotaG a = F.iota a U ≫ F.ι U :=
  Scheme.OpenCover.map_glueMorphismsOfLocallyDirected F.gluingData.cover _
    (fun {_ _} h => F.iota_compat a (leOfHom h)) U

lemma iotaG_toBase (a : LeafQM.O) : F.iotaG a ≫ F.toBase = F.toBase := by
  refine F.gluingData.cover.hom_ext _ _ fun U => ?_
  have h1 := F.ι_iotaG a U
  have h2 := F.ι_toBase U
  have h3 := F.iota_p a U
  change F.ι U ≫ F.iotaG a ≫ F.toBase = F.ι U ≫ F.toBase
  rw [← Category.assoc, h1, Category.assoc, h2, ← Category.assoc, h3]

/-- The glued section `eta a`. -/
def etaG (a : LeafQM.O) : M ⟶ F.glued :=
  (𝒰 (M := M)).glueMorphismsOfLocallyDirected (fun U => F.sec a U ≫ F.ι U)
    (fun {U V} h => by
      rw [trans_eq]
      exact F.sec_compat a (leOfHom h))

lemma ι_etaG (a : LeafQM.O) (U : M.affineOpens) : U.1.ι ≫ F.etaG a = F.sec a U ≫ F.ι U :=
  Scheme.OpenCover.map_glueMorphismsOfLocallyDirected (𝒰 (M := M)) _
    (fun {_ _} h => by rw [trans_eq]; exact F.sec_compat a (leOfHom h)) U

lemma etaG_toBase (a : LeafQM.O) : F.etaG a ≫ F.toBase = 𝟙 M := by
  refine (𝒰 (M := M)).hom_ext _ _ fun U => ?_
  have h1 := F.ι_etaG a U
  have h2 := F.ι_toBase U
  have h3 := F.sec_p a U
  change U.1.ι ≫ F.etaG a ≫ F.toBase = U.1.ι ≫ 𝟙 M
  rw [← Category.assoc, h1, Category.assoc, h2, ← Category.assoc, h3,
    Category.id_comp, Category.comp_id]

/-- A property local on the target that holds for every `X U → U` holds for the glued family. -/
lemma of_local (P : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget P]
    (H : ∀ U, P (F.p U)) : P F.toBase := by
  refine IsZariskiLocalAtTarget.of_openCover (𝒰 (M := M)) fun U => ?_
  have hpb := (F.isPullback_ι U).flip
  change P (pullback.snd F.toBase U.1.ι)
  exact (P.arrow_mk_iso_iff (Arrow.isoMk hpb.isoPullback (Iso.refl _) (by simp))).mp (H U)

instance : IsZariskiLocalAtTarget (@SmoothOfRelativeDimension 2) :=
  HasRingHomProperty.instIsZariskiLocalAtTarget _

/-- **The glued kernel `QMFamily`.** -/
def toQMFamily : LeafQM.AV.QMFamily M where
  F := Over.mk F.toBase
  proper := F.of_local @IsProper fun U => F.proper U
  smooth := F.of_local (@SmoothOfRelativeDimension 2) fun U => F.smooth U
  iota := F.iotaG
  iota_over := F.iotaG_toBase
  eta := F.etaG
  eta_sec := F.etaG_toBase

end LocalFamily

end ZInQ.Contrib.CloudB2Shimura.Dictionary.D7

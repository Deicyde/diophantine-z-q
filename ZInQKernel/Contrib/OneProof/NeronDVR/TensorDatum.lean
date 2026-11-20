import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.TensorCofaces
import ZInQKernel.Contrib.OneProof.NeronDVR.SectionDescent
import ZInQKernel.Contrib.OneProof.NeronDVR.SectionSpanCover
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Descent.Affine

/-!
# Tensor coordinates for the overlaps of a scheme descent datum

The literal double and triple overlaps have structural maps to the spectra
of the corresponding tensor products. This identifies the cocycle on
these overlaps with faithfully flat descent of the global sections.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped MonoidalCategory TensorProduct

universe u
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace NeronDVR.TensorDescent

open ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective.TensorCofaces

variable (R R' : Type u) [CommRing R] [CommRing R'] [Algebra R R']

local notation "p" => baseMap R R'
local notation "ℓ" => left R R'
local notation "r" => right R R'
local notation "F₁₂" => face12 R R'
local notation "F₁₃" => face13 R R'
local notation "F₂₃" => face23 R R'

/-- The triple tensor spectrum is the pullback of the first factor and the
last two factors over the base. -/
theorem isPullback_triple : IsPullback (F₁₂ ≫ ℓ) F₂₃ p (r ≫ p) := by
  let T := R' ⊗[R] R'
  have hbase : Spec.map (CommRingCat.ofHom (algebraMap R T)) = r ≫ p := by
    unfold right baseMap
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    apply congrArg Spec.map
    ext x
    exact ((Algebra.TensorProduct.includeRight : R' →ₐ[R] T).commutes x).symm
  have hleft : (F₁₂ ≫ ℓ) =
      Spec.map (CommRingCat.ofHom (algebraMap R' (R' ⊗[R] T))) := by
    unfold face12 left
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  rw [← hbase, hleft]
  refine IsPullback.of_iso_pullback ⟨?_⟩ (pullbackSpecIso R R' T).symm
    (pullbackSpecIso_inv_fst' R R' T) (pullbackSpecIso_inv_snd R R' T)
  rw [← hleft, hbase, Category.assoc, left_base R R', ← Category.assoc,
    face12_right R R', Category.assoc, left_base R R']

variable (X : Over (Cover R'))

abbrev overlap : Scheme.{u} := Limits.pullback (X.hom ≫ p) p

local notation "Y" => overlap R R' X

abbrev first : Y ⟶ X.left := pullback.fst (X.hom ≫ p) p
abbrev secondBase : Y ⟶ Cover R' := pullback.snd (X.hom ≫ p) p

local notation "a" => first R R' X
local notation "q" => secondBase R R' X

theorem overlap_base_eq : (a ≫ X.hom) ≫ p = q ≫ p := by simp [pullback.condition]

/-- The structural map of the actual overlap to the square tensor spectrum. -/
def structure2 : Y ⟶ Square R R' :=
  (isPullback_square R R').lift (a ≫ X.hom) q (overlap_base_eq R R' X)

local notation "f₂" => structure2 R R' X

@[reassoc (attr := simp)]
theorem structure2_left : f₂ ≫ ℓ = a ≫ X.hom := (isPullback_square R R').lift_fst _ _ _
@[reassoc (attr := simp)]
theorem structure2_right : f₂ ≫ r = q := (isPullback_square R R').lift_snd _ _ _

theorem cartesian1 : IsPullback a f₂ X.hom ℓ := by
  have h : IsPullback a q (X.hom ≫ p) p := IsPullback.of_hasPullback _ _
  rw [← structure2_right R R' X] at h
  exact h.of_bot (structure2_left R R' X).symm (isPullback_square R R')

variable (d : CategoryTheory.Over.DescentDatum (baseMap R R') X)

private def reverse : Y ⟶ Y :=
  pullback.lift d.toHom (a ≫ X.hom) (by
    rw [← Category.assoc, d.toHom_comp_hom, overlap_base_eq R R' X])

private theorem reverse_fst : reverse R R' X d ≫ a = d.toHom :=
  pullback.lift_fst _ _ _

private theorem reverse_snd : reverse R R' X d ≫ q = a ≫ X.hom :=
  pullback.lift_snd _ _ _

private theorem reverse_toHom : reverse R R' X d ≫ d.toHom = a := by
  let h := overlap_base_eq R R' X
  let pt : Over.mk (a ≫ X.hom) ⟶ X := Over.DescentDatum.universalPoint
  let moved := d.transport _ _ h pt
  have hc := d.transport_transport (a ≫ X.hom) q (a ≫ X.hom) h h.symm pt
  rw [d.transport_self] at hc
  exact (d.transport_left_eq_lift_toHom _ _ h.symm moved).symm.trans
    (congrArg CommaMorphism.left hc)

private theorem reverse_involution : reverse R R' X d ≫ reverse R R' X d = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, reverse_fst, reverse_toHom, Category.id_comp]
  · rw [Category.assoc, reverse_snd, ← Category.assoc, reverse_fst, d.toHom_comp_hom]
    exact (Category.id_comp _).symm

theorem cartesian2 : IsPullback d.toHom f₂ X.hom r := by
  let e : Y ≅ Y := ⟨reverse R R' X d, reverse R R' X d,
    reverse_involution R R' X d, reverse_involution R R' X d⟩
  have h : IsPullback d.toHom (a ≫ X.hom) (X.hom ≫ p) p :=
    IsPullback.of_iso_pullback ⟨by rw [← Category.assoc, d.toHom_comp_hom,
      overlap_base_eq R R' X]⟩ e (reverse_fst R R' X d) (reverse_snd R R' X d)
  rw [← structure2_left R R' X] at h
  exact h.of_bot (d.toHom_comp_hom.trans (structure2_right R R' X).symm)
    (isPullback_square R R').flip

abbrev tripleOverlap : Scheme.{u} := Limits.pullback (q ≫ p) p

local notation "Z" => tripleOverlap R R' X

abbrev chart12 : Z ⟶ Y := pullback.fst (q ≫ p) p
abbrev chart13 : Z ⟶ Y := coactionForget p X.hom
abbrev chart23 : Z ⟶ Y := coactionMap p X.hom d.toHom d.toHom_comp_hom

local notation "b₁₂" => chart12 R R' X
local notation "b₁₃" => chart13 R R' X
local notation "b₂₃" => chart23 R R' X d
local notation "q₃" => pullback.snd (q ≫ p) p

@[reassoc (attr := simp)]
theorem chart13_first : b₁₃ ≫ a = b₁₂ ≫ a := by simp [chart13]
@[reassoc (attr := simp)]
theorem chart13_secondBase : b₁₃ ≫ q = q₃ := by simp [chart13]
@[reassoc (attr := simp)]
theorem chart23_first : b₂₃ ≫ a = b₁₂ ≫ d.toHom := by simp [chart23]
@[reassoc (attr := simp)]
theorem chart23_secondBase : b₂₃ ≫ q = q₃ := by simp [chart23]

theorem nerve_eq1 : b₁₂ ≫ a = b₁₃ ≫ a := (chart13_first R R' X).symm
theorem nerve_eq2 : b₁₂ ≫ d.toHom = b₂₃ ≫ a := (chart23_first R R' X d).symm
theorem nerve_eq3 : b₁₃ ≫ d.toHom = b₂₃ ≫ d.toHom := d.coactionMap_toHom.symm

private def lastPair : Z ⟶ Square R R' :=
  (isPullback_square R R').lift (b₁₂ ≫ q) q₃ (by simp [pullback.condition])

@[reassoc (attr := simp)]
private theorem lastPair_left : lastPair R R' X ≫ ℓ = b₁₂ ≫ q :=
  (isPullback_square R R').lift_fst _ _ _
@[reassoc (attr := simp)]
private theorem lastPair_right : lastPair R R' X ≫ r = q₃ :=
  (isPullback_square R R').lift_snd _ _ _

/-- The structural map of the actual triple overlap to the triple tensor
spectrum. -/
def structure3 : Z ⟶ Triple R R' :=
  (isPullback_triple R R').lift (b₁₂ ≫ a ≫ X.hom) (lastPair R R' X)
    (by rw [Category.assoc, overlap_base_eq R R' X, ← Category.assoc,
      ← lastPair_left R R' X, Category.assoc, left_base R R', ← Category.assoc])

local notation "f₃" => structure3 R R' X

@[reassoc (attr := simp)]
theorem structure3_first : f₃ ≫ (F₁₂ ≫ ℓ) = b₁₂ ≫ a ≫ X.hom :=
  (isPullback_triple R R').lift_fst _ _ _
@[reassoc (attr := simp)]
private theorem structure3_lastPair : f₃ ≫ F₂₃ = lastPair R R' X :=
  (isPullback_triple R R').lift_snd _ _ _

theorem chart12_base : b₁₂ ≫ f₂ = f₃ ≫ F₁₂ := by
  apply (isPullback_square R R').hom_ext
  · simp only [Category.assoc, structure2_left, structure3_first]
  · simp only [Category.assoc, structure2_right, face12_right, ← Category.assoc f₃ F₂₃,
      structure3_lastPair, lastPair_left]

theorem chart13_base : b₁₃ ≫ f₂ = f₃ ≫ F₁₃ := by
  apply (isPullback_square R R').hom_ext
  · simp only [Category.assoc, structure2_left, chart13_first_assoc, ← face12_left,
      structure3_first]
  · simp only [Category.assoc, structure2_right, chart13_secondBase, face13_right,
      ← Category.assoc f₃ F₂₃, structure3_lastPair, lastPair_right]

theorem chart23_base : b₂₃ ≫ f₂ = f₃ ≫ F₂₃ := by
  apply (isPullback_square R R').hom_ext
  · rw [Category.assoc, structure2_left, chart23_first_assoc, d.toHom_comp_hom,
      structure3_lastPair, lastPair_left]
  · rw [Category.assoc, structure2_right, chart23_secondBase, structure3_lastPair, lastPair_right]

private theorem cartesian3_first :
    IsPullback (b₁₂ ≫ a) f₃ X.hom (F₁₂ ≫ ℓ) := by
  have hz : IsPullback b₁₂ q₃ (q ≫ p) p := IsPullback.of_hasPullback _ _
  rw [← lastPair_right R R' X] at hz
  have hmid : IsPullback b₁₂ (lastPair R R' X) q ℓ :=
    hz.of_bot (lastPair_left R R' X).symm (isPullback_square R R')
  have hlarge := hmid.paste_horiz (IsPullback.of_hasPullback (X.hom ≫ p) p)
  rw [left_base R R', ← structure3_lastPair R R' X] at hlarge
  exact hlarge.of_bot (by simp only [Category.assoc, structure3_first])
    (isPullback_triple R R')

theorem cartesian12 : IsPullback b₁₂ f₃ f₂ F₁₂ :=
  (cartesian3_first R R' X).of_right (chart12_base R R' X) (cartesian1 R R' X)

theorem cartesian13 : IsPullback b₁₃ f₃ f₂ F₁₃ := by
  have h : IsPullback (b₁₃ ≫ a) f₃ X.hom (F₁₃ ≫ ℓ) := by
    rw [chart13_first, ← face12_left]
    exact cartesian3_first R R' X
  exact h.of_right (chart13_base R R' X) (cartesian1 R R' X)

theorem cartesian23 : IsPullback b₂₃ f₃ f₂ F₂₃ := by
  have h := (cartesian12 R R' X).paste_horiz (cartesian2 R R' X d)
  rw [face12_right, nerve_eq2 R R' X d] at h
  exact h.of_right (chart23_base R R' X d) (cartesian1 R R' X)

variable (L : X.left.Modules)

/-- The line descent cocycle on the actual triple overlap of the scheme
datum, with the canonical pullback comparisons. -/
def LineCocycle (ψ : (Scheme.Modules.pullback a).obj L ≅ (Scheme.Modules.pullback d.toHom).obj L) : Prop :=
  ((Scheme.Modules.pullbackCongr (nerve_eq1 R R' X)).app L).symm ≪≫
    ((Scheme.Modules.pullbackComp b₁₂ a).app L).symm ≪≫
    (Scheme.Modules.pullback b₁₂).mapIso ψ ≪≫
    ((Scheme.Modules.pullbackComp b₁₂ d.toHom).app L) ≪≫
    ((Scheme.Modules.pullbackCongr (nerve_eq2 R R' X d)).app L) ≪≫
    ((Scheme.Modules.pullbackComp b₂₃ a).app L).symm ≪≫
    (Scheme.Modules.pullback b₂₃).mapIso ψ ≪≫
    ((Scheme.Modules.pullbackComp b₂₃ d.toHom).app L) ≪≫
    ((Scheme.Modules.pullbackCongr (nerve_eq3 R R' X d)).app L).symm =
  ((Scheme.Modules.pullbackComp b₁₃ a).app L).symm ≪≫
    (Scheme.Modules.pullback b₁₃).mapIso ψ ≪≫
    ((Scheme.Modules.pullbackComp b₁₃ d.toHom).app L)

open ZInQ.Contrib.CloudR2NOS.Descent

/-- For a quasi-coherent module on a quasi-compact, quasi-separated
scheme over an affine faithfully flat cover, compatible sections span
all global sections. -/
theorem span_compatible_sections [Module.FaithfullyFlat R R']
    [QuasiCompact X.hom] [QuasiSeparated X.hom]
    [SheafOfModules.IsQuasicoherent (R := X.left.ringCatSheaf) L]
    (ψ : (Scheme.Modules.pullback a).obj L ≅ (Scheme.Modules.pullback d.toHom).obj L) (hψ : LineCocycle R R' X d L ψ) :
    letI := moduleTop X.hom L
    ∀ s : Γ(L, ⊤), s ∈ Submodule.span R' {s |
      ψ.hom.app ⊤ (Scheme.Modules.pullbackSection a (U := ⊤) s) =
        Scheme.Modules.pullbackSection d.toHom (U := ⊤) s} := by
  exact SectionDescent.span_descended_of_isQuasicoherent R' X.left X.hom L Y f₂ a d.toHom
    (cartesian1 R R' X) (cartesian2 R R' X d) Z f₃ b₁₂ b₁₃ b₂₃
    (cartesian12 R R' X) (cartesian13 R R' X) (cartesian23 R R' X d)
    (nerve_eq1 R R' X) (nerve_eq2 R R' X d) (nerve_eq3 R R' X d) ψ hψ

/-- An invertible module with a compatible descent cocycle and an affine
nonvanishing cover makes the underlying scheme descent datum effective. -/
theorem isEffective_of_lineCocycle [Module.FaithfullyFlat R R']
    [QuasiCompact X.hom] [QuasiSeparated X.hom] [L.IsInvertible]
    (ψ : (Scheme.Modules.pullback a).obj L ≅ (Scheme.Modules.pullback d.toHom).obj L) (hψ : LineCocycle R R' X d L ψ)
    (hAffine : ∀ x : X.left, ∃ s : 𝟙_ X.left.Modules ⟶ L,
      x ∈ s.zeroLocus.support.compl ∧ IsAffineOpen s.zeroLocus.support.compl) :
    d.IsEffective := by
  have hff := RingHom.faithfullyFlat_algebraMap_iff.mpr
    (inferInstance : Module.FaithfullyFlat R R')
  have hp : Flat p ∧ Surjective p :=
    (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap R R'))).mpr hff
  have : Flat p := hp.1
  have : Surjective p := hp.2
  have : QuasiCompact p := show QuasiCompact (Spec.map _) from inferInstance
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have := isQuasicoherent_L X.left L
  exact d.isEffective_of_span_compatible_sections ψ
    ((X.hom.appLE ⊤ ⊤ le_top).hom.comp (Scheme.ΓSpecIso _).inv.hom)
    (span_compatible_sections R R' X d L ψ hψ) hAffine

end NeronDVR.TensorDescent

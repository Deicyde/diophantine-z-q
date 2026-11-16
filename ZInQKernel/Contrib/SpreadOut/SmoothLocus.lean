import Mathlib
import ZInQKernel.Contrib.SpreadOut.Spread

/-!
# Spreading out, V: descent of smoothness through the smooth locus

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task spread-out, 2026-11-13).

Mathlib only.  For a directed system `D` with limit `c` and `Xᵢ` of finite presentation over `Dᵢ`:
if every point of `Xᵢ ×_{Dᵢ} lim` at which `Xᵢ ×_{Dᵢ} lim → lim` is smooth maps into the smooth
locus of `Xᵢ → Dᵢ` (`hpt`), and `Xᵢ ×_{Dᵢ} lim → lim` is smooth, then `Xᵢ ×_{Dᵢ} Dⱼ → Dⱼ` is smooth
for some `j → i` (`smoothDescendsFor_of_pointwise`).  The smooth locus is open (Mathlib,
`Scheme.Hom.isOpen_smoothLocus`), so this is Mathlib's `exists_map_eq_top` (Stacks 01Z4-type
statement for opens containing the image of the limit) applied to the diagram
`l ↦ Xᵢ ×_{Dᵢ} D l`, plus `smooth_pullback_snd_of_range` (a base change landing in the smooth
locus is smooth).

`SmoothAtLocalizationBaseChange` is the pointwise input for base changes along `Spec S → Spec R`
with `S` a localization of `R` (glue, STANDARD: the stalks of `X ×_R S` are stalks of `X`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry

namespace ZInQ.Contrib.SpreadOut

universe u

/-- A base change whose first projection lands in the smooth locus is smooth. -/
theorem smooth_pullback_snd_of_range {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] (g : Z ⟶ Y)
    (h : ∀ z, pullback.fst f g z ∈ f.smoothLocus) : Smooth (pullback.snd f g) := by
  set U := f.smoothLocus
  haveI : Smooth (U.ι ≫ f) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    exact Scheme.Opens.ι_preimage_self U
  let q : pullback f g ⟶ U := IsOpenImmersion.lift U.ι (pullback.fst f g) (by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact h z)
  have hq : q ≫ U.ι = pullback.fst f g := IsOpenImmersion.lift_fac _ _ _
  let σ : pullback f g ⟶ pullback (U.ι ≫ f) g := pullback.lift q (pullback.snd f g) (by
    rw [← Category.assoc, hq, pullback.condition])
  let p : pullback (U.ι ≫ f) g ⟶ pullback f g :=
    pullback.lift (pullback.fst _ _ ≫ U.ι) (pullback.snd _ _) (by
      rw [Category.assoc, pullback.condition])
  haveI : IsIso σ := by
    refine ⟨p, ?_, ?_⟩
    · apply pullback.hom_ext
      · simp [σ, p, hq]
      · simp [σ, p]
    · apply pullback.hom_ext
      · rw [← cancel_mono U.ι]
        simp [σ, p, hq]
      · simp [σ, p]
  have : pullback.snd f g = σ ≫ pullback.snd (U.ι ≫ f) g := by simp [σ]
  rw [this]
  infer_instance

section Directed

variable {J : Type} [Preorder J] [IsDirectedOrder J] [Nonempty J] (D : Jᵒᵖ ⥤ Scheme.{0})
  [∀ {i j : Jᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
  [∀ i, QuasiSeparatedSpace (D.obj i)] (c : Cone D) (hc : IsLimit c)

include hc in
/-- **Descent of smoothness from the pointwise condition `hpt`.** -/
theorem smoothDescendsFor_of_pointwise
    (hpt : ∀ (i : Jᵒᵖ) (Xi : Over (D.obj i)) [LocallyOfFinitePresentation Xi.hom]
      (y : ↥(pullback Xi.hom (c.π.app i))),
      ((pullback.snd Xi.hom (c.π.app i)).stalkMap y).hom.FormallySmooth →
      pullback.fst Xi.hom (c.π.app i) y ∈ Xi.hom.smoothLocus) :
    SmoothDescendsFor D c := by
  intro i Xi hl hq hs hsm
  haveI : ∀ {l l' : Over i} (φ : l ⟶ l'), IsAffineHom ((bcDiag D Xi).map φ) :=
    fun φ => bcDiag_isAffineHom D Xi φ
  haveI : ∀ l, CompactSpace ((bcDiag D Xi).obj l) := bcDiag_compactSpace D Xi
  have hsm' : Smooth (pullback.snd Xi.hom (c.π.app i)) := hsm
  let U0 : ((bcDiag D Xi).obj (Over.mk (𝟙 i))).Opens :=
    pullback.fst Xi.hom (D.map (𝟙 i)) ⁻¹ᵁ Xi.hom.smoothLocus
  have hU : (bcCone D c Xi).π.app (Over.mk (𝟙 i)) ⁻¹ᵁ U0 = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have e : (bcCone D c Xi).π.app (Over.mk (𝟙 i)) ≫ pullback.fst Xi.hom (D.map (𝟙 i)) =
        pullback.fst Xi.hom (c.π.app i) := by simp
    show ((bcCone D c Xi).π.app (Over.mk (𝟙 i)) ≫ pullback.fst Xi.hom (D.map (𝟙 i))) y ∈
      Xi.hom.smoothLocus
    rw [e]
    apply hpt
    have := (pullback.snd Xi.hom (c.π.app i)).smoothLocus_eq_top
    have hy : y ∈ (pullback.snd Xi.hom (c.π.app i)).smoothLocus := by rw [this]; trivial
    exact hy
  obtain ⟨l, fl, hl'⟩ := exists_map_eq_top (bcDiag D Xi) (bcCone D c Xi)
    (bcConeIsLimit D c hc Xi) U0 hU
  refine ⟨l.left, l.hom, ?_⟩
  show Smooth (pullback.snd Xi.hom (D.map l.hom))
  apply smooth_pullback_snd_of_range
  intro z
  have hz : z ∈ (bcDiag D Xi).map fl ⁻¹ᵁ U0 := by rw [hl']; trivial
  have e : (bcDiag D Xi).map fl ≫ pullback.fst Xi.hom (D.map (𝟙 i)) =
      pullback.fst Xi.hom (D.map l.hom) := by simp
  change ((bcDiag D Xi).map fl ≫ pullback.fst Xi.hom (D.map (𝟙 i))) z ∈ Xi.hom.smoothLocus at hz
  rw [e] at hz
  exact hz

end Directed

/-- **Pointwise smoothness along a localization base change (glue, STANDARD).**  Let `S` be a
localization of `R`, `f : X → Spec R` a morphism and `y` a point of `X ×_R S`.  If the base change
`X ×_R S → Spec S` has a formally smooth stalk map at `y`, then `f` has a formally smooth stalk
map at the image of `y` in `X`.  (The stalk of `X ×_R S` at `y` is the stalk of `X` at its image,
and the stalk of `Spec S` is that of `Spec R`: both are localizations, e.g. EGA I 3.6.1 /
Stacks 01JO for the stalks of a fibre product along a localization; locators UNVERIFIED.) -/
def SmoothAtLocalizationBaseChange : Prop :=
  ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (M : Submonoid R) [IsLocalization M S]
    (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R))
    (y : ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R S))))),
    ((pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R S)))).stalkMap y).hom.FormallySmooth →
    (f.stalkMap (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R S))) y)).hom.FormallySmooth

end ZInQ.Contrib.SpreadOut

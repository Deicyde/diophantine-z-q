/-
H5 lane3 Step 1: `TrivialFibreLocusClosed` (SeesawBridge.lean) PROVED from H72's affine
closedness and ONE comparison obligation. 2026-11-17. New file. SOURCE-ONLY, UNCOMPILED.
Universe u.

The proof shows that the complement `Sᶜ` of the trivial-fibre locus is open.
* For `x ∉ S`, take an affine open `V ∋ x` and `φ := V.fromSpec : Spec Γ(T, V) ⟶ T`, an open
  immersion with range `V`. `Γ(T, V)` is Noetherian because `T` is locally Noetherian, being
  locally of finite type over a field.
* On the base-changed family `f' := pr₂ : X ×_K Spec Γ(V) → Spec Γ(V)` (proper, flat,
  geometrically integral by base change), the trivial-fibre locus is closed by H72
  `isClosed_fibrePicardClass_trivial` (L1/NativeTrivialityLocus.lean fd0f9728…). It equals
  `φ⁻¹' S` by `OpenImmersionFibreIff`.
* So `φ '' (φ⁻¹' Sᶜ)` is an open neighbourhood of `x` inside `Sᶜ` (`φ` is an open map).

ONE obligation (TRUE), `OpenImmersionFibreIff`: along an open immersion `φ : W ⟶ T`, the residue
fibre of the base-changed family at `w` is trivial iff the residue fibre of the original family at
`φ w` is trivial. Open immersions induce isomorphisms of residue fields, so the two fibres are
isomorphic by actual pullback pasting. H72 L2/RelativeFibreTriviality
`fibrePicardClass_baseChange_of_eq_one` gives one direction.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step1.SeesawBridge
import ZInQKernel.Contrib.CloudR2Poincare.L1.NativeTrivialityLocus

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry.Scheme.Modules

namespace ZInQ.Contrib.CloudR2NOS.Step1

/-- The comparison obligation (TRUE; see header). -/
def OpenImmersionFibreIff : Prop :=
  ∀ {K : Type u} [Field K] {X T W : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of K))
    (fT : T ⟶ Spec (CommRingCat.of K)) (φ : W ⟶ T) [IsOpenImmersion φ]
    (L : (Limits.pullback fX fT).Modules) [L.IsInvertible] (w : W),
    Scheme.Pic.map (pullback.fst (pullback.snd fX fT) (T.fromSpecResidueField (φ w)))
        (Scheme.Pic.mk L) = 1 ↔
      Scheme.Pic.map (pullback.fst (pullback.snd fX (φ ≫ fT)) (W.fromSpecResidueField w))
        (Scheme.Pic.mk ((Scheme.Modules.pullback (pullback.map fX (φ ≫ fT) fX fT (𝟙 X) φ (𝟙 _)
          (by simp) (by simp))).obj L)) = 1

/-- `TrivialFibreLocusClosed`, PROVED from H72's affine closedness and `OpenImmersionFibreIff`. -/
theorem trivialFibreLocusClosed (hO : OpenImmersionFibreIff.{u}) :
    TrivialFibreLocusClosed.{u} := by
  intro K _ _ X T fX fT _ _ _ L _
  haveI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian fT
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨V, hxV⟩ : ∃ V : T.affineOpens, x ∈ (V : T.Opens) := by
    have : x ∈ (⨆ V : T.affineOpens, (V : T.Opens)) := by
      rw [iSup_affineOpens_eq_top]
      trivial
    exact Opens.mem_iSup.mp this
  haveI : IsNoetherianRing Γ(T, V.1) := IsLocallyNoetherian.component_noetherian V
  let φ := V.2.fromSpec
  let f' := pullback.snd fX (φ ≫ fT)
  haveI : IsProper f' := inferInstance
  haveI : Flat f' := inferInstance
  haveI : GeometricallyIntegral f' := inferInstance
  let M := (Scheme.Modules.pullback (pullback.map fX (φ ≫ fT) fX fT (𝟙 X) φ (𝟙 _)
    (by simp) (by simp))).obj L
  have hC := ZInQ.Contrib.CloudR2Poincare.L1.isClosed_fibrePicardClass_trivial Γ(T, V.1) f' M
  have heq : φ ⁻¹' {τ : T | Scheme.Pic.map
      (pullback.fst (pullback.snd fX fT) (T.fromSpecResidueField τ)) (Scheme.Pic.mk L) = 1} =
      {y | Scheme.Pic.map (pullback.fst f' ((Spec Γ(T, V.1)).fromSpecResidueField y))
        (Scheme.Pic.mk M) = 1} := by
    ext y
    exact hO fX fT φ L y
  refine ⟨φ '' (φ ⁻¹' {τ : T | Scheme.Pic.map
      (pullback.fst (pullback.snd fX fT) (T.fromSpecResidueField τ)) (Scheme.Pic.mk L) = 1}ᶜ),
    ?_, φ.isOpenEmbedding.isOpenMap _ ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact hy
  · rw [Set.preimage_compl, heq]
    exact hC.isOpen_compl
  · obtain ⟨y, rfl⟩ : x ∈ Set.range φ := by
      rw [IsAffineOpen.range_fromSpec]
      exact hxV
    exact ⟨y, hx, rfl⟩

/-- GM1 v3 resting only on `OpenImmersionFibreIff`, plus the H72 single producers. -/
theorem seesawPulledBack_v3'' (hO : OpenImmersionFibreIff.{u}) : SeesawPulledBack.{u} :=
  seesawPulledBack_v3' (trivialFibreLocusClosed hO)

end ZInQ.Contrib.CloudR2NOS.Step1

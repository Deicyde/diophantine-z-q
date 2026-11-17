import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.DirectImage.CechBaseChange

/-!
# Actual degree-zero Čech augmentation / canonical tensor compatibility

The augmentation is constructed from the native restriction maps. Compatibility
is proved from the VENDORED DEFINITIONS of `cechModuleBaseChange` and
`sectionsModuleBaseChange`, not from a selected cohomology isomorphism.
No W07 source is copied/modified and no desired base-change Fact is introduced.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace ZInQ.Contrib.CloudR2Poincare.L1

/-- The actual degree-zero diagonal of restrictions from an open containing the cover. -/
def cechSectionsDiagonal {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (W : X.Opens)
    (hW : ∀ t : Fin 1 → ι, (⨅ l, U (t l)) ≤ W) :
    Scheme.Modules.sectionsModule f M W →ₗ[Γ(S, ⊤)]
      (∀ t : Fin 1 → ι, Scheme.Modules.sectionsModule f M (⨅ l, U (t l))) :=
  LinearMap.pi fun t ↦ Scheme.Modules.sectionsModuleRestrict f M (hW t)

@[simp] theorem cechSectionsDiagonal_apply {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (W : X.Opens)
    (hW : ∀ t : Fin 1 → ι, (⨅ l, U (t l)) ≤ W)
    (s : Scheme.Modules.sectionsModule f M W) (t : Fin 1 → ι) :
    cechSectionsDiagonal f M U W hW s t = Scheme.Modules.sectionsModuleRestrict f M (hW t) s :=
  rfl

/-- The pulled cover lies in the inverse image of the original top open. -/
theorem pulledCover_le_preimage_top {X Y : Scheme.{u}} (g : Y ⟶ X)
    {ι : Type u} (U : ι → X.Opens) (t : Fin 1 → ι) :
    (⨅ l, g ⁻¹ᵁ U (t l)) ≤ g ⁻¹ᵁ ⊤ := by
  rw [← g.preimage_iInf]
  exact g.preimage_mono le_top

/-- On a PURE tensor, actual Čech degree-zero base change commutes with the
actual canonical coefficient-sections map. -/
theorem cechDiagonal_baseChange_tmul
    {X Y S T : Scheme.{u}} {f : X ⟶ S} {f' : Y ⟶ T} {g : T ⟶ S} {g' : Y ⟶ X}
    (square : IsPullback g' f' f g) (M : X.Modules)
    [Algebra Γ(S, ⊤) Γ(T, ⊤)] (hg : algebraMap Γ(S, ⊤) Γ(T, ⊤) = g.appTop.hom)
    {ι : Type u} (U : ι → X.Opens) (b : Γ(T, ⊤))
    (s : Scheme.Modules.sectionsModule f M ⊤) :
    Scheme.Modules.cechModuleBaseChange square M hg U 0
        (b ⊗ₜ[Γ(S, ⊤)] cechSectionsDiagonal f M U ⊤ (fun _ ↦ le_top) s) =
      cechSectionsDiagonal f' ((Scheme.Modules.pullback g').obj M)
        (fun i ↦ g' ⁻¹ᵁ U i) (g' ⁻¹ᵁ ⊤) (pulledCover_le_preimage_top g' U)
        (Scheme.Modules.sectionsModuleBaseChange square M hg ⊤ (b ⊗ₜ[Γ(S, ⊤)] s)) := by
  funext t
  rw [Scheme.Modules.cechModuleBaseChange_tmul, cechSectionsDiagonal_apply,
    Scheme.Modules.sectionsModuleBaseChange_tmul, cechSectionsDiagonal_apply]
  have hn := Scheme.Modules.presheaf_map_smul_pullbackSection
    (f := f) (f' := f') (g' := g') M
    (le_top : (⨅ l : Fin 1, U (t l)) ≤ ⊤) b s
  rw [← hn, Scheme.Modules.sectionsModuleRestrict_comp]

/-- The whole native tensor map commutes with the actual degree-zero augmentation. -/
theorem cechDiagonal_baseChange
    {X Y S T : Scheme.{u}} {f : X ⟶ S} {f' : Y ⟶ T} {g : T ⟶ S} {g' : Y ⟶ X}
    (square : IsPullback g' f' f g) (M : X.Modules)
    [Algebra Γ(S, ⊤) Γ(T, ⊤)] (hg : algebraMap Γ(S, ⊤) Γ(T, ⊤) = g.appTop.hom)
    {ι : Type u} (U : ι → X.Opens)
    (x : Γ(T, ⊤) ⊗[Γ(S, ⊤)] Scheme.Modules.sectionsModule f M ⊤) :
    Scheme.Modules.cechModuleBaseChange square M hg U 0
        ((cechSectionsDiagonal f M U ⊤ (fun _ ↦ le_top)).baseChange Γ(T, ⊤) x) =
      cechSectionsDiagonal f' ((Scheme.Modules.pullback g').obj M)
        (fun i ↦ g' ⁻¹ᵁ U i) (g' ⁻¹ᵁ ⊤) (pulledCover_le_preimage_top g' U)
        (Scheme.Modules.sectionsModuleBaseChange square M hg ⊤ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b s =>
      rw [LinearMap.baseChange_tmul]
      exact cechDiagonal_baseChange_tmul square M hg U b s

end ZInQ.Contrib.CloudR2Poincare.L1

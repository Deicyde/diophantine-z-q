/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_RelEffCartierDiv_IsUniversal_geometricallyConnected. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelEffCartierDivFunctor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_IsUniversal_exists_sumMap
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_CategoryTheory_MorphismProperty_widePullback_base
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_GeometricallyConnected_of_comp_of_surjective
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_IsUniversal_geometricallyConnected

set_option autoImplicit false

universe u
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open P2MW.S_AlgebraicGeometry_RelEffCartierDiv_IsUniversal_geometricallyConnected.AlgebraicGeometry

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (SmoothOfRelativeDimension.smooth SmoothOfRelativeDimension geometrically_iff_of_isClosedUnderIsomorphisms GeometricallyConnected.comp Scheme Smooth UniversallyOpen IsSeparated GeometricallyConnected geometrically RelEffCartierDiv.IsUniversal RelEffCartierDiv fibrePowOver fibrePowOver.toBase RelEffCartierDiv.IsUniversal.exists_sumMap GeometricallyConnected.of_comp_of_surjective)
open AlgebraicGeometry

namespace GeometricallyConnected p2m_export "AlgebraicGeometry.GeometricallyConnected" "comp of_comp_of_surjective" end GeometricallyConnected
open scoped AlgebraicGeometry.GeometricallyConnected in
theorem GeometricallyConnected.id (X : Scheme.{u}) : GeometricallyConnected (𝟙 X) := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ k ↦ ?_⟩
  rw [(pullback.snd (𝟙 X) k).homeomorph.connectedSpace_iff]
  infer_instance

theorem isMultiplicative_geometricallyConnected_inf_universallyOpen :
    (@GeometricallyConnected ⊓ @UniversallyOpen : MorphismProperty Scheme.{u}).IsMultiplicative where
  id_mem X := ⟨GeometricallyConnected.id X, inferInstance⟩
  comp_mem f g hf hg := by
    obtain ⟨hf₁, hf₂⟩ := hf
    obtain ⟨hg₁, hg₂⟩ := hg
    exact ⟨GeometricallyConnected.comp f g, inferInstance⟩

end AlgebraicGeometry

theorem solution
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    [GeometricallyConnected f] {r : ℕ} {Y : Scheme.{u}} {y : Y ⟶ S}
    {Duniv : RelEffCartierDiv f r y} (hU : Duniv.IsUniversal) : GeometricallyConnected y := by
  obtain ⟨σ, hσ, -, -, -, -, hsurj, -⟩ := hU.exists_sumMap
  have : Smooth f := SmoothOfRelativeDimension.smooth (n := 1) (f := f)
  have : UniversallyOpen f := inferInstance
  have := isMultiplicative_geometricallyConnected_inf_universallyOpen.{u}
  have hGC : (@GeometricallyConnected ⊓ @UniversallyOpen : MorphismProperty Scheme.{u})
      (fibrePowOver.toBase f r) :=
    MorphismProperty.widePullback_base (P := @GeometricallyConnected ⊓ @UniversallyOpen)
      (fun _ : Fin r ↦ 𝒞) (fun _ ↦ f) fun _ ↦ ⟨‹_›, ‹_›⟩
  have : GeometricallyConnected (σ ≫ y) := by rw [hσ]; exact hGC.1
  exact GeometricallyConnected.of_comp_of_surjective σ y

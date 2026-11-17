/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_AffineLimit
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardStageHom
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

theorem AlgebraicGeometry.RelPicard.LFP.exists_fg_nonempty_iso_pullbackAlong
    (R : Type u) [CommRing R] {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover) (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (A : Type u) [CommRing A] [Algebra R A] (M : RigidifiedLineBundle c ε (Scheme.TwoAffineOpenCover.specMap R A)) :
    ∃ (A₀ : Subalgebra R A) (_ : A₀.FG) (M₀ : RigidifiedLineBundle c ε (Scheme.TwoAffineOpenCover.specMap R A₀)),
      Nonempty ((M₀.pullbackAlong (RelPicard.LFP.stageHom R A₀.val)).L ≅ M.L) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong.solution

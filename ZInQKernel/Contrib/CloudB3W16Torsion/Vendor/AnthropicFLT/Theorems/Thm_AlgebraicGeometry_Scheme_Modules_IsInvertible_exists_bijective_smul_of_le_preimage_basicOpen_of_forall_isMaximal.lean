/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_bijective_smul_of_le_preimage_basicOpen_of_forall_isMaximal. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_bijective_smul_of_le_preimage_basicOpen_of_forall_isMaximal

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_bijective_smul_of_le_preimage_basicOpen_of_forall_isMaximal
    {R : Type u} [CommRing R] [IsNoetherianRing R] [_root_.IsReduced R] [IsJacobsonRing R] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of R)) [IsProper f] [Flat f]
    (hO : ∀ 𝔭 : PrimeSpectrum R,
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap R 𝔭.asIdeal.ResidueField)) ⊤
      Function.Bijective (algebraMap 𝔭.asIdeal.ResidueField
        Γ(Limits.pullback f (Scheme.TwoAffineOpenCover.specMap R 𝔭.asIdeal.ResidueField), ⊤)))
    (L : Y.Modules) (hL : Scheme.Modules.IsInvertible L)
    (htriv : ∀ 𝔪 : PrimeSpectrum R, 𝔪.asIdeal.IsMaximal →
      Nonempty ((Scheme.Modules.pullback
        (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R 𝔪.asIdeal.ResidueField))).obj L ≅
        SheafOfModules.unit
          (Limits.pullback f (Scheme.TwoAffineOpenCover.specMap R 𝔪.asIdeal.ResidueField)).ringCatSheaf))
    (𝔭 : PrimeSpectrum R) :
    ∃ (g : R) (m : Γ(L, ⊤)), g ∉ 𝔭.asIdeal ∧ ∀ V : Y.Opens, V ≤ f ⁻¹ᵁ (PrimeSpectrum.basicOpen g) →
      Function.Bijective fun a : Γ(Y, V) =>
        a • (L.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op m : Γ(L, V)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_bijective_smul_of_le_preimage_basicOpen_of_forall_isMaximal.solution

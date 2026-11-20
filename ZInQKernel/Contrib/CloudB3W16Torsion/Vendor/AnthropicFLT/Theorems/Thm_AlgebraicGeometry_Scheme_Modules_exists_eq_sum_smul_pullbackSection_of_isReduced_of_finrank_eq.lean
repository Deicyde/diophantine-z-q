/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_eq_sum_smul_pullbackSection_of_isReduced_of_finrank_eq. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_eq_sum_smul_pullbackSection_of_isReduced_of_finrank_eq

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits open AlgebraicGeometry hiding OModulePresheaf

theorem AlgebraicGeometry.Scheme.Modules.exists_eq_sum_smul_pullbackSection_of_isReduced_of_finrank_eq
    {R : Type u} [CommRing R] [IsNoetherianRing R] [_root_.IsReduced R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] (M : X.Modules)
    (htriv : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))
    (r : ℕ)
    (hconst : ∀ 𝔭 : PrimeSpectrum R,
      letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
        (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap R 𝔭.asIdeal.ResidueField))
        ((Scheme.Modules.pullback
          (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R 𝔭.asIdeal.ResidueField))).obj M) ⊤
      Module.finrank 𝔭.asIdeal.ResidueField
        Γ((Scheme.Modules.pullback
          (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R 𝔭.asIdeal.ResidueField))).obj M, ⊤) = r)
    (A : Type u) [CommRing A] [Algebra R A]
    {k : ℕ} (τ : Fin k → Γ((Scheme.Modules.pullback
        (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A))).obj M, ⊤)) :
    ∃ (N : ℕ) (m : Fin (N + 1) → Γ(M, ⊤)) (c : Fin k → Fin (N + 1) → A), ∀ i,
      τ i = ∑ j, ((Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap R A)).appTop
                    ((Scheme.ΓSpecIso (.of A)).inv (c i j))) •
        (show Γ((Scheme.Modules.pullback
                  (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A))).obj M, ⊤) from
          (((Scheme.Modules.pullbackPushforwardAdjunction
            (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A))).unit.app M).app ⊤) (m j)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_eq_sum_smul_pullbackSection_of_isReduced_of_finrank_eq.solution

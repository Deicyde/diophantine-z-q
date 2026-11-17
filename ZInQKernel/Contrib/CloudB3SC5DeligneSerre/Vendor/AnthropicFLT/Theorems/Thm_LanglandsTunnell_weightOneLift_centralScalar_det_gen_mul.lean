/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_LanglandsTunnell_weightOneLift_centralScalar_det_gen_mul (git blob 8fd683b0ffa68a2698d781e1fd4a13326250fd34, sha256 9919d1d98c5e9c67cecc08bec7d23698c7dea8c49b42c81282c6adf20c52e928).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_DihedralWeightOneLift
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_DirichletCharacter_DirichletIdeleChar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_LanglandsTunnell_weightOneLift_centralScalar_det_gen_mul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open NumberField AutomorphicForm UpperHalfPlane DihedralWeightOne
open IsDedekindDomain
open scoped ModularForm MatrixGroups

theorem LanglandsTunnell.weightOneLift_centralScalar_det_gen_mul
    {n : ℕ} [NeZero n] (hn : n ≠ 0) (f : ℍ → ℂ)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (χ : DirichletCharacter ℂ n)
    (hχ : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 n →
      f ∣[(1 : ℤ)] (γ : GL (Fin 2) ℝ) = χ ((γ 1 1 : ℤ) : ZMod n) • f)
    (Φ : HeckeEigensystem ℚ ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hb : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      Φ.b v = ((((DirichletCharacter.dirichletIdeleChar χ *
          (Units.map (Complex.ofRealHom.toMonoidHom.comp NNReal.toRealHom.toMonoidHom)).comp
            (MeasureTheory.distribHaarChar (AdeleRing (𝓞 ℚ) ℚ)).toHomUnits).comp
          Matrix.GeneralLinearGroup.det) ((productionPinsCompact ℚ).gen v) : ℂˣ) : ℂ)) :
    ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
    ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f
          (centralScalar (𝓞 ℚ) ℚ (Matrix.GeneralLinearGroup.det ((productionPinsCompact ℚ).gen v)) * g)
        = Φ.b v * weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f g := by
  revert n hn f hf χ hχ Φ S hb
  exact @_root_.P2MW.S_LanglandsTunnell_weightOneLift_centralScalar_det_gen_mul.solution

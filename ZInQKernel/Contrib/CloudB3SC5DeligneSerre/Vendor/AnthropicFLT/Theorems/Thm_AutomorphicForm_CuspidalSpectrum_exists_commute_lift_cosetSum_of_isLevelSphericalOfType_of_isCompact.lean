/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_commute_lift_cosetSum_of_isLevelSphericalOfType_of_isCompact (git blob 5f43c49b82e79c48b132db194003a914e6efaf69, sha256 3312b9fcb2bc0669e64168b9170c477d0e14fe310dc19c736a05721ca1c70058).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchSpherical
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_CuspidalSpectrum_exists_commute_lift_cosetSum_of_isLevelSphericalOfType_of_isCompact

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.CuspidalSpectrum.exists_commute_lift_cosetSum_of_isLevelSphericalOfType_of_isCompact
    (F : Type) [Field F] [NumberField F]
    {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (hσ : HasModulus F ξ σ)
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F)
    (tys : AutomorphicForm.ArchTypeFamily F)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f)
    (hsph : IsLevelSphericalOfType F tys U f)
    (Tc : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ))
    (hcomm : ∀ (φ : ↥(cuspMemberSubmodule F Φ₀ ξ)) (hφ' : rightConv F φ f ∈ cuspMemberSubmodule F Φ₀ ξ),
        Tc (toCuspSubcarrier F hΦ₀ σ ξ φ) = toCuspSubcarrier F hΦ₀ σ ξ ⟨rightConv F φ f, hφ'⟩)
    (g : AdelicGL2 (𝓞 F) F) (hg : g ∈ finiteAdelicGL2Subgroup F) (n : ℕ) (reps : Fin n → AdelicGL2 (𝓞 F) F)
    (h1 : ∀ i, ∃ u' ∈ U, ∃ u'' ∈ U, reps i = u' * g * u'')
    (h2 : ∀ x : AdelicGL2 (𝓞 F) F, (∃ u' ∈ U, ∃ u'' ∈ U, x = u' * g * u'') → ∃ i, ∃ u' ∈ U, x = reps i * u')
    (h3 : ∀ i j, (reps i)⁻¹ * reps j ∈ U → i = j) :
    ∃ S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ), S.comp Tc = Tc.comp S ∧
      ∀ φ : ↥(cuspMemberSubmodule F Φ₀ ξ),
        (φ : AdelicGL2 (𝓞 F) F → ℂ) ∈ Representation.invariants ((rightRegular F).comp U.subtype) →
        ∃ h : (fun x => ∑ i, (φ : AdelicGL2 (𝓞 F) F → ℂ) (x * reps i)) ∈ cuspMemberSubmodule F Φ₀ ξ,
          S (toCuspSubcarrier F hΦ₀ σ ξ φ) = toCuspSubcarrier F hΦ₀ σ ξ ⟨fun x => ∑ i, (φ : AdelicGL2 (𝓞 F) F → ℂ) (x * reps i), h⟩ := by
  revert F α β Φ₀ hΦ₀ σ ξ hσ U hU O hO hUO tys f hf hsph Tc hcomm g hg n reps h1 h2 h3
  exact @_root_.P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_commute_lift_cosetSum_of_isLevelSphericalOfType_of_isCompact.solution

/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_CuspidalConstituent_iInf_isCuspSubrep_inf_invariants_inf_archCutSubmodule_le (git blob 052bf289434f99b49dc4fe8470a6c660eace7a18, sha256 098ad0c5b9ccd493b2d3274030a49c61ae40bd6948dd6a8a083147c39281427e).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_CuspidalConstituent_iInf_isCuspSubrep_inf_invariants_inf_archCutSubmodule_le

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

theorem AutomorphicForm.CuspidalConstituent.iInf_isCuspSubrep_inf_invariants_inf_archCutSubmodule_le
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F)
    (tys : AutomorphicForm.ArchTypeFamily F)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hV : IsCuspSubrep F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ V)
    (M : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hMk : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion),
      ∀ φ ∈ M, rightTranslate F (rowIsometryInclAt₀ F w k) φ ∈ M)
    (hMhecke : ∀ g ∈ finiteAdelicGL2Subgroup F, ∀ (n : ℕ) (reps : Fin n → AdelicGL2 (𝓞 F) F),
      (∀ i, ∃ u ∈ U, ∃ u' ∈ U, reps i = u * g * u') →
      (∀ x : AdelicGL2 (𝓞 F) F, (∃ u ∈ U, ∃ u' ∈ U, x = u * g * u') → ∃ i, ∃ u ∈ U, x = reps i * u) →
      (∀ i j, (reps i)⁻¹ * reps j ∈ U → i = j) →
      ∀ φ ∈ M ⊓ Representation.invariants ((rightRegular F).comp U.subtype), (fun x => ∑ i, φ (x * reps i)) ∈ M)
    (hMconv : ∀ f : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F f → IsArchBiFinite F tys f →
      (∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, f (u * x) = f x ∧ f (x * u) = f x) → ∀ φ ∈ M, rightConv F φ f ∈ M) :
    (⨅ (W : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
        (_ : IsCuspSubrep F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ W ∧ V ⊓ Representation.invariants ((rightRegular F).comp U.subtype) ⊓ archCutSubmodule F tys ⊓ M ≤ W), W)
      ⊓ Representation.invariants ((rightRegular F).comp U.subtype) ⊓ archCutSubmodule F tys ≤ M := by
  revert F D ξ U hU O hO hUO tys V hV M hMk hMhecke hMconv
  exact @_root_.P2MW.S_AutomorphicForm_CuspidalConstituent_iInf_isCuspSubrep_inf_invariants_inf_archCutSubmodule_le.solution

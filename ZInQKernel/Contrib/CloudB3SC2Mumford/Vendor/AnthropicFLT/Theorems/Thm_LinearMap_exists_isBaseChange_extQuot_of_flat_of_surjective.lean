/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_LinearMap_exists_isBaseChange_extQuot_of_flat_of_surjective
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_LinearMap_exists_isBaseChange_extQuot_of_flat_of_surjective

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u v

theorem LinearMap.exists_isBaseChange_extQuot_of_flat_of_surjective
    {B : Type u} [CommRing B] [IsNoetherianRing B] {B' : Type u} [CommRing B'] [Algebra B B'] [Module.Flat B B']
    {M : Type v} [AddCommGroup M] [Module B M] {N : Type v} [AddCommGroup N] [Module B N]
    {M' : Type v} [AddCommGroup M'] [Module B M'] [Module B' M'] [IsScalarTower B B' M']
    {N' : Type v} [AddCommGroup N'] [Module B N'] [Module B' N'] [IsScalarTower B B' N']
    (μ : M →ₗ[B] M') (hμ : IsBaseChange B' μ) (ν : N →ₗ[B] N') (hν : IsBaseChange B' ν)
    {r : ℕ} (p : (Fin r → B) →ₗ[B] M) (hp : Function.Surjective p)
    (p' : (Fin r → B') →ₗ[B'] M') (hp' : ∀ v : Fin r → B, p' (fun i => algebraMap B B' (v i)) = μ (p v)) :
    Function.Surjective p' ∧
    ∃ (g : ↥(LinearMap.ker p) →ₗ[B] ↥(LinearMap.ker p'))
      (T : ((↥(LinearMap.ker p) →ₗ[B] N) ⧸ LinearMap.range (LinearMap.lcomp B N (LinearMap.ker p).subtype)) →ₗ[B]
           ((↥(LinearMap.ker p') →ₗ[B'] N') ⧸ LinearMap.range (LinearMap.lcomp B' N' (LinearMap.ker p').subtype))),
      (∀ (s : ↥(LinearMap.ker p)) (i : Fin r), ((g s : ↥(LinearMap.ker p')) : Fin r → B') i = algebraMap B B' ((s : Fin r → B) i)) ∧
      IsBaseChange B' T ∧
      (∀ δ : ↥(LinearMap.ker p) →ₗ[B] N, ∃ δ' : ↥(LinearMap.ker p') →ₗ[B'] N', ∀ s : ↥(LinearMap.ker p), δ' (g s) = ν (δ s)) ∧
      (∀ (δ : ↥(LinearMap.ker p) →ₗ[B] N) (δ' : ↥(LinearMap.ker p') →ₗ[B'] N'),
        (∀ s : ↥(LinearMap.ker p), δ' (g s) = ν (δ s)) →
        T (Submodule.Quotient.mk δ) = Submodule.Quotient.mk δ') := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_exists_isBaseChange_extQuot_of_flat_of_surjective.solution

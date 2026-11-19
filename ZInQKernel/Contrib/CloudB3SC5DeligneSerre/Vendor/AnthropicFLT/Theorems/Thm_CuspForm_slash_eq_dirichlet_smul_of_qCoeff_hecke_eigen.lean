/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CuspForm_slash_eq_dirichlet_smul_of_qCoeff_hecke_eigen (git blob cb3c3932383937e63928c54858b1bb35fba75c49, sha256 701a33cbb2718394445ecac18610f59bf19e340cfbea9ce935538a44f298f596).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularForm_HeckeOperator
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Modularity
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CuspForm_slash_eq_dirichlet_smul_of_qCoeff_hecke_eigen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open CongruenceSubgroup ModularForm
open scoped ModularForm UpperHalfPlane MatrixGroups

theorem CuspForm.slash_eq_dirichlet_smul_of_qCoeff_hecke_eigen
    {M : ℕ} [NeZero M] (k : ℤ)
    (g : CuspForm ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
    (χ : DirichletCharacter ℂ M)
    (heig : ∀ p : ℕ, p.Prime → ¬ p ∣ M → ∃ lam : ℂ, ∀ n : ℕ,
      ModularFormClass.qCoeff (⇑g) (n * p)
        + χ (p : ZMod M) * (p : ℂ) ^ (k - 1)
            * (if p ∣ n then ModularFormClass.qCoeff (⇑g) (n / p) else 0)
        = lam * ModularFormClass.qCoeff (⇑g) n)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    (⇑g : ℍ → ℂ) ∣[k] γ = χ ((γ 1 1 : ℤ) : ZMod M) • (⇑g : ℍ → ℂ) := by
  revert M k g χ heig γ hγ
  exact @_root_.P2MW.S_CuspForm_slash_eq_dirichlet_smul_of_qCoeff_hecke_eigen.solution

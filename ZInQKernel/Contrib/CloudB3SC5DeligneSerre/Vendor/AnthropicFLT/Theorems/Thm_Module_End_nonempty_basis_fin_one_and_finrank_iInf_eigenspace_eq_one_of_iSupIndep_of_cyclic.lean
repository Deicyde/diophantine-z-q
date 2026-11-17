/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Module_End_nonempty_basis_fin_one_and_finrank_iInf_eigenspace_eq_one_of_iSupIndep_of_cyclic (git blob 26e4f0157d29df30c9937366423e78656fe77802, sha256 688f21986d79b46829c9f1996c391440cf4f7e9d2b55f1ead93dc422e3f1a3f1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Order.SupIndep
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Module_End_nonempty_basis_fin_one_and_finrank_iInf_eigenspace_eq_one_of_iSupIndep_of_cyclic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem Module.End.nonempty_basis_fin_one_and_finrank_iInf_eigenspace_eq_one_of_iSupIndep_of_cyclic
    {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {ι : Type*} [Fintype ι]
    (V : ι → Submodule K W) (hVind : iSupIndep V) (hVtop : iSup V = ⊤)
    (A : Subalgebra K (Module.End K W))
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hstab : ∀ a ∈ A, ∀ (i : ι), ∀ v ∈ V i, a v ∈ V i)
    (e : ι → ↥A) (he₁ : ∀ (i : ι), ∀ v ∈ V i, (e i : Module.End K W) v = v)
    (he₀ : ∀ (i j : ι), j ≠ i → ∀ v ∈ V j, (e i : Module.End K W) v = 0)
    (w : ι → W) (hw : ∀ i, w i ∈ V i)
    (hcyc : ∀ (i : ι), ∀ v ∈ V i, ∃ a : ↥A, (a : Module.End K W) (w i) = v)
    (hle : ∀ (i : ι) (χ : ↥A →ₐ[K] K),
      Module.finrank K ↥(V i ⊓ ⨅ a : ↥A, Module.End.eigenspace (a : Module.End K W) (χ a)) ≤ 1) :
    Nonempty (Module.Basis (Fin 1) ↥A W) ∧
    ∀ χ : ↥A →ₐ[K] K,
      Module.finrank K ↥(⨅ a : ↥A, Module.End.eigenspace (a : Module.End K W) (χ a)) = 1 := by
  revert K W ι V hVind hVtop A hcomm hstab e he₁ he₀ w hw hcyc hle
  exact @_root_.P2MW.S_Module_End_nonempty_basis_fin_one_and_finrank_iInf_eigenspace_eq_one_of_iSupIndep_of_cyclic.solution

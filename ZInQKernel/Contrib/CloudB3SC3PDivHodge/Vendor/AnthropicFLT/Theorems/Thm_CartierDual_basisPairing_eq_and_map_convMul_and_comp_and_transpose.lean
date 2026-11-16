/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CartierDual_basisPairing_eq_and_map_convMul_and_comp_and_transpose
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Definitions.Def_HopfAlgebra_CartierDual
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Definitions.Def_HopfAlgebra_CartierDualInstances
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.P2M.Sol.S_CartierDual_basisPairing_eq_and_map_convMul_and_comp_and_transpose

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped TensorProduct

theorem CartierDual.basisPairing_eq_and_map_convMul_and_comp_and_transpose
    {R : Type*} [inst_t1 : CommRing R] {A : Type*} [inst_t2 : CommRing A] [inst_t3 : HopfAlgebra R A]
    [inst_t4 : Module.Finite R A] [inst_t5 : Module.Free R A]
    {ι : Type*} [inst_t6 : Fintype ι] (b : Module.Basis ι R A)
    (L : Type*) [inst_t7 : CommRing L] [inst_t8 : Algebra R L] :

    (∀ {ι' : Type*} [Fintype ι'] (b' : Module.Basis ι' R A)
        (f : A →ₗ[R] L) (Ψ : Module.Dual R A →ₗ[R] L),
        ∑ i, f (b i) * Ψ (b.coord i) = ∑ j, f (b' j) * Ψ (b'.coord j)) ∧

    (∀ {L' : Type*} [CommRing L'] [Algebra R L'] (φ : L →ₐ[R] L')
        (f : A →ₗ[R] L) (Ψ : Module.Dual R A →ₗ[R] L),
        φ (∑ i, f (b i) * Ψ (b.coord i)) = ∑ i, φ (f (b i)) * φ (Ψ (b.coord i))) ∧

    (∀ {A' : Type*} [AddCommGroup A'] [Module R A'] {ι' : Type*} [Fintype ι'] (b' : Module.Basis ι' R A')
        (t : A' →ₗ[R] A) (_ : Function.Surjective t) (N : A' →ₗ[R] A')
        (u : Module.Dual R A' →ₗ[R] Module.Dual R A) (_ : ∀ (φ' : Module.Dual R A') (a' : A'), u φ' (t a') = φ' (N a'))
        (f : A →ₗ[R] L) (F : A' →ₗ[R] L) (_ : ∀ a' : A', F (N a') = f (t a'))
        (Ψ : Module.Dual R A →ₗ[R] L),
        ∑ k, F (b' k) * Ψ (u (b'.coord k)) = ∑ i, f (b i) * Ψ (b.coord i)) ∧

    (∀ (f g : WithConv (A →ₐ[R] L)) (ψ : CartierDual R A →ₐ[R] L),
        ∑ i, (f * g) (b i) * ψ (CartierDual.ofDual R A (b.coord i)) =
          (∑ i, f (b i) * ψ (CartierDual.ofDual R A (b.coord i))) *
            ∑ i, g (b i) * ψ (CartierDual.ofDual R A (b.coord i))) ∧

    (∀ (f : A →ₐ[R] L) (ψ ψ' : WithConv (CartierDual R A →ₐ[R] L)),
        ∑ i, f (b i) * (ψ * ψ') (CartierDual.ofDual R A (b.coord i)) =
          (∑ i, f (b i) * ψ (CartierDual.ofDual R A (b.coord i))) *
            ∑ i, f (b i) * ψ' (CartierDual.ofDual R A (b.coord i))) ∧

    (∀ ψ : CartierDual R A →ₐ[R] L,
        ∑ i, (1 : WithConv (A →ₐ[R] L)) (b i) * ψ (CartierDual.ofDual R A (b.coord i)) = 1) ∧
    (∀ f : A →ₐ[R] L,
        ∑ i, f (b i) * (1 : WithConv (CartierDual R A →ₐ[R] L)) (CartierDual.ofDual R A (b.coord i)) = 1) ∧

    (∀ (f : WithConv (A →ₐ[R] L)) (ψ : CartierDual R A →ₐ[R] L) (n : ℕ),
        ∑ i, (f ^ n) (b i) * ψ (CartierDual.ofDual R A (b.coord i)) =
          (∑ i, f (b i) * ψ (CartierDual.ofDual R A (b.coord i))) ^ n) :=
  @_root_.P2MW.S_CartierDual_basisPairing_eq_and_map_convMul_and_comp_and_transpose.solution R inst_t1 A inst_t2 inst_t3 inst_t4 inst_t5 ι inst_t6 b L inst_t7 inst_t8

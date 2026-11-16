/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_isCoherent_linearEquiv_extQuot_of_isCoherent
    {A : Type u} [CommRing A] {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsLocallyNoetherian P]
    (H K : OModulePresheaf q)
    (hHc : H.IsCoherent) (hHq : H.IsQuasicoherent) (hKc : K.IsCoherent) (hKq : K.IsQuasicoherent) :
    ∃ (X : OModulePresheaf q)
      (ε : ∀ (W : P.affineOpens) (r : ℕ) (p : (Fin r → Γ(P, W.1)) →ₗ[Γ(P, W.1)] H.obj W.1), Function.Surjective p →
        (X.obj W.1 ≃ₗ[Γ(P, W.1)]
          ((↥(LinearMap.ker p) →ₗ[Γ(P, W.1)] K.obj W.1) ⧸
            LinearMap.range (LinearMap.lcomp (Γ(P, W.1)) (K.obj W.1) (LinearMap.ker p).subtype)))),
      X.IsCoherent ∧ X.IsQuasicoherent ∧
      ∀ (W W' : P.affineOpens) (h : W'.1 ≤ W.1)
        (r : ℕ) (p : (Fin r → Γ(P, W.1)) →ₗ[Γ(P, W.1)] H.obj W.1) (hp : Function.Surjective p)
        (r' : ℕ) (p' : (Fin r' → Γ(P, W'.1)) →ₗ[Γ(P, W'.1)] H.obj W'.1) (hp' : Function.Surjective p')
        (g : (Fin r → Γ(P, W.1)) →+ (Fin r' → Γ(P, W'.1)))
        (_hg : ∀ (a : Γ(P, W.1)) (v : Fin r → Γ(P, W.1)), g (a • v) = (P.presheaf.map (homOfLE h).op).hom a • g v)
        (hgp : ∀ v : Fin r → Γ(P, W.1), p' (g v) = H.res h (p v))
        (δ : ↥(LinearMap.ker p) →ₗ[Γ(P, W.1)] K.obj W.1) (δ' : ↥(LinearMap.ker p') →ₗ[Γ(P, W'.1)] K.obj W'.1)
        (hδ : ∀ s : ↥(LinearMap.ker p),
          δ' ⟨g s.1, by rw [LinearMap.mem_ker, hgp, (LinearMap.mem_ker.mp s.2), map_zero]⟩ = K.res h (δ s)),
        X.res h ((ε W r p hp).symm (Submodule.Quotient.mk δ)) = (ε W' r' p' hp').symm (Submodule.Quotient.mk δ') := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.solution

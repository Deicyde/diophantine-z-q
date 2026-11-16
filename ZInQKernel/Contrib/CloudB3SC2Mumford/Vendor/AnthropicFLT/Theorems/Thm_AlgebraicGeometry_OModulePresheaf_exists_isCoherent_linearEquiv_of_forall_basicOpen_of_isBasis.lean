/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis
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
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis
    {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (CommRingCat.of R))

    (B : Set V.affineOpens)
    (hdown : ∀ (W W' : V.affineOpens), W'.1 ≤ W.1 → W ∈ B → W' ∈ B)
    (hcov : ∀ x : V, ∃ W ∈ B, x ∈ W.1)

    (M : ↥B → Type u) [∀ W, AddCommGroup (M W)] [∀ W, Module R (M W)] [∀ W, Module Γ(V, W.1.1) (M W)]
    [∀ W : ↥B, letI := Scheme.TwoAffineOpenCover.algebraOfHom π W.1.1; IsScalarTower R Γ(V, W.1.1) (M W)]
    (res : ∀ {W W' : ↥B}, W'.1.1 ≤ W.1.1 → (M W →ₗ[R] M W'))
    (res_smul : ∀ {W W' : ↥B} (h : W'.1.1 ≤ W.1.1) (a : Γ(V, W.1.1)) (x : M W),
      res h (a • x) = (V.presheaf.map (homOfLE h).op).hom a • res h x)
    (res_refl : ∀ (W : ↥B) (x : M W), res (le_refl W.1.1) x = x)
    (res_comp : ∀ {W W' W'' : ↥B} (h : W''.1.1 ≤ W'.1.1) (h' : W'.1.1 ≤ W.1.1) (x : M W),
      res (h.trans h') x = res h (res h' x))
    (hqc : ∀ (W Wg : ↥B) (g : Γ(V, W.1.1)) (hWg : Wg.1.1 = V.basicOpen g),
      (∀ y : M Wg, ∃ (n : ℕ) (x : M W),
          res (hWg.trans_le (V.basicOpen_le g)) x =
            (V.presheaf.map (homOfLE (hWg.trans_le (V.basicOpen_le g))).op).hom (g ^ n) • y) ∧
      (∀ x : M W, res (hWg.trans_le (V.basicOpen_le g)) x = 0 → ∃ n : ℕ, (g ^ n) • x = 0))
    (hfg : ∀ W : ↥B, Module.Finite (Γ(V, W.1.1) : Type u) (M W)) :
    ∃ (G : OModulePresheaf π) (e : ∀ W : ↥B, G.obj W.1.1 ≃ₗ[R] M W),
      G.IsCoherent ∧ G.IsQuasicoherent ∧
      (∀ (W : ↥B) (a : Γ(V, W.1.1)) (x : G.obj W.1.1), e W (a • x) = a • e W x) ∧
      (∀ (W W' : ↥B) (h : W'.1.1 ≤ W.1.1) (x : G.obj W.1.1), e W' (G.res h x) = res h (e W x)) ∧

      (∀ (F : OModulePresheaf π), F.IsQuasicoherent →
        ∀ (θ : ∀ W : ↥B, M W →ₗ[R] F.obj W.1.1),
          (∀ (W : ↥B) (a : Γ(V, W.1.1)) (x : M W), θ W (a • x) = a • θ W x) →
          (∀ (W W' : ↥B) (h : W'.1.1 ≤ W.1.1) (x : M W), θ W' (res h x) = F.res h (θ W x)) →
          ∃! Φ : OModulePresheaf.AffHom G F, ∀ (W : ↥B) (x : G.obj W.1.1), Φ.app W.1 x = θ W (e W x)) ∧

      (∀ (F : OModulePresheaf π), F.IsQuasicoherent →
        ∀ (ϑ : ∀ W : ↥B, F.obj W.1.1 →ₗ[R] M W),
          (∀ (W : ↥B) (a : Γ(V, W.1.1)) (x : F.obj W.1.1), ϑ W (a • x) = a • ϑ W x) →
          (∀ (W W' : ↥B) (h : W'.1.1 ≤ W.1.1) (x : F.obj W.1.1), ϑ W' (F.res h x) = res h (ϑ W x)) →
          ∃! Ψ : OModulePresheaf.AffHom F G, ∀ (W : ↥B) (x : F.obj W.1.1), e W (Ψ.app W.1 x) = ϑ W x) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.solution

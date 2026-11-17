/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_AffineLimit_locallyOfFiniteType_of_forall_exists_fg_factor. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_AffineLimit_locallyOfFiniteType_of_forall_exists_fg_factor

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.AffineLimit.locallyOfFiniteType_of_forall_exists_fg_factor {R : Type u} [CommRing R] {X : Scheme.{u}}
    (ξ : X ⟶ Spec (CommRingCat.of R))
    (h : ∀ (A : Type u) [CommRing A] [Algebra R A] (φ : Spec (CommRingCat.of A) ⟶ X),
      φ ≫ ξ = Spec.map (CommRingCat.ofHom (algebraMap R A)) →
      ∃ (A₀ : Subalgebra R A) (_ : A₀.FG) (φ₀ : Spec (CommRingCat.of ↥A₀) ⟶ X),
        φ₀ ≫ ξ = Spec.map (CommRingCat.ofHom (algebraMap R ↥A₀)) ∧
        Spec.map (CommRingCat.ofHom A₀.val.toRingHom) ≫ φ₀ = φ) :
    LocallyOfFiniteType ξ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_AffineLimit_locallyOfFiniteType_of_forall_exists_fg_factor.solution

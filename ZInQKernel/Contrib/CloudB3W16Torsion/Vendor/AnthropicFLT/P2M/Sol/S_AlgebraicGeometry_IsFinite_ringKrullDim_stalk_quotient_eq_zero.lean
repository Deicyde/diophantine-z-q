/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_IsFinite_ringKrullDim_stalk_quotient_eq_zero. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_IsFinite_ringKrullDim_stalk_quotient_eq_zero

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace FD0625672e

open scoped TensorProduct

theorem ringKrullDim_quotient_map_maximalIdeal_eq_zero
    (R S : Type*) [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Algebra.QuasiFinite R S] :
    ringKrullDim (S ⧸ (maximalIdeal R).map (algebraMap R S)) = 0 := by

  let e : (maximalIdeal R).Fiber S ≃ₐ[R] S ⧸ (maximalIdeal R).map (algebraMap R S) :=
    (Algebra.TensorProduct.congr (.symm <| .ofBijective _
      (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))) .refl).trans <|
    (Algebra.TensorProduct.comm _ _ _).trans
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot S (maximalIdeal R)).symm.restrictScalars R)

  haveI : IsArtinianRing ((maximalIdeal R).Fiber S) := inferInstance
  haveI hA : IsArtinianRing (S ⧸ (maximalIdeal R).map (algebraMap R S)) := e.surjective.isArtinianRing
  haveI : Ring.KrullDimLE 0 (S ⧸ (maximalIdeal R).map (algebraMap R S)) :=
    (isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.mp hA).2

  haveI : Nontrivial (S ⧸ (maximalIdeal R).map (algebraMap R S)) := by
    rw [Ideal.Quotient.nontrivial_iff]
    -- [port] Mathlib's named properness lemma replaces the former zero-based TFAE lookup.
    exact (IsLocalRing.map_maximalIdeal_lt_top (algebraMap R S)).ne
  exact ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance

end FD0625672e

theorem solution
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsFinite g] [IsLocallyNoetherian Y] (x : X) :
    ringKrullDim ((X.presheaf.stalk x) ⧸
      (maximalIdeal (Y.presheaf.stalk (g.base x))).map (g.stalkMap x).hom) = 0 := by
  letI : Algebra (Y.presheaf.stalk (g.base x)) (X.presheaf.stalk x) := (g.stalkMap x).hom.toAlgebra
  haveI : Algebra.QuasiFinite (Y.presheaf.stalk (g.base x)) (X.presheaf.stalk x) := g.quasiFiniteAt x
  haveI : IsLocalHom (algebraMap (Y.presheaf.stalk (g.base x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (g.stalkMap x).hom)
  exact FD0625672e.ringKrullDim_quotient_map_maximalIdeal_eq_zero (Y.presheaf.stalk (g.base x)) (X.presheaf.stalk x)

#print axioms solution

/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_isRegularLocalRing_localization_atPrime_of_isStandardSmooth. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_Algebra_IsStandardSmooth_exists_isStandardSmoothOfRelativeDimension_of_field
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_isRegularLocalRing_localization_atPrime_mvPolynomial
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_isRegularLocalRing_localization_atPrime_of_etale_of_comap
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_isRegularLocalRing_localization_atPrime_of_isStandardSmooth

set_option autoImplicit false

theorem solution
    (k B : Type*) [Field k] [CommRing B] [Algebra k B]
    [Algebra.IsStandardSmooth k B] (q : Ideal B) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) := by
  classical
  obtain ⟨m, hm⟩ :=
    Algebra.IsStandardSmooth.exists_isStandardSmoothOfRelativeDimension_of_field (k := k) (B := B)
  haveI := hm
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial m k B
  letI : Algebra (MvPolynomial (Fin m) k) B := g.toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin m) k) B := hg
  haveI : IsScalarTower k (MvPolynomial (Fin m) k) B :=
    IsScalarTower.of_algebraMap_eq fun c => (g.commutes c).symm
  have hbase := isRegularLocalRing_localization_atPrime_mvPolynomial k m
    (q.comap (algebraMap (MvPolynomial (Fin m) k) B))
  exact isRegularLocalRing_localization_atPrime_of_etale_of_comap
    (MvPolynomial (Fin m) k) B q hbase

/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_isRegularLocalRing_localization_atPrime_of_isStandardSmooth
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Theorems.Thm_Algebra_IsStandardSmooth_exists_isStandardSmoothOfRelativeDimension_of_field
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Theorems.Thm_isRegularLocalRing_localization_atPrime_mvPolynomial
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Theorems.Thm_isRegularLocalRing_localization_atPrime_of_etale_of_comap
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_isRegularLocalRing_localization_atPrime_of_isStandardSmooth
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

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

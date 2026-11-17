import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_Algebra_FinitePresentation_exists_surjective_aeval_det_pderiv_not_mem_of_basis_residueField.lean
Original Git blob: 36b40addfa3a1b918e6fc41b7a456a48572ef37d
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_Algebra_FinitePresentation_exists_surjective_aeval_det_pderiv_not_mem_of_basis_residueField

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "KaehlerDifferential MvPolynomial TensorProduct"
h77_open "TensorProduct"
open scoped _root_.TensorProduct
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open TensorProduct KaehlerDifferential MvPolynomial

universe u

theorem Algebra.FinitePresentation.exists_surjective_aeval_det_pderiv_not_mem_of_basis_residueField
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S]
    (u : Ideal S) [u.IsPrime]
    {ι : Type} [Finite ι] (w : ι → S)
    (b₀ : Module.Basis ι u.ResidueField (u.ResidueField ⊗[S] Ω[S⁄R]))
    (hb₀ : ∀ i, b₀ i = (1 : u.ResidueField) ⊗ₜ[S] D R S (w i)) :
    ∃ (m : ℕ) (x : Fin m → S) (h : Fin m → MvPolynomial (ι ⊕ Fin m) R),
      Function.Surjective (MvPolynomial.aeval (Sum.elim w x) : MvPolynomial (ι ⊕ Fin m) R →ₐ[R] S) ∧
      (∀ a, MvPolynomial.aeval (Sum.elim w x) (h a) = 0) ∧
      MvPolynomial.aeval (Sum.elim w x)
        (Matrix.det (Matrix.of fun a b : Fin m => MvPolynomial.pderiv (Sum.inr b) (h a))) ∉ u := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_Algebra_FinitePresentation_exists_surjective_aeval_det_pderiv_not_mem_of_basis_residueField.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian

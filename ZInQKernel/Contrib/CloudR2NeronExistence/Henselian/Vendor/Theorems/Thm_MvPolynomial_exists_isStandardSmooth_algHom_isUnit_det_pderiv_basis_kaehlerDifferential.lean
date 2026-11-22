import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_MvPolynomial_exists_isStandardSmooth_algHom_isUnit_det_pderiv_basis_kaehlerDifferential.lean
Original Git blob: 0b44b74f130d591d699d8cc6ae2c96c908b267bd
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_MvPolynomial_exists_isStandardSmooth_algHom_isUnit_det_pderiv_basis_kaehlerDifferential

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "KaehlerDifferential MvPolynomial"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open KaehlerDifferential MvPolynomial

universe u

theorem MvPolynomial.exists_isStandardSmooth_algHom_isUnit_det_pderiv_basis_kaehlerDifferential
    {R : Type u} [CommRing R] {ι : Type} [Finite ι] {m : ℕ} (h : Fin m → MvPolynomial (ι ⊕ Fin m) R) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C) (φ : MvPolynomial (ι ⊕ Fin m) R →ₐ[R] C),
      Algebra.IsStandardSmooth R C ∧
      (∀ a, φ (h a) = 0) ∧
      IsUnit (φ (Matrix.det (Matrix.of fun a b : Fin m => MvPolynomial.pderiv (Sum.inr b) (h a)))) ∧
      (∀ (B : Type u) [CommRing B] [Algebra R B] (ψ : MvPolynomial (ι ⊕ Fin m) R →ₐ[R] B),
          (∀ a, ψ (h a) = 0) →
          IsUnit (ψ (Matrix.det (Matrix.of fun a b : Fin m => MvPolynomial.pderiv (Sum.inr b) (h a)))) →
          ∃ χ : C →ₐ[R] B, χ.comp φ = ψ) ∧
      ∃ b : Module.Basis ι C Ω[C⁄R], ∀ i, b i = D R C (φ (MvPolynomial.X (Sum.inl i))) := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_MvPolynomial_exists_isStandardSmooth_algHom_isUnit_det_pderiv_basis_kaehlerDifferential.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian

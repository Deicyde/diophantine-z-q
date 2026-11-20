import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_AffineDilatation_nonempty_algEquiv_mvPolynomial_sum.lean
Original Git blob: 9a32816a8d39eaf48d93665f88d0098c5df6b676
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_RingTheory_AffineDilatation
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_AffineDilatation_nonempty_algEquiv_mvPolynomial_sum

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem AffineDilatation.nonempty_algEquiv_mvPolynomial_sum
    {R : Type u} [CommRing R] (π : R) (hπ : IsSMulRegular R π) (σ : Type v) (τ : Type v) :
    ∃ e : AffineDilatation.Ring
          (Ideal.span (insert (MvPolynomial.C π) (Set.range fun j : τ => (MvPolynomial.X (Sum.inr j) : MvPolynomial (σ ⊕ τ) R))))
          (MvPolynomial.C π) ≃ₐ[R] MvPolynomial (σ ⊕ τ) R,
      (∀ i : σ, e (algebraMap (MvPolynomial (σ ⊕ τ) R) _ (MvPolynomial.X (Sum.inl i))) = MvPolynomial.X (Sum.inl i)) ∧
      (∀ j : τ, e (AffineDilatation.divElem _ (MvPolynomial.C π) (MvPolynomial.X (Sum.inr j))
          (Ideal.subset_span (Set.mem_insert_of_mem _ ⟨j, rfl⟩))) = MvPolynomial.X (Sum.inr j)) ∧
      (∀ j : τ, e (algebraMap (MvPolynomial (σ ⊕ τ) R) _ (MvPolynomial.X (Sum.inr j))) =
          MvPolynomial.C π * MvPolynomial.X (Sum.inr j)) := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_AffineDilatation_nonempty_algEquiv_mvPolynomial_sum.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian

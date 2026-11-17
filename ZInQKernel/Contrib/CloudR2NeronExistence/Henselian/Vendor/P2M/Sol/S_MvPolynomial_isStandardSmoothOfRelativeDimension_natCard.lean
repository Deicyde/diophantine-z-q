import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_MvPolynomial_isStandardSmoothOfRelativeDimension_natCard.lean
Original Git blob: 2aea2b40ccf77874eb7a2d33d258979eee9440fa
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Explicitly closed 1 scopes originally left open at EOF.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "MvPolynomial"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_MvPolynomial_isStandardSmoothOfRelativeDimension_natCard
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open MvPolynomial

namespace MvPolynomialSmoothEngine
h77_bridge_namespace

variable (S : Type u) [CommRing S] (ι : Type v)

noncomputable def polyGenerators : Algebra.Generators S (MvPolynomial ι S) ι where
  val := X
  σ' := _root_.id
  aeval_val_σ' s := by simp
  algebra := Algebra.id _
  algebraMap_eq := by
    ext p
    · simp
    · simp

theorem polyGenerators_ker : (polyGenerators S ι).ker = ⊥ := by
  rw [Algebra.Generators.ker_eq_ker_aeval_val]
  refine (RingHom.ker_eq_bot_iff_eq_zero _).mpr fun p hp => ?_
  simpa [polyGenerators] using hp

noncomputable def polyPresentation : Algebra.Presentation S (MvPolynomial ι S) ι PEmpty.{1} where
  toGenerators := polyGenerators S ι
  relation := PEmpty.elim
  span_range_relation_eq_ker := by
    rw [polyGenerators_ker]
    simp

noncomputable def polyPreSubmersive :
    Algebra.PreSubmersivePresentation S (MvPolynomial ι S) ι PEmpty.{1} where
  toPresentation := polyPresentation S ι
  map := PEmpty.elim
  map_inj a := a.elim

theorem polyPreSubmersive_jacobian : (polyPreSubmersive S ι).jacobian = 1 := by
  classical
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  have h : (polyPreSubmersive S ι).jacobiMatrix = 1 := Matrix.ext fun i _ => i.elim
  rw [h, Matrix.det_one, map_one]

noncomputable def polySubmersive :
    Algebra.SubmersivePresentation S (MvPolynomial ι S) ι PEmpty.{1} where
  toPreSubmersivePresentation := polyPreSubmersive S ι
  jacobian_isUnit := by rw [polyPreSubmersive_jacobian]; exact isUnit_one

theorem isStandardSmoothOfRelativeDimension_mvPolynomial [Finite ι] :
    Algebra.IsStandardSmoothOfRelativeDimension (Nat.card ι) S (MvPolynomial ι S) :=
  (polySubmersive S ι).isStandardSmoothOfRelativeDimension (by
    simp [Algebra.Presentation.dimension])

theorem isStandardSmoothOfRelativeDimension_mvPolynomial_fin (d : ℕ) :
    Algebra.IsStandardSmoothOfRelativeDimension d S (MvPolynomial (Fin d) S) := by
  simpa using isStandardSmoothOfRelativeDimension_mvPolynomial S (Fin d)

end MvPolynomialSmoothEngine

theorem solution
    (S : Type u) [CommRing S] (ι : Type v) [Finite ι] :
    Algebra.IsStandardSmoothOfRelativeDimension (Nat.card ι) S (MvPolynomial ι S) :=
  MvPolynomialSmoothEngine.isStandardSmoothOfRelativeDimension_mvPolynomial S ι


end P2MW.S_MvPolynomial_isStandardSmoothOfRelativeDimension_natCard
end ZInQ.Contrib.CloudR2NeronExistence.Henselian

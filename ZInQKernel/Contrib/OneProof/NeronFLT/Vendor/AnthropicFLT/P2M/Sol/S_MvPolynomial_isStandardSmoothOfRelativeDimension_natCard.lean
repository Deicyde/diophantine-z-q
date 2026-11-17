/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_MvPolynomial_isStandardSmoothOfRelativeDimension_natCard
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_MvPolynomial_isStandardSmoothOfRelativeDimension_natCard

set_option autoImplicit false

universe u v

open MvPolynomial

namespace MvPolynomialSmoothEngine

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

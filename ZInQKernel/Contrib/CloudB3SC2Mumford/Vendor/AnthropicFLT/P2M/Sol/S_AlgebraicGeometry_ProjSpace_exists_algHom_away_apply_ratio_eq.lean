/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicGeometry_ProjSpace_exists_algHom_away_apply_ratio_eq
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicGeometry_ProjSpace_exists_algHom_away_apply_ratio_eq

set_option autoImplicit false

universe u v

-- [port] was: p2m_open "MvPolynomial HomogeneousLocalization AlgebraicGeometry P2MW.S_AlgebraicGeometry_ProjSpace_exists_algHom_away_apply_ratio_eq.AlgebraicGeometry"
open _root_.MvPolynomial
open _root_.HomogeneousLocalization
open _root_.AlgebraicGeometry
-- [port] `p2m_open` accepts a namespace before it is declared; it is declared (empty) here first
namespace AlgebraicGeometry
end AlgebraicGeometry
open _root_.P2MW.S_AlgebraicGeometry_ProjSpace_exists_algHom_away_apply_ratio_eq.AlgebraicGeometry

namespace AlgebraicGeometry
-- [port] was: p2m_export "AlgebraicGeometry" "ProjSpace.ratio ProjSpace.val_algebraMap"
export _root_.AlgebraicGeometry (ProjSpace.ratio ProjSpace.val_algebraMap)
namespace ProjSpace
-- [port] was: p2m_export "AlgebraicGeometry.ProjSpace" "ratio val_algebraMap map"
export _root_.AlgebraicGeometry.ProjSpace (ratio val_algebraMap map)
namespace ChartLift
-- [port] was: p2m_open "AlgebraicGeometry.ProjSpace AlgebraicGeometry"
open _root_.AlgebraicGeometry.ProjSpace
open _root_.AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (n : ℕ) (i : Fin (n + 1))
  {B : Type v} [CommRing B] [Algebra R B] (b : Fin (n + 1) → B) (hb : b i = 1)

-- [port] local notation `𝒜` removed (build-time syntax); its uses below are expanded to `(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)`

noncomputable def lift0 : Localization.Away (X i : MvPolynomial (Fin (n + 1)) R) →+* B :=
  IsLocalization.Away.lift (X i : MvPolynomial (Fin (n + 1)) R)
    (g := (MvPolynomial.aeval b : MvPolynomial (Fin (n + 1)) R →ₐ[R] B).toRingHom)
    (by simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X, hb]; exact isUnit_one)

theorem lift0_algebraMap (p : MvPolynomial (Fin (n + 1)) R) :
    lift0 R n i b hb (algebraMap _ _ p) = MvPolynomial.aeval b p :=
  IsLocalization.Away.lift_eq _ _ _

noncomputable def liftAway : Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (X i : MvPolynomial (Fin (n + 1)) R) →ₐ[R] B where
  toRingHom := (lift0 R n i b hb).comp (algebraMap (Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (X i : MvPolynomial (Fin (n + 1)) R)) (Localization.Away (X i : MvPolynomial (Fin (n + 1)) R)))
  commutes' r := by
    show lift0 R n i b hb ((algebraMap R (Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (X i : MvPolynomial (Fin (n + 1)) R)) r).val) = algebraMap R B r
    rw [ProjSpace.val_algebraMap, lift0_algebraMap, MvPolynomial.aeval_C]

theorem liftAway_ratio (k : Fin (n + 1)) : liftAway R n i b hb (ProjSpace.ratio R n i k) = b k := by
  show lift0 R n i b hb (ProjSpace.ratio R n i k).val = b k
  rw [ProjSpace.ratio, Away.val_mk, Localization.mk_eq_mk', lift0, IsLocalization.Away.lift, IsLocalization.lift_mk'_spec]

  show MvPolynomial.aeval b (X k) = MvPolynomial.aeval b (X i ^ 1) * b k
  simp [hb]

include hb in
theorem exists_algHom :
    ∃ φ : Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (X i : MvPolynomial (Fin (n + 1)) R) →ₐ[R] B, ∀ k, φ (ProjSpace.ratio R n i k) = b k :=
  ⟨liftAway R n i b hb, liftAway_ratio R n i b hb⟩

end AlgebraicGeometry.ProjSpace.ChartLift

section
attribute [local instance] MvPolynomial.gradedAlgebra
theorem solution
    (R : Type u) [CommRing R] (n : ℕ) (i : Fin (n + 1))
    {B : Type v} [CommRing B] [Algebra R B] (b : Fin (n + 1) → B) (hb : b i = 1) :
    ∃ φ : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) →ₐ[R] B,
      ∀ k, φ (ProjSpace.ratio R n i k) = b k :=
  AlgebraicGeometry.ProjSpace.ChartLift.exists_algHom R n i b hb
end

/-
Copyright (c) 2026 H5/NOS Round-2 lane4 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

H5 closed-section plan GM11 (Step 3), native-power support. SOURCE ONLY, UNCOMPILED.
Native HELD.

Two isomorphisms of NATIVE W07 tensor powers (`AlgebraicGeometry.Scheme.Modules.tensorPow`,
fork `…/Modules/TensorPower.lean` sha256 8930369610ac1a128a42146bcc1fb1f983c2801efa6e9916ed2db05d2f565691),
both built from actual structure maps:

* `pullbackTensorPowIso`: restriction (pullback) commutes with native powers, from the W07
  monoidal structure `pullbackMonoidal : (pullback g).Monoidal`
  (fork `…/Modules/PullbackMonoidal.lean`, sha256 prefix 8fdf855632675eab), via `εIso`/`μIso`.
* `tensorPowMulIso`: `L^{⊗(b*n)} ≅ (L^{⊗b})^{⊗n}`, from W07 `tensorPowAddIso`.

These are NOT a Source/W07 power comparison (that is C5's GM12); only native powers occur.
-/
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.TensorPower
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.PullbackMonoidal

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.ClosedSection

/-- Pullback along any morphism commutes with native W07 tensor powers, via the actual
monoidal structure isomorphisms of `Scheme.Modules.pullback g`. -/
noncomputable def pullbackTensorPowIso {X Y : Scheme.{u}} (g : Y ⟶ X) (L : X.Modules) :
    (n : ℕ) → (Scheme.Modules.pullback g).obj (L.tensorPow n) ≅
      ((Scheme.Modules.pullback g).obj L).tensorPow n
  | 0 => (Functor.Monoidal.εIso (Scheme.Modules.pullback g)).symm
  | n + 1 => (Functor.Monoidal.μIso (Scheme.Modules.pullback g) L (L.tensorPow n)).symm ≪≫
      (Iso.refl _ ⊗ᵢ pullbackTensorPowIso g L n)

/-- `L^{⊗(b*n)} ≅ (L^{⊗b})^{⊗n}` for native W07 powers, from the actual `tensorPowAddIso`. -/
noncomputable def tensorPowMulIso {X : Scheme.{u}} (L : X.Modules) (b : ℕ) :
    (n : ℕ) → L.tensorPow (b * n) ≅ (L.tensorPow b).tensorPow n
  | 0 => eqToIso (congrArg L.tensorPow (Nat.mul_zero b))
  | n + 1 => eqToIso (congrArg L.tensorPow (by ring : b * (n + 1) = b + b * n)) ≪≫
      L.tensorPowAddIso b (b * n) ≪≫ (Iso.refl _ ⊗ᵢ tensorPowMulIso L b n)

end ZInQ.Contrib.CloudR2NOS.ClosedSection

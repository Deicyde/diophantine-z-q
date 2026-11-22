/-
Copyright (c) 2026 H5/NOS Round-2 lane4 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

H5 closed-section GM11 (Step 3): I2 ⇒ I3 with (G1), (G4), (G5), (G6), (G7) PROVED.
SOURCE ONLY, UNCOMPILED. Native HELD.
Remaining explicit hypotheses: (G2) `FiniteBySectionsNativePow`, (G3) `UniformizerSequence`
(both true; sketches in the closed-section truth precheck).
NEW EDITION (lane C4, 2026-11-17; `FiniteBySections (R := …)` drift sweep after a Parent compile probe). DISCLOSED INTERNAL STATEMENT REPAIR in `hI2`,
the same accepted form as Step3Assembly ed2 / Step3AssemblyG7 / Step3AssemblyProved (Parent did not veto): `(R := k)` (no such parameter
in the pinned W03 `FiniteBySections`) is replaced by a type ascription of the SAME morphism `Hs.X.hom` into `Spec (CommRingCat.of k)`.
The whole `hI2` binder is byte-identical to the Step3Assembly family's; no premise added or weakened.
-/
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.Step3AssemblyG1
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.QuasiFiniteFibre

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.ClosedSection

local notation "FBS" => ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.FiniteBySections

/-- **Step 3 on the SAME stage, with (G1), (G4), (G5), (G6), (G7) proved.** -/
theorem step3_I3_of_G2_G3
    (hG2 : FiniteBySectionsNativePow.{u}) (hG3 : UniformizerSequence.{u})
    {C : Type u} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    (H : Grp (Over (Spec (CommRingCat.of C)))) [PkgI2.IsAbelianScheme H]
    (M : H.X.left.Modules) [M.IsInvertible]
    (hI2 :
      let s := IsLocalRing.closedPoint C
      let k : Type u := (Spec (CommRingCat.of C)).residueField s
      let g := (Spec (CommRingCat.of C)).fromSpecResidueField s
      let Hs := (Over.pullback g).mapGrp.obj H
      let Ms := (Scheme.Modules.pullback (H.X.hom.fiberι s)).obj M
      ∃ b : ℕ, 0 < b ∧ FBS (Ms.tensorPow b)
        (Hs.X.hom : _ ⟶ Spec (CommRingCat.of ↥((Spec (CommRingCat.of C)).residueField s)))) :
    ∃ a : ℕ, 0 < a ∧ FBS (M.tensorPow a) H.X.hom :=
  step3_I3_of_G2_G3_G6 hG2 hG3 QuasiFiniteFibre.quasiFiniteOnClosedFibre H M hI2

end ZInQ.Contrib.CloudR2NOS.ClosedSection

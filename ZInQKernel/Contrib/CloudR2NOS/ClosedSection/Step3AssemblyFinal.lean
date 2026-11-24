/-
Copyright (c) 2026 H5/NOS Round-2 lane4 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

H5 closed-section GM11 (Step 3): I2 ⇒ I3 with ALL sub-gaps (G1)–(G7) PROVED.
SOURCE ONLY, UNCOMPILED. Native HELD. No hypothesis beyond the stage data and I2.
NEW EDITION (lane C4, 2026-11-17; `FiniteBySections (R := …)` drift sweep after a Parent compile probe). DISCLOSED INTERNAL STATEMENT REPAIR in `hI2`,
the same accepted form as Step3Assembly ed2 / Step3AssemblyG7 / Step3AssemblyProved (Parent did not veto): `(R := k)` (no such parameter
in the pinned W03 `FiniteBySections`) is replaced by a type ascription of the SAME morphism `Hs.X.hom` into `Spec (CommRingCat.of k)`.
The whole `hI2` binder is byte-identical to the Step3Assembly family's; no premise added or weakened.
-/
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.Step3AssemblyG2
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.UniformizerSES

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.ClosedSection

local notation "FBS" => ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.FiniteBySections

/-- **Step 3 (I2 ⇒ I3) on the SAME constructed `C/H/M`, unconditional at Source level:** a
positive native power of the closed-fibre restriction finite-by-sections over the residue field
gives a positive native power of `M` finite-by-sections over the DVR `C`. -/
theorem step3_I3_unconditional
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
  step3_I3_of_G3 UniformizerSES.uniformizerSequence H M hI2

end ZInQ.Contrib.CloudR2NOS.ClosedSection

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 97a5b23586f9, module
-- TauCeti.NumberTheory.NumberField.Global.Ideles.Ray.OpenSubgroup), Apache-2.0: declarations added to that module after commit 5a01f5fe, whose
-- version is vendored as `ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.Ideles.Ray.OpenSubgroup`.
module

public import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.Ideles.Ray.OpenSubgroup
public import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.Ideles.Ray.Subgroup
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.Places.Connected
import ZInQKernel.Contrib.TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Basic
import ZInQKernel.Contrib.TauCeti.Topology.Algebra.Group.Connected
import ZInQKernel.Contrib.TauCeti.Topology.Algebra.Group.Units

public section
noncomputable section

namespace OpenSubgroup

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Filter Topology
open scoped NumberField NumberField.AdeleRing WithZero
open TauCeti.GlobalNumberFields
variable {K : Type*} [Field K] [NumberField K]

/-- **The conductor of an open subgroup of the idele class group**: the least modulus whose ray
subgroup lies in `U`. Every modulus whose ray subgroup lies in `U` is a multiple of it
(`ideleClassConductor_dvd_iff`). -/
def ideleClassConductor (U : OpenSubgroup (IdeleClassGroup (𝓞 K) K)) : Modulus K :=
  Modulus.wellFounded_dvd_and_ne.min {𝔪 | raySubgroup 𝔪 ≤ U.toSubgroup}
    (exists_raySubgroup_le_of_isOpen U.toSubgroup U.isOpen)

end OpenSubgroup

namespace OpenSubgroup

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Filter Topology
open scoped NumberField NumberField.AdeleRing WithZero
open TauCeti.GlobalNumberFields
variable {K : Type*} [Field K] [NumberField K]

/-- The ray subgroup of the conductor of `U` lies in `U`. -/
theorem raySubgroup_ideleClassConductor_le (U : OpenSubgroup (IdeleClassGroup (𝓞 K) K)) :
    raySubgroup U.ideleClassConductor ≤ U :=
  Modulus.wellFounded_dvd_and_ne.min_mem {𝔪 | raySubgroup 𝔪 ≤ U.toSubgroup}
    (exists_raySubgroup_le_of_isOpen U.toSubgroup U.isOpen)

end OpenSubgroup

namespace OpenSubgroup

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Filter Topology
open scoped NumberField NumberField.AdeleRing WithZero
open TauCeti.GlobalNumberFields
variable {K : Type*} [Field K] [NumberField K]

/-- **The universal property of the conductor**: the conductor of `U` divides `𝔪` exactly when the
ray subgroup of `𝔪` lies in `U`. -/
theorem ideleClassConductor_dvd_iff {U : OpenSubgroup (IdeleClassGroup (𝓞 K) K)}
    {𝔪 : Modulus K} : U.ideleClassConductor ∣ 𝔪 ↔ raySubgroup 𝔪 ≤ U := by
  refine ⟨fun h ↦ (raySubgroup_antitone h).trans (raySubgroup_ideleClassConductor_le U),
    fun h ↦ ?_⟩
  -- The greatest common divisor of the conductor and `𝔪` again has its ray subgroup in `U`, so by
  -- minimality it is the conductor.
  have hgcd : raySubgroup (U.ideleClassConductor.gcd 𝔪) ≤ U := by
    rw [raySubgroup_gcd]
    exact sup_le (raySubgroup_ideleClassConductor_le U) h
  have hmin := Modulus.wellFounded_dvd_and_ne.not_lt_min {𝔪 | raySubgroup 𝔪 ≤ U.toSubgroup} hgcd
  have heq : U.ideleClassConductor.gcd 𝔪 = U.ideleClassConductor :=
    not_not.mp fun hne ↦ hmin ⟨Modulus.gcd_dvd_left _ _, hne⟩
  exact heq ▸ Modulus.gcd_dvd_right _ _

end OpenSubgroup

end
end

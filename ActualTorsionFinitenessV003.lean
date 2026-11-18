import ActualFiniteLevelActionV003
import ZInQKernel.Contrib.AbVarBC.Points
import ZInQKernel.Contrib.CloudB3W16Torsion.NativeBridges

/-!
# Finiteness of all original geometric torsion points

The proved native multiplication-étale theorem makes multiplication
finite. The original torsion points inject into its finite geometric
fibre. Base change transports this result to the original point group.
No point-set finiteness or field-of-definition hypothesis is supplied.
-/

noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry MonObj

namespace ActualTorsionFiniteness
open ActualFiniteLevel
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

lemma finite_original_torsion [IsAlgClosed Ω] (A : PkgI3.AbVar K) (m : ℕ)
    (hm : (m : Ω) ≠ 0) : Finite (torsionSubgroup A Ω m) := by
  let B := A.baseChange Ω
  let G := ObjBridge.toGrp B
  haveI : PkgI2.IsAbelianVariety G := inferInstance
  haveI : Finite (PkgI2.torsion G Ω m) :=
    ZInQ.Contrib.CloudB3W16Torsion.finite_torsion G m hm
  let e : B.Pt Ω ≃* A.Pt Ω := ZInQ.Contrib.AbVarBC.bcPt (L := Ω) A Ω
  let f : torsionSubgroup A Ω m → PkgI2.torsion G Ω m := fun x =>
    ⟨e.symm x.1, by
      change e.symm x.1 ^ m = 1
      rw [← map_pow]
      exact (congrArg e.symm x.2).trans (map_one _)⟩
  apply Finite.of_injective f
  intro x y h
  apply Subtype.ext
  apply e.symm.injective
  exact congrArg Subtype.val h

lemma finite_prime_power_torsion [CharZero K] [IsAlgClosure K Ω]
    (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) :
    Finite (torsionSubgroup A Ω (ℓ ^ n)) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  apply finite_original_torsion
  have h : ((ℓ ^ n : ℕ) : K) ≠ 0 := by
    rw [Nat.cast_pow]
    exact pow_ne_zero n (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero)
  simpa only [map_natCast] using (map_ne_zero (algebraMap K Ω)).mpr h

end ActualTorsionFiniteness

import ZInQKernel.Contrib.CloudB3RC53.Duality.LocalKummer

/-!
# The actual degree-zero torsion is the rational fixed torsion

The finite Kummer condition retains B(F)[n] in degree zero. Its canonical
coefficient inclusion identifies this group with H⁰(F,B[n]). The result below
uses the actual Galois action on the actual coefficient module, not a count of
abstract groups. It explains the degree-zero identification needed when the
local quotient cone is identified with its degree-one and degree-two groups.
-/

noncomputable section

namespace ZInQ.Contrib.RC53Assist.DerivedKummer.DegreeZero

open TauCeti TauCeti.ContCohomology

variable {F : Type} [Field F] [DecidableEq F] (B : WeierstrassCurve F)

/-- The actual rational torsion inclusion, restricted to the Galois invariants. -/
def torsionToH0 (n : ℕ) : AddSubgroup.torsionBy B.toAffine.Point n →+
    H0 (AbsoluteGaloisGroup F) (B.TorsionCoeff n) :=
  (B.baseTorsionCoeff n).codRestrict _ (fun t =>
    (FixedPoints.mem_addSubgroup _ _ _).2 (fun σ => B.smul_baseTorsionCoeff σ t))

/-- Rational n-torsion is exactly the invariant part of the actual n-torsion
coefficient module. No local-duality print is used in this identification. -/
theorem torsionToH0_bijective (n : ℕ) : Function.Bijective (torsionToH0 B n) := by
  constructor
  · intro t u h
    exact B.baseTorsionCoeff_injective n (congrArg Subtype.val h)
  · rintro ⟨q, hq⟩
    obtain ⟨t, ht⟩ := B.exists_baseTorsionCoeff_eq_of_forall_smul_eq
      ((FixedPoints.mem_addSubgroup _ _ _).1 hq)
    exact ⟨t, Subtype.ext ht⟩

/-- The canonical degree-zero identification. -/
def torsionH0Equiv (n : ℕ) : AddSubgroup.torsionBy B.toAffine.Point n ≃+
    H0 (AbsoluteGaloisGroup F) (B.TorsionCoeff n) :=
  AddEquiv.ofBijective (torsionToH0 B n) (torsionToH0_bijective B n)

/-- The identification is the actual coefficient inclusion on every torsion
point, so it supplies the map as well as its abstract group type. -/
theorem torsionH0Equiv_apply (n : ℕ) (t : AddSubgroup.torsionBy B.toAffine.Point n) :
    (torsionH0Equiv B n t : B.TorsionCoeff n) = B.baseTorsionCoeff n t := rfl

/-- On actual points in the separable closure, the identification is the
base-field point map. -/
theorem torsionH0Equiv_point_apply (n : ℕ) (t : AddSubgroup.torsionBy B.toAffine.Point n) :
    ((torsionH0Equiv B n t : B.TorsionCoeff n) : B.PointCoeff) = B.basePointCoeff t := rfl

end ZInQ.Contrib.RC53Assist.DerivedKummer.DegreeZero

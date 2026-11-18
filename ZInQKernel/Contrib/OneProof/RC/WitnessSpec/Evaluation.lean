import ZInQKernel.Contrib.OneProof.RC.Stages.Witness

/-! The finite specialization formula (tex 8392–8398), with the local geometry
separated from the exact Kummer calculation. -/

noncomputable section

open scoped WeierstrassCurve
open WeierstrassCurve TauCeti ZInQ.Manuscript.RC.PrintsArith
  ZInQ.Manuscript.RC.Stages

namespace ZInQ.Manuscript.RC.WitnessSpec

section Evaluation

variable {X Y H : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup H]
  (n : ℕ) (red : X →+ Y)

local notation "Xₙ" => AddSubgroup.torsionBy X (n : ℤ)
local notation "Yₙ" => AddSubgroup.torsionBy Y (n : ℤ)

/-- Restrict an additive specialization map to the finite torsion. -/
def torsionMap : Xₙ →+ Yₙ :=
  (red.comp (AddSubgroup.subtype Xₙ)).codRestrict Yₙ fun t => by
    apply AddSubgroup.torsionBy.nsmul_iff.mpr
    change n • red t.val = 0
    rw [← map_nsmul, AddSubgroup.torsionBy.nsmul_iff.mp t.property, map_zero]

/-- Prime-to-characteristic injectivity and the matching two torsion counts suffice
to identify the finite torsion. This does not require surjectivity on all points. -/
theorem torsionMap_bijective [Finite Yₙ] (hinj : Set.InjOn red Xₙ)
    (hcard : Nat.card Xₙ = Nat.card Yₙ) : Function.Bijective (torsionMap n red) := by
  have hi : Function.Injective (torsionMap n red) :=
    fun x y h => Subtype.ext (hinj x.property y.property (congrArg Subtype.val h))
  exact (Nat.bijective_iff_injective_and_card (torsionMap n red)).mpr ⟨hi, hcard⟩

variable (g : X →+ X) (F : Y →+ Y)
  (hred : ∀ x, red (g x) = F (red x))
  (hsq : ∀ t : X, n • t = 0 → g (g t) = t)
  (hbij : Function.Bijective (torsionMap n red))

include hred hsq hbij in
/-- Squared Frobenius fixes all geometric residue torsion after transporting the
corresponding global fact by the specialization isomorphism. -/
theorem frob_sq_on_reduced_torsion : ∀ t : Y, n • t = 0 → F (F t) = t := by
  intro t ht
  obtain ⟨u, hu⟩ := hbij.2 ⟨t, AddSubgroup.torsionBy.nsmul_iff.mpr ht⟩
  have he : red u.val = t := congrArg Subtype.val hu
  rw [← he, ← hred, ← hred, hsq _ (AddSubgroup.torsionBy.nsmul_iff.mp u.property)]

variable (hdiv : Function.Surjective (fun R : Y => n • R))

/-- The actual recipe for the evaluation: specialize to quadratic fixed points, apply
the finite Kummer homomorphism, then read the global row via inverse torsion reduction. -/
def stageMap (n : ℕ) (red : X →+ Y) (g : X →+ X) (F : Y →+ Y)
    (hred : ∀ x, red (g x) = F (red x))
    (hsq : ∀ t : X, n • t = 0 → g (g t) = t)
    (hbij : Function.Bijective (torsionMap n red))
    (hdiv : Function.Surjective (fun R : Y => n • R))
    (row : AddSubgroup.torsionBy X (n : ℤ) →+ H)
    {G : Type*} [AddCommGroup G] (r : G →+ FixedSq F) : G →+ H := by
  let e : AddSubgroup.torsionBy X (n : ℤ) ≃+ AddSubgroup.torsionBy Y (n : ℤ) :=
    AddEquiv.ofBijective (torsionMap n red) hbij
  let k := kappa F n hdiv (frob_sq_on_reduced_torsion n red g F hred hsq hbij)
  exact row.comp (e.symm.toAddMonoidHom.comp (k.comp r))

/-- The integer coefficient of the cocycle is unchanged in the finite ring: no sign
or unit factor appears on this choice of arithmetic Frobenius. -/
theorem stageMap_apply_division (readRow : Xₙ →+ H) {G : Type*} [AddCommGroup G] (r : G →+ FixedSq F)
    (P : G) (Q R : X) (hR : n • R = Q) (hP : red Q = (r P).val)
    (t : Xₙ) (ht : t.val = g (g R) - R) :
    stageMap (X := X) (Y := Y) (H := H) (G := G) n red g F hred hsq hbij hdiv readRow r P = readRow t := by
  have hκ : kappa F n hdiv (frob_sq_on_reduced_torsion n red g F hred hsq hbij) (r P) =
      torsionMap n red t := by
    apply Subtype.ext
    change (kappa F n hdiv _ (r P)).val = red t.val
    rw [ht]
    exact kappa_of_specialization red g F n hdiv
      (frob_sq_on_reduced_torsion n red g F hred hsq hbij) Q R hR (r P) hP
      ((hred (g R)).trans (congrArg F (hred R)))
  simp only [stageMap, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, hκ]
  exact congrArg readRow ((AddEquiv.ofBijective (torsionMap n red) hbij).symm_apply_apply t)

#print axioms torsionMap
#print axioms torsionMap_bijective
#print axioms frob_sq_on_reduced_torsion
#print axioms stageMap
#print axioms stageMap_apply_division

end Evaluation

end ZInQ.Manuscript.RC.WitnessSpec

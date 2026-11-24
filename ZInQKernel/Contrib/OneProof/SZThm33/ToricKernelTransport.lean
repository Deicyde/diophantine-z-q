import ZInQKernel.Contrib.OneProof.SZThm33.ToricSchemeCoordinates
import ZInQKernel.Contrib.OneProof.ChevalleyFree
import ZInQKernel.Contrib.OneProof.FaltingsDVR.EtalePower
import ZInQKernel.Contrib.OneProof.SZThm33.PullbackTate

/-! Transport of a split torus kernel across two algebra structures on a
commutative ring. -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ.HeightSplit ZInQ.ChevFree DictModels.RaynaudOr SmoothGroup

set_option linter.style.haveILetI false
set_option maxHeartbeats 1700000
set_option synthInstance.maxHeartbeats 160000
set_option backward.isDefEq.respectTransparency false

namespace SZRaynaud

variable {k : Type} [Field k] {U : Over (Spec (.of k))} [GrpObj U]
  {B' : PkgI3.AbVar (AlgebraicClosure k)}

local instance : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj

variable (π : ((Over.pullback (sφ (φbar k))).obj U) ⟶ B'.X) [IsMonHom π] (r : ℕ)
  (e : ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R], (Fin r → Rˣ) →* (algPt (AlgebraicClosure k) R ⟶ ((Over.pullback (sφ (φbar k))).obj U)))

private abbrev specRingMap {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) :
    Spec (.of S) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom f)

private theorem toricOverCondition {R : Type} [CommRing R]
    (ra rb : (AlgebraicClosure k) →+* R) (hab : ra.comp (φbar k) = rb.comp (φbar k)) :
    specRingMap ra ≫ (sφ (φbar k)) = specRingMap rb ≫ (sφ (φbar k)) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hab]

/-- Evaluate the torus with the first structure map, then regard its
underlying U-point over the second structure map before applying the quotient. -/
def torusTransport (R : Type) [CommRing R] (ra rb : (AlgebraicClosure k) →+* R)
    (hab : ra.comp (φbar k) = rb.comp (φbar k)) :
    (Fin r → Rˣ) →* (Over.mk (specRingMap rb) ⟶ B'.X) :=
  letI : Algebra (AlgebraicClosure k) R := ra.toAlgebra
  let ea := pullbackTestPointEquiv (sφ (φbar k)) (specRingMap ra) (specRingMap rb ≫ (sφ (φbar k))) (toricOverCondition ra rb hab) U
  let eb := pullbackTestPointEquiv (sφ (φbar k)) (specRingMap rb) (specRingMap rb ≫ (sφ (φbar k))) rfl U
  (IsMonHom.monoidHom π _).comp
    (eb.toMonoidHom.comp (ea.symm.toMonoidHom.comp (e R)))

theorem torusTransport_left (R : Type) [CommRing R] (ra rb : (AlgebraicClosure k) →+* R)
    (hab : ra.comp (φbar k) = rb.comp (φbar k)) (t : Fin r → Rˣ) :
    letI : Algebra (AlgebraicClosure k) R := ra.toAlgebra
    (torusTransport π r e R ra rb hab t).left =
      pullback.lift ((e R t).left ≫ pullback.fst U.hom (sφ (φbar k))) (specRingMap rb)
        (by
          rw [Category.assoc, pullback.condition, ← Category.assoc]
          have h := Over.w (e R t)
          change (e R t).left ≫ pullback.snd U.hom (sφ (φbar k)) = specRingMap ra at h
          rw [h]
          exact toricOverCondition ra rb hab) ≫ π.left := by
  letI : Algebra (AlgebraicClosure k) R := ra.toAlgebra
  let ea := pullbackTestPointEquiv (sφ (φbar k)) (specRingMap ra) (specRingMap rb ≫ (sφ (φbar k))) (toricOverCondition ra rb hab) U
  let eb := pullbackTestPointEquiv (sφ (φbar k)) (specRingMap rb) (specRingMap rb ≫ (sφ (φbar k))) rfl U
  let z := ea.symm (e R t)
  change (eb z).left ≫ π.left = _
  congr 1
  apply pullback.hom_ext
  · rw [pullback.lift_fst]
    exact (pullbackTestPointEquiv_fst (sφ (φbar k)) (specRingMap rb) (specRingMap rb ≫ (sφ (φbar k))) rfl U z).trans
      (by simpa only [ea, z, MulEquiv.apply_symm_apply] using
        (pullbackTestPointEquiv_fst (sφ (φbar k)) (specRingMap ra) (specRingMap rb ≫ (sφ (φbar k))) (toricOverCondition ra rb hab) U z).symm)
  · rw [pullback.lift_snd]
    exact Over.w (eb z)

private theorem torusTransport_one (R : Type) [CommRing R] (ra rb : (AlgebraicClosure k) →+* R)
    (hab : ra.comp (φbar k) = rb.comp (φbar k)) :
    (torusTransport π r e R ra rb hab 1).left =
      specRingMap rb ≫ (η[B'.X] : 𝟙_ _ ⟶ B'.X).left := by
  rw [map_one]
  rfl

/-- Naturality of toric transport under arbitrary ring maps of the test
rings. -/
theorem torusTransport_natural_left
    (he_nat : ∀ (R S : Type) [CommRing R] [Algebra (AlgebraicClosure k) R] [CommRing S] [Algebra (AlgebraicClosure k) S]
      (f : R →ₐ[(AlgebraicClosure k)] S) (t : Fin r → Rˣ),
      e S (fun i => Units.map (f : R →* S) (t i)) = algPtMap f ≫ e R t)
    {R S : Type} [CommRing R] [CommRing S] (a : R →+* S)
    (ra rb : (AlgebraicClosure k) →+* R) (hab : ra.comp (φbar k) = rb.comp (φbar k)) (t : Fin r → Rˣ)
    (ha : (a.comp ra).comp (φbar k) = (a.comp rb).comp (φbar k)) :
    specRingMap a ≫ (torusTransport π r e R ra rb hab t).left =
      (torusTransport π r e S (a.comp ra) (a.comp rb) ha (fun i => Units.map a (t i))).left := by
  rw [torusTransport_left, torusTransport_left, ← Category.assoc]
  congr 1
  letI : Algebra (AlgebraicClosure k) R := ra.toAlgebra
  letI : Algebra (AlgebraicClosure k) S := (a.comp ra).toAlgebra
  let f : R →ₐ[(AlgebraicClosure k)] S := ⟨a, fun _ => rfl⟩
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst]
    have hh := congrArg (fun p => p.left) (he_nat R S f t)
    change (e S (fun i => Units.map a (t i))).left = specRingMap a ≫ (e R t).left at hh
    rw [hh, Category.assoc]
  · simp only [Category.assoc, pullback.lift_snd]
    exact (Spec.map_comp ..).symm

#print axioms torusTransport_natural_left

end SZRaynaud

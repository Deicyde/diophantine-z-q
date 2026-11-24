import ZInQKernel.Contrib.OneProof.FaltingsDVR.FaltingsCyclicClosure
import ZInQKernel.Contrib.OneProof.SemiAbelianDescendsPerfect
import ZInQKernel.Contrib.OneProof.MilneQuasiInverse.Kernel
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! Prime-to-characteristic torsion detects a nontrivial rational kernel on a split torus. -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ.HeightSplit ZInQ.SemiAbDescend ZInQ.Contrib.MilneQuasiInverse.Kernel
open scoped BigOperators

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 120000

namespace ZInQ.FaltingsRestate

variable {k : Type} [Field k] [IsAlgClosed k] {r : ℕ}

private theorem eval_torus_polynomial (x : Fin r → kˣ) (P : MvPolynomial (Fin r) k) :
    torusLift x (algebraMap (MvPolynomial (Fin r) k) (TorusRing k r) P) =
      MvPolynomial.eval (fun i => (x i : k)) P := by
  change (IsLocalization.liftAlgHom _ : TorusRing k r →ₐ[k] k) _ = _
  rw [IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  change MvPolynomial.aeval (fun i => (x i : k)) P = _
  rw [MvPolynomial.aeval_eq_eval₂Hom, Algebra.algebraMap_self]
  rfl

private theorem torus_lift_vanishing_iff (I : Ideal (TorusRing k r)) (x : Fin r → kˣ) :
    (∀ q ∈ I, torusLift x q = 0) ↔
      ∀ P ∈ I.comap (algebraMap (MvPolynomial (Fin r) k) (TorusRing k r)),
        MvPolynomial.eval (fun i => (x i : k)) P = 0 := by
  constructor
  · intro h P hp
    rw [← eval_torus_polynomial]
    exact h _ hp
  · intro h q hq
    let p : MvPolynomial (Fin r) k := ∏ i, MvPolynomial.X i
    obtain ⟨⟨a, d⟩, hd⟩ := IsLocalization.surj (Submonoid.powers p) q
    have hdI : (algebraMap (MvPolynomial (Fin r) k) (TorusRing k r)) a ∈ I := by
      rw [← hd]
      exact I.mul_mem_right _ hq
    have hEq := congrArg (torusLift x) hd
    change torusLift x (q * algebraMap (MvPolynomial (Fin r) k) (TorusRing k r) d) =
      torusLift x (algebraMap (MvPolynomial (Fin r) k) (TorusRing k r) a) at hEq
    rw [map_mul, eval_torus_polynomial x a, h a hdI] at hEq
    have hunit : IsUnit (torusLift x (algebraMap (MvPolynomial (Fin r) k) (TorusRing k r) d)) :=
      (IsLocalization.map_units (TorusRing k r) d).map (torusLift x).toMonoidHom
    exact (mul_eq_zero.mp hEq).resolve_right hunit.ne_zero

set_option backward.isDefEq.respectTransparency false in
/-- A polynomial family of points parametrized by a split torus has no
nontrivial rational kernel if its kernel has no prime-to-characteristic torsion. -/
theorem torus_parameter_kernel_rational_trivial
    {G : Over (Spec (CommRingCat.of k))} [GrpObj G] [LocallyOfFiniteType G.hom]
    (E : (Fin r → kˣ) →* (algPt k k ⟶ G))
    (u : algPt k (TorusRing k r) ⟶ G)
    (hp : ∀ t, algPtMap (torusLift t) ≫ u = E t)
    (h : ∀ (m : ℕ), (m : k) ≠ 0 →
      ∀ t, E t = 1 → t ^ m = 1 → t = 1)
    (x : Fin r → kˣ) (hx : E x = 1) : x = 1 := by
  classical
  let R := TorusRing k r
  let H := E.ker
  let unitMap := (1 : algPt k k ⟶ G)
  let y := unitMap.left (IsLocalRing.closedPoint k)
  have hbase : (algPt k k).hom = 𝟙 _ := by simp [algPt]
  have hunitMap : unitMap.left ≫ G.hom = 𝟙 _ := (Over.w unitMap).trans hbase
  haveI : Subsingleton (algPt k k).left := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  haveI : IsClosedImmersion unitMap.left := isClosedImmersion_of_comp_eq_id _ _ hunitMap
  have hy : IsClosed ({y} : Set G.left) := by
    have hc := unitMap.left.isClosedEmbedding.isClosed_range
    rwa [Set.range_eq_singleton (fun a => congrArg unitMap.left (Subsingleton.elim (α := PrimeSpectrum k) a (IsLocalRing.closedPoint k)))] at hc
  let Q : Set (PrimeSpectrum R) := u.left ⁻¹' {y}
  have hQ : IsClosed Q := hy.preimage u.left.continuous
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal Q).mp hQ
  let p (t : Fin r → kˣ) := Spec.map (CommRingCat.ofHom ((torusLift (K := k) t).toRingHom))
  have hQmem (t : Fin r → kˣ) :
      t ∈ H ↔ p t (IsLocalRing.closedPoint k) ∈ Q := by
    have heval : (E t).left (IsLocalRing.closedPoint k) =
        u.left (p t (IsLocalRing.closedPoint k)) := by
      rw [← hp]
      rfl
    change E t = unitMap ↔ u.left (p t (IsLocalRing.closedPoint k)) = y
    rw [← heval]
    constructor
    · intro hh
      exact congrArg (fun q : algPt k k ⟶ G => q.left (IsLocalRing.closedPoint k)) hh
    · intro hh
      apply Over.OverMorphism.ext
      exact ext_of_apply_closedPoint_eq G.hom ((Over.w _).trans hbase) hunitMap hh
  let polys : Set (MvPolynomial (Fin r) k) :=
    (I.comap (algebraMap (MvPolynomial (Fin r) k) R) : Set (MvPolynomial (Fin r) k))
  have hE (t : Fin r → kˣ) : t ∈ H ↔
      ∀ P ∈ polys, MvPolynomial.eval (fun i => (t i : k)) P = 0 := by
    refine (hQmem t).trans ?_
    rw [hI]
    refine Iff.trans ?_ (torus_lift_vanishing_iff I t)
    change (I : Set R) ⊆ ((p t (IsLocalRing.closedPoint k)).asIdeal : Set R) ↔ _
    have hzero : (IsLocalRing.closedPoint k).asIdeal = ⊥ :=
      (Ideal.eq_bot_or_top _).resolve_right (IsLocalRing.closedPoint k).isPrime.ne_top
    change (∀ q ∈ I, torusLift t q ∈ (IsLocalRing.closedPoint k).asIdeal) ↔ _
    rw [hzero]
    simp only [Ideal.mem_bot]
    rfl
  exact eq_one_of_polynomial_torus_subgroup_no_torsion H polys hE h x hx

end ZInQ.FaltingsRestate

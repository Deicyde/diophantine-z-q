import ZInQKernel.Contrib.OneProof.TateQuotientImage
import ZInQKernel.Contrib.CloudR2Poincare.L4.StabilizerScheme
import Mathlib.FieldTheory.Normal.Basic

/-! # The reduced support of a finite Galois-stable set of geometric points -/

noncomputable section
open CategoryTheory AlgebraicGeometry PkgI3.AbVar
open scoped CategoryTheory.MonObj

namespace ZInQ.Contrib.TateFiniteApproximation

variable {K : Type} [Field K]
abbrev GeomPt (X : Over (Spec (.of K))) := ptObj (K := K) (AlgebraicClosure K) ⟶ X

/-- The image point of a geometric point over the ground field. -/
def supportPoint {X : Over (Spec (.of K))} (P : GeomPt X) : X.left :=
  P.left (IsLocalRing.closedPoint (AlgebraicClosure K))

theorem isClosed_supportPoint {X : Over (Spec (.of K))} [IsSeparated X.hom] (P : GeomPt X) :
    IsClosed {supportPoint P} := by
  have : IsIntegralHom ((ptObj (K := K) (AlgebraicClosure K)).hom) := by
    apply IsIntegralHom.SpecMap_iff.mpr
    exact Algebra.IsIntegral.isIntegral
  have : UniversallyClosed (P.left ≫ X.hom) := by rw [Over.w]; infer_instance
  have : UniversallyClosed P.left := UniversallyClosed.of_comp_of_isSeparated P.left X.hom
  let : Nonempty (ptObj (K := K) (AlgebraicClosure K)).left := ⟨IsLocalRing.closedPoint _⟩
  let : Subsingleton (ptObj (K := K) (AlgebraicClosure K)).left :=
    inferInstanceAs (Subsingleton (PrimeSpectrum (AlgebraicClosure K)))
  have he : Set.range P.left = {supportPoint P} := by
    apply Set.range_eq_singleton
    exact fun x => congrArg P.left (Subsingleton.elim x _)
  exact he ▸ P.left.isClosedMap.isClosed_range

private theorem embeddings_conjugate {L : Type} [Field L] [Algebra K L]
    (a b : L →ₐ[K] AlgebraicClosure K) :
    ∃ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, ∀ x, σ (a x) = b x := by
  let e := a.equivFieldRange.symm.trans b.equivFieldRange
  refine ⟨e.liftNormal (AlgebraicClosure K), fun x => ?_⟩
  exact (e.liftNormal_commutes (AlgebraicClosure K) (a.equivFieldRange x)).trans
    (by simp [e])

/-- Two geometric points have the same support over K exactly when they are
conjugate under the absolute Galois group. -/
theorem supportPoint_eq_iff {X : Over (Spec (.of K))} (P Q : GeomPt X) :
    supportPoint P = supportPoint Q ↔
      ∃ σ : Field.absoluteGaloisGroup K, galHom σ ≫ P = Q := by
  constructor
  · intro he
    let x := supportPoint Q
    let i := X.left.fromSpecResidueField x
    let a := Spec.preimage (i ≫ X.hom)
    let : Algebra K (X.left.residueField x) := a.hom.toAlgebra
    have factor (P : GeomPt X) (h : supportPoint P = x) :
        ∃ ψ : X.left.residueField x →ₐ[K] AlgebraicClosure K,
        P.left = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ i := by
      have trans (z : X.left) (hz : z = x) (b : X.left.residueField z ⟶ CommRingCat.of (AlgebraicClosure K)) :
          ∃ b' : X.left.residueField x ⟶ CommRingCat.of (AlgebraicClosure K),
          Spec.map b ≫ X.left.fromSpecResidueField z = Spec.map b' ≫ i := by
        subst z; exact ⟨b, rfl⟩
      obtain ⟨b, hb⟩ := trans _ h ((Scheme.SpecToEquivOfField (AlgebraicClosure K) X.left P.left).2)
      have hp : P.left = Spec.map b ≫ i := by
        rw [← hb]
        exact ((Scheme.SpecToEquivOfField (AlgebraicClosure K) X.left).symm_apply_apply P.left).symm
      have hw : a ≫ b = CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)) := by
        apply Spec.map_injective
        rw [Spec.map_comp, Spec.map_preimage, ← Category.assoc, ← hp]
        exact Over.w P
      exact ⟨{toRingHom := b.hom, commutes' := fun c => congrArg (fun f => f.hom c) hw}, hp⟩
    obtain ⟨b, hb⟩ := factor P he
    obtain ⟨c, hc⟩ := factor Q rfl
    obtain ⟨σ, hσ⟩ := embeddings_conjugate b c
    refine ⟨σ, Over.OverMorphism.ext ?_⟩
    change Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure K →+* AlgebraicClosure K)) ≫ P.left = Q.left
    rw [hb, hc, ← Category.assoc, ← Spec.map_comp]
    congr 2
    ext z
    exact hσ z
  · rintro ⟨σ, rfl⟩
    let : Subsingleton (ptObj (K := K) (AlgebraicClosure K)).left :=
      inferInstanceAs (Subsingleton (PrimeSpectrum (AlgebraicClosure K)))
    exact congrArg P.left (Subsingleton.elim _ _)

/-- A finite Galois-stable set is cut out on geometric points by the closed
subset consisting of its support over the ground field. -/
theorem exists_closed_support {X : Over (Spec (.of K))} [IsSeparated X.hom]
    (S : Set (GeomPt X)) (hfin : S.Finite)
    (hstable : ∀ σ : Field.absoluteGaloisGroup K, ∀ P ∈ S, galHom σ ≫ P ∈ S) :
    ∃ Z : TopologicalSpace.Closeds X.left,
      (Z : Set X.left).Finite ∧ ∀ P : GeomPt X, supportPoint P ∈ Z ↔ P ∈ S := by
  let Z := supportPoint '' S
  have hZ : Z.Finite := hfin.image _
  have hc : IsClosed Z := by
    rw [show Z = ⋃ P ∈ S, {supportPoint P} by ext x; simp [Z, Set.mem_image]; aesop]
    exact hfin.isClosed_biUnion fun P _ => isClosed_supportPoint P
  refine ⟨⟨Z,hc⟩, hZ, fun P => ⟨?_, fun h => ⟨P,h,rfl⟩⟩⟩
  rintro ⟨Q, hQ, he⟩
  obtain ⟨σ,rfl⟩ := (supportPoint_eq_iff Q P).mp he
  exact hstable σ Q hQ

end ZInQ.Contrib.TateFiniteApproximation

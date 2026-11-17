import ZInQKernel.Contrib.CloudB3W17bProjectiveBridge.ProjIso
import ZInQKernel.Contrib.CloudB3W17bGraphScout.AlgebraicProjection

/-! Native projective embedding, carried by actual scheme isomorphisms to a
finite polynomial Proj over a lifted complex base. No Oka projectivity input
or algebraic-map witness is added as a premise. -/

open CategoryTheory Limits AlgebraicGeometry MvPolynomial
open MonoidalCategory CartesianMonoidalCategory MonObj

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bProjectiveBridge

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

/-- A genuine base isomorphism induces a genuine relative-projective-space iso. -/
def relativeBaseIso (I : Type u) {S T : Scheme.{u}} (b : S ≅ T) :
    ProjectiveSpace I S ≅ ProjectiveSpace I T where
  hom := ProjectiveSpace.map I b.hom
  inv := ProjectiveSpace.map I b.inv
  hom_inv_id := by rw [← ProjectiveSpace.map_comp, b.hom_inv_id, ProjectiveSpace.map_id]
  inv_hom_id := by rw [← ProjectiveSpace.map_comp, b.inv_hom_id, ProjectiveSpace.map_id]

/-- Base change and coordinate reindexing preserve the actual coefficient-base morphism. -/
def relativePolynomialIso (I : Type) {R S : Type} [CommRing R] [CommRing S]
    (b : Spec (.of R) ≅ Spec (.of S)) {n : ℕ} (e : I ≃ Fin (n + 1)) :
    ProjectiveSpace I (Spec (.of R)) ≅ Proj (homogeneousSubmodule (Fin (n + 1)) S) :=
  relativeBaseIso I b ≪≫ ProjectiveSpace.affineIso I (.of S) ≪≫ (renameProjIso e).symm

/-- The comparison is over the given base isomorphism, not just a scheme isomorphism. -/
theorem relativePolynomialIso_over (I : Type) {R S : Type} [CommRing R] [CommRing S]
    (b : Spec (.of R) ≅ Spec (.of S)) {n : ℕ} (e : I ≃ Fin (n + 1)) :
    (relativePolynomialIso I b e).hom ≫ Proj.projectiveSpaceOverAffineToSpec (Fin (n + 1)) S =
      (ProjectiveSpace I (Spec (.of R)) ↘ Spec (.of R)) ≫ b.hom := by
  change ProjectiveSpace.map I b.hom ≫ (ProjectiveSpace.affineIso I (.of S)).hom ≫
    (renameProjIso e).inv ≫ Proj.projectiveSpaceOverAffineToSpec (Fin (n + 1)) S = _
  rw [show (renameProjIso e).inv ≫ Proj.projectiveSpaceOverAffineToSpec (Fin (n + 1)) S =
      Proj.projectiveSpaceOverAffineToSpec I S from renameProjIso_over e.symm,
    ProjectiveSpace.affineIso_hom_over, ProjectiveSpace.map_over]

/-- The original A admits a closed embedding in its actual relative projective space. -/
theorem abVar_native_embedding (A : PkgI3.AbVar ℂ) :
    ∃ (I : Type) (_ : Finite I) (e : A.X.left ⟶ ProjectiveSpace I (Spec (.of ℂ))),
      IsClosedImmersion e ∧ e ≫ (ProjectiveSpace I (Spec (.of ℂ)) ↘ Spec (.of ℂ)) = A.X.hom :=
  ZInQ.Contrib.CloudB3W17bGraphScout.abVar_exists_projective_closed_embedding A

/-- No coordinate-index inhabitance is assumed: a source scheme point forces it. -/
theorem coordinate_nonempty {I : Type} {X : Scheme}
    (e : X ⟶ ProjectiveSpace I (Spec (.of ℂ))) [Nonempty X] : Nonempty I := by
  by_contra hi
  have : IsEmpty I := ⟨fun i => hi ⟨i⟩⟩
  have : IsEmpty (ProjectiveSpace I (Spec (.of ℂ))) := inferInstance
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  exact isEmptyElim (e x)

/-- A finite inhabited index can be reindexed to exactly n+1 coordinates. -/
theorem exists_coordinate_equiv (I : Type) [Finite I] [Nonempty I] :
    ∃ n : ℕ, Nonempty (I ≃ Fin (n + 1)) := by
  letI := Fintype.ofFinite I
  have hpos : 0 < Fintype.card I := Fintype.card_pos
  refine ⟨Fintype.card I - 1, ?_⟩
  have hcard : Fintype.card I - 1 + 1 = Fintype.card I := Nat.sub_add_cancel hpos
  exact ⟨(Fintype.equivFin I).trans (Equiv.cast (congrArg Fin hcard.symm))⟩

/-- The same underlying native A has an actual closed embedding into polynomial Proj
on n+1 coordinates over the given isomorphic complex base. -/
theorem abVar_polynomial_embedding (A : PkgI3.AbVar ℂ)
    {S : Type} [CommRing S] (b : Spec (.of ℂ) ≅ Spec (.of S)) :
    ∃ (n : ℕ) (e : A.X.left ⟶ Proj (homogeneousSubmodule (Fin (n + 1)) S)),
      IsClosedImmersion e ∧ e ≫ Proj.projectiveSpaceOverAffineToSpec (Fin (n + 1)) S =
        A.X.hom ≫ b.hom := by
  obtain ⟨I, hI, e, he, hbase⟩ := abVar_native_embedding A
  have := hI
  have := he
  have : Nonempty A.X.left := ⟨η[A.X].left (IsLocalRing.closedPoint ℂ)⟩
  have := coordinate_nonempty e
  obtain ⟨n, ⟨idx⟩⟩ := exists_coordinate_equiv I
  let p := relativePolynomialIso I b idx
  refine ⟨n, e ≫ p.hom, inferInstance, ?_⟩
  rw [Category.assoc, relativePolynomialIso_over, ← Category.assoc, hbase]

/-- The actual ambient A×B is handled by the same genuine group-scheme embedding theorem. -/
theorem prodAbVar_polynomial_embedding (A B : PkgI3.AbVar ℂ)
    {S : Type} [CommRing S] (b : Spec (.of ℂ) ≅ Spec (.of S)) :
    ∃ (n : ℕ) (e : (A.X ⊗ B.X).left ⟶ Proj (homogeneousSubmodule (Fin (n + 1)) S)),
      IsClosedImmersion e ∧ e ≫ Proj.projectiveSpaceOverAffineToSpec (Fin (n + 1)) S =
        (A.X ⊗ B.X).hom ≫ b.hom :=
  abVar_polynomial_embedding (AVGlue.prodAbVar A B) b

#print axioms relativeBaseIso
#print axioms relativePolynomialIso
#print axioms relativePolynomialIso_over
#print axioms abVar_native_embedding
#print axioms coordinate_nonempty
#print axioms exists_coordinate_equiv
#print axioms abVar_polynomial_embedding
#print axioms prodAbVar_polynomial_embedding

end ZInQ.Contrib.CloudB3W17bProjectiveBridge

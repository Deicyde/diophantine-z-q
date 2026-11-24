import ZInQKernel.Contrib.OneProof.BShStandard

/-! ON THE SPOT (provenance (c)): sum the finite family over a splitting
field, descend the invariant sum, and specialize through a common valuation. -/

noncomputable section

namespace BShTraces

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open LeafModCurves PkgI3 PkgI3.AbVar AfTateLam ShimuraPointDict BShStandard

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

/-- An affine spectrum over the rationals, with the specified structural map. -/
def ratSpec {R : Type} [CommRing R] (q : ℚ →+* R) : Over SpecQ :=
  Over.mk (Spec.map (CommRingCat.ofHom q))

/-- Regard a map from an affine spectrum as a point over the rationals. -/
def ratPoint {R : Type} [CommRing R] {Y : Over SpecQ}
    (q : ℚ →+* R) (f : Spec (CommRingCat.of R) ⟶ Y.left) : ratSpec q ⟶ Y :=
  Over.homMk f (spec_to_rat_eq _ _)

/-- Change the ring of definition of a point. -/
def ratSpecMap {R S : Type} [CommRing R] [CommRing S] {qR : ℚ →+* R} {qS : ℚ →+* S}
    (f : R →+* S) : ratSpec qS ⟶ ratSpec qR :=
  ratPoint qS (Spec.map (CommRingCat.ofHom f))

variable {X : Over SpecQ} [IsIntegral X.left] {J : AbVar ℚ}
local notation "KX" => X.left.functionField

/-- Rational constants in the function field. -/
def baseMap (X : Over SpecQ) [IsIntegral X.left] : ℚ →+* X.left.functionField :=
  (Spec.preimage (X.left.fromSpecFunctionField ≫ X.hom)).hom

/-- Base change the generic point along a field homomorphism. -/
def genericBranch {L : Type} [Field L] (qL : ℚ →+* L) (b : KX →+* L) :
    ratSpec qL ⟶ X :=
  ratPoint qL (Spec.map (CommRingCat.ofHom b) ≫ X.left.fromSpecFunctionField)

private theorem comp_prod_points {T U : Over SpecQ} (b : T ⟶ U)
    {I : Type*} [Fintype I] (P : I → (U ⟶ J.X)) :
    b ≫ (∏ i, P i) = ∏ i, b ≫ P i := by
  classical
  suffices ∀ s : Finset I, b ≫ (∏ i ∈ s, P i) = ∏ i ∈ s, b ≫ P i from this _
  intro s
  induction s using Finset.induction_on with
  | empty => simp [MonObj.comp_one]
  | insert i s hi ih => simp [Finset.prod_insert, hi, MonObj.comp_mul, ih]

/-- Pullback of the sum of marked branches along the structural inclusion of a
finite Galois extension. The Galois action may permute repeated entries. -/
theorem exists_extension_of_permuted_branches
    (hC : IsCurve X) (aj : X ⟶ J.X)
    {L : Type} [Field L] [Algebra KX L] [FiniteDimensional KX L] [IsGalois KX L]
    {I : Type*} [Fintype I] (b : I → KX →+* L)
    (hperm : ∀ σ : L ≃ₐ[KX] L, ∃ π : Equiv.Perm I,
      ∀ i, (σ : L →+* L).comp (b i) = b (π i)) :
    ∃ F : X ⟶ J.X,
      ratSpecMap (qR := baseMap X) (qS := (algebraMap KX L).comp (baseMap X))
          (algebraMap KX L) ≫ genericBranch (baseMap X) (RingHom.id KX) ≫ F =
        ∏ i, genericBranch ((algebraMap KX L).comp (baseMap X)) (b i) ≫ aj := by
  let q := (algebraMap KX L).comp (baseMap X)
  let P : I → (ratSpec q ⟶ J.X) := fun i => genericBranch q (b i) ≫ aj
  let S : ratSpec q ⟶ J.X := ∏ i, P i
  have hS (σ : L ≃ₐ[KX] L) :
      Spec.map (CommRingCat.ofHom (σ : L →+* L)) ≫ S.left = S.left := by
    obtain ⟨π, hπ⟩ := hperm σ
    change ((ratSpecMap (qR := q) (qS := q) (σ : L →+* L)) ≫ S).left = S.left
    congr 1
    dsimp only [S]
    rw [comp_prod_points]
    have he (i : I) : ratSpecMap (qR := q) (qS := q) (σ : L →+* L) ≫ P i = P (π i) := by
      apply Over.OverMorphism.ext
      change Spec.map (CommRingCat.ofHom (σ : L →+* L)) ≫
        (Spec.map (CommRingCat.ofHom (b i)) ≫ X.left.fromSpecFunctionField) ≫ aj.left =
          (Spec.map (CommRingCat.ofHom (b (π i))) ≫ X.left.fromSpecFunctionField) ≫ aj.left
      simp only [Category.assoc]
      rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, hπ]
    simp_rw [he]
    exact Equiv.prod_comp π P
  obtain ⟨S₀, h₀⟩ := exists_descend_galois S.left hS
  letI : IsProper J.X.hom := J.proper
  obtain ⟨F, hF⟩ := exists_extension hC S₀
  refine ⟨F, ?_⟩
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (algebraMap KX L)) ≫
    (Spec.map (CommRingCat.ofHom (RingHom.id KX)) ≫ X.left.fromSpecFunctionField) ≫ F.left =
      S.left
  rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp, hF, h₀]

/-- Specialize a sum of branches along any common valuation ring.  The maps
from its spectrum give the source point and all the branches at once. -/
theorem specialize_sum_of_branches (F : X ⟶ J.X) (aj : X ⟶ J.X)
    {L : Type} [Field L] (A : ValuationSubring L)
    (qA : ℚ →+* A) (qL : ℚ →+* L) (qC : ℚ →+* ℂ) (e : A →+* ℂ)
    {I : Type*} [Fintype I] (f : ratSpec qA ⟶ X) (b : I → (ratSpec qA ⟶ X))
    (h : ratSpecMap (qR := qA) (qS := qL) A.subtype ≫ f ≫ F =
      ∏ i, ratSpecMap (qR := qA) (qS := qL) A.subtype ≫ b i ≫ aj) :
    ratSpecMap (qR := qA) (qS := qC) e ≫ f ≫ F =
      ∏ i, ratSpecMap (qR := qA) (qS := qC) e ≫ b i ≫ aj := by
  let g := ratSpecMap (qR := qA) (qS := qL) A.subtype
  let s : ratSpec qA ⟶ J.X := ∏ i, b i ≫ aj
  have hgen : g ≫ (f ≫ F) = g ≫ s := h.trans (comp_prod_points g _).symm
  letI : IsProper J.X.hom := J.proper
  let sq : ValuativeCommSq J.X.hom :=
    { R := A
      K := L
      i₁ := (g ≫ f ≫ F).left
      i₂ := Spec.map (CommRingCat.ofHom qA)
      commSq := ⟨spec_to_rat_eq _ _⟩ }
  let l₁ : sq.commSq.LiftStruct := ⟨(f ≫ F).left, rfl, spec_to_rat_eq _ _⟩
  let l₂ : sq.commSq.LiftStruct := ⟨s.left, congrArg Over.Hom.left hgen.symm, spec_to_rat_eq _ _⟩
  letI := IsSeparated.valuativeCriterion J.X.hom sq
  have hl : f ≫ F = s := Over.OverMorphism.ext
    (congrArg CommSq.LiftStruct.l (Subsingleton.elim l₁ l₂))
  rw [hl, comp_prod_points]

section Germs

open UpperHalfPlane Filter
open scoped Topology

/-- A field embedding that gives the expected finite germ values on a stalk
lifts the generic branch through the valuation ring and specializes to that point. -/
theorem exists_branch_lift_of_stalk_values {L : Type} [Field L] {z : ℂ}
    (u : L →+* PuncturedGerm z)
    (hu : ∀ g, ∃ f : ℂ → ℂ, (f : PuncturedGerm z) = u g ∧ MeromorphicAt f z)
    (qL : ℚ →+* L) (qA : ℚ →+* finiteValuationSubring u hu)
    (b : KX →+* L) (x : CPt X)
    (h : ∀ r : X.left.presheaf.stalk (complexMap x (IsLocalRing.closedPoint ℂ)),
      HasValue (u (b (algebraMap _ KX r))) (Scheme.stalkClosedPointTo (complexMap x) r)) :
    ∃ f : ratSpec qA ⟶ X,
      ratSpecMap (qR := qA) (qS := qL) (finiteValuationSubring u hu).subtype ≫ f =
        genericBranch qL b ∧
      ratSpecMap (qR := qA) (qS := algebraMap ℚ ℂ) (finiteValue u) ≫ f = x := by
  let A := finiteValuationSubring u hu
  let v : X.left.presheaf.stalk (complexMap x (IsLocalRing.closedPoint ℂ)) →+* A :=
    (b.comp (algebraMap _ KX)).codRestrict _ (fun r => ⟨_, h r⟩)
  have he : (finiteValue u).comp v = (Scheme.stalkClosedPointTo (complexMap x)).hom := by
    ext r
    exact hasValue_unique (finiteValue_spec _ (v r)) (h r)
  let f := ratPoint qA (Spec.map (CommRingCat.ofHom v) ≫ X.left.fromSpecStalk _)
  refine ⟨f, ?_, ?_⟩
  · apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom A.subtype) ≫ Spec.map (CommRingCat.ofHom v) ≫
      X.left.fromSpecStalk _ = Spec.map (CommRingCat.ofHom b) ≫ X.left.fromSpecFunctionField
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
    change Spec.map (CommRingCat.ofHom (b.comp (algebraMap _ KX))) ≫ _ = _
    have generic (w : X.left) :
        Spec.map (CommRingCat.ofHom (algebraMap (X.left.presheaf.stalk w) KX)) ≫
          X.left.fromSpecStalk w = X.left.fromSpecFunctionField :=
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes w)
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, generic]
  · apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (finiteValue u)) ≫ Spec.map (CommRingCat.ofHom v) ≫
      X.left.fromSpecStalk _ = complexMap x
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, he]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk _

end Germs

#print axioms comp_prod_points
#print axioms exists_extension_of_permuted_branches
#print axioms specialize_sum_of_branches
#print axioms exists_branch_lift_of_stalk_values

end BShTraces

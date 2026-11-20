import ZInQKernel.Contrib.CloudR2Poincare.L2.FieldTrivialityDetection
import ZInQKernel.Contrib.CloudR2Poincare.L2.NormalizedRestriction
import ZInQKernel.Contrib.CloudR2Poincare.L1.QuotientBundle

/-!
# The actual reduced closed graph of quotient polarization classes

This is the global residue-fibre triviality locus on J×Q of the difference
between the restricted J-polarization family and the descended bundle on B×Q.
Its reduced closed scheme is constructed, not assumed. Normalized fpqc field
class detection classifies all extension-field points of this ORIGINAL graph.
The graph projection being an isomorphism is a separate geometric step.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory
  CartesianMonoidalCategory MonObj

namespace ZInQ.Contrib.CloudR2Poincare.L2

universe u

/-- Actual product structural morphism is proper over the original field. -/
theorem abVarProduct_proper {k : Type u} [Field k] (J Q : PkgI3.AbVar k) :
    IsProper (J.X ⊗ Q.X).hom := by
  change IsProper (pullback.fst J.X.hom Q.X.hom ≫ J.X.hom)
  infer_instance

/-- Actual first projection of the product is a base change of Q→Spec k. -/
theorem abVarProduct_fst_proper {k : Type u} [Field k] (J Q : PkgI3.AbVar k) :
    IsProper (fst J.X Q.X).left := by
  change IsProper (pullback.fst J.X.hom Q.X.hom)
  infer_instance

/-- The actual normalized J-family restricted along the original B→J. -/
def restrictedPolarizationFamily {k : Type u} [Field k]
    (J B : PkgI3.AbVar k) (i : PkgI3.AbVar.Hom B J) (L : J.X.left.Pic) :
    (pullback B.X.hom J.X.hom).Pic :=
  Scheme.Pic.map (L1.picardFamilyMap i.hom J.X)
    (L1.normalizedPolarizationFamily J.X L (𝟙 J.X))

/-- Genuine normalization of the restricted family, via the actual unit-section square. -/
theorem restrictedPolarizationFamily_normalized {k : Type u} [Field k]
    (J B : PkgI3.AbVar k) (i : PkgI3.AbVar.Hom B J) (L : J.X.left.Pic) :
    Scheme.Pic.map (sectionBaseChange B.X.hom η[B.X].left (L1.groupUnit_over B.X) J.X)
      (restrictedPolarizationFamily J B i L) = 1 := by
  rw [restrictedPolarizationFamily, ← Scheme.Pic.map_comp, sectionBaseChange_picardFamilyMap]
  exact L1.normalizedPolarizationFamily_normalized J.X L (𝟙 J.X)

/-- Parameter restriction of that actual B×J family. -/
theorem restrictedPolarizationFamily_parameter {k : Type u} [Field k]
    (J B : PkgI3.AbVar k) (i : PkgI3.AbVar.Hom B J) (L : J.X.left.Pic)
    {T : Over (Spec (.of k))} (x : T ⟶ J.X) :
    Scheme.Pic.map (JacobianChallenge.baseChangeMap B.X.hom x)
      (restrictedPolarizationFamily J B i L) =
    Scheme.Pic.map (L1.picardFamilyMap i.hom T) (L1.normalizedPolarizationFamily J.X L x) := by
  rw [restrictedPolarizationFamily, ← Scheme.Pic.map_comp, L1.picardFamilyMap_naturality,
    Scheme.Pic.map_comp, L1.normalizedPolarizationFamily_parameter, Category.comp_id]

/-- Difference of the actual restricted and quotient-descended bundles on B×(J×Q). -/
def quotientGraphFamily {k : Type u} [Field k]
    (J B Q : PkgI3.AbVar k) (i : PkgI3.AbVar.Hom B J) (L : J.X.left.Pic)
    (P : (pullback B.X.hom Q.X.hom).Pic) :
    (pullback B.X.hom (J.X ⊗ Q.X).hom).Pic :=
  Scheme.Pic.map (JacobianChallenge.baseChangeMap B.X.hom (fst J.X Q.X))
      (restrictedPolarizationFamily J B i L) *
    (Scheme.Pic.map (JacobianChallenge.baseChangeMap B.X.hom (snd J.X Q.X)) P)⁻¹

/-- Both true normalizations make the graph difference family normalized. -/
theorem quotientGraphFamily_normalized {k : Type u} [Field k]
    (J B Q : PkgI3.AbVar k) (i : PkgI3.AbVar.Hom B J) (L : J.X.left.Pic)
    (P : (pullback B.X.hom Q.X.hom).Pic) (hP : L1.IsNormalizedFamily B Q.X P) :
    Scheme.Pic.map
      (sectionBaseChange B.X.hom η[B.X].left (L1.groupUnit_over B.X) (J.X ⊗ Q.X))
      (quotientGraphFamily J B Q i L P) = 1 := by
  rw [quotientGraphFamily, Scheme.Pic.map_mul, L1.pic_map_inv]
  have hn := normalizedPicard_baseChange_normalized B.X.hom η[B.X].left
    (L1.groupUnit_over B.X) (fst J.X Q.X) (restrictedPolarizationFamily J B i L)
    (restrictedPolarizationFamily_normalized J B i L)
  have hnP := normalizedPicard_baseChange_normalized B.X.hom η[B.X].left
    (L1.groupUnit_over B.X) (snd J.X Q.X) P hP
  rw [hn, hnP, inv_one, _root_.mul_one]

/-- The graph's actual fibre class for an arbitrary pair of parameter morphisms. -/
theorem quotientGraphFamily_pair {k : Type u} [Field k]
    (J B Q : PkgI3.AbVar k) (i : PkgI3.AbVar.Hom B J) (L : J.X.left.Pic)
    (P : (pullback B.X.hom Q.X.hom).Pic) {T : Over (Spec (.of k))}
    (x : T ⟶ J.X) (z : T ⟶ Q.X) :
    Scheme.Pic.map (JacobianChallenge.baseChangeMap B.X.hom (lift x z))
      (quotientGraphFamily J B Q i L P) =
    Scheme.Pic.map (L1.picardFamilyMap i.hom T) (L1.normalizedPolarizationFamily J.X L x) *
      (Scheme.Pic.map (JacobianChallenge.baseChangeMap B.X.hom z) P)⁻¹ := by
  rw [quotientGraphFamily, Scheme.Pic.map_mul, L1.pic_map_inv,
    ← Scheme.Pic.map_comp, ← Scheme.Pic.map_comp, ← JacobianChallenge.baseChangeMap_comp,
    ← JacobianChallenge.baseChangeMap_comp, lift_fst, lift_snd, restrictedPolarizationFamily_parameter]

/-- GLOBAL closed locus of the graph family on the original J×Q. -/
def quotientGraphClosed {k : Type u} [Field k]
    (J B Q : PkgI3.AbVar k) (i : PkgI3.AbVar.Hom B J) (L : J.X.left.Pic)
    (P : (pullback B.X.hom Q.X.hom).Pic) : TopologicalSpace.Closeds (J.X ⊗ Q.X).left :=
  letI : IsProper (J.X ⊗ Q.X).hom := abVarProduct_proper J Q
  letI : IsLocallyNoetherian (J.X ⊗ Q.X).left :=
    LocallyOfFiniteType.isLocallyNoetherian (J.X ⊗ Q.X).hom
  globalFibreTrivialityClosed (pullback.snd B.X.hom (J.X ⊗ Q.X).hom)
    (quotientGraphFamily J B Q i L P)

/-- The actual reduced closed subscheme Γ, over the original field. -/
def quotientGraph {k : Type u} [Field k]
    (J B Q : PkgI3.AbVar k) (i : PkgI3.AbVar.Hom B J) (L : J.X.left.Pic)
    (P : (pullback B.X.hom Q.X.hom).Pic) : Over (Spec (.of k)) :=
  Over.mk (L1.reducedClosedSupportι (J.X ⊗ Q.X).left (quotientGraphClosed J B Q i L P) ≫
    (J.X ⊗ Q.X).hom)

/-- Actual closed graph inclusion Γ→J×Q. -/
def quotientGraphι {k : Type u} [Field k]
    (J B Q : PkgI3.AbVar k) (i : PkgI3.AbVar.Hom B J) (L : J.X.left.Pic)
    (P : (pullback B.X.hom Q.X.hom).Pic) : quotientGraph J B Q i L P ⟶ J.X ⊗ Q.X :=
  Over.homMk (L1.reducedClosedSupportι (J.X ⊗ Q.X).left (quotientGraphClosed J B Q i L P))

instance quotientGraph_closed {k : Type u} [Field k]
    (J B Q : PkgI3.AbVar k) (i : PkgI3.AbVar.Hom B J) (L : J.X.left.Pic)
    (P : (pullback B.X.hom Q.X.hom).Pic) : IsClosedImmersion (quotientGraphι J B Q i L P).left :=
  L1.reducedClosedSupport_closed _ _

instance quotientGraph_reduced {k : Type u} [Field k]
    (J B Q : PkgI3.AbVar k) (i : PkgI3.AbVar.Hom B J) (L : J.X.left.Pic)
    (P : (pullback B.X.hom Q.X.hom).Pic) : AlgebraicGeometry.IsReduced (quotientGraph J B Q i L P).left :=
  L1.reducedClosedSupport_reduced _ _

/-- The ORIGINAL graph is proper over J because Q is proper and Γ is closed. -/
theorem quotientGraph_projection_isProper {k : Type u} [Field k]
    (J B Q : PkgI3.AbVar k) (i : PkgI3.AbVar.Hom B J) (L : J.X.left.Pic)
    (P : (pullback B.X.hom Q.X.hom).Pic) :
    IsProper (quotientGraphι J B Q i L P ≫ fst J.X Q.X).left := by
  letI : IsProper (fst J.X Q.X).left := abVarProduct_fst_proper J Q
  change IsProper ((quotientGraphι J B Q i L P).left ≫ (fst J.X Q.X).left)
  infer_instance

/-- ALL extension-field points of the ORIGINAL graph are classified by the
actual difference-fibre equality; not by a separately constructed Ω graph. -/
theorem quotientGraph_fieldPoint_factor_iff
    {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω]
    (J B Q : PkgI3.AbVar k) (i : PkgI3.AbVar.Hom B J) (L : J.X.left.Pic)
    (P : (pullback B.X.hom Q.X.hom).Pic) (hP : L1.IsNormalizedFamily B Q.X P)
    (x : L1.fieldTest k Ω ⟶ J.X) (z : L1.fieldTest k Ω ⟶ Q.X) :
    (∃ a : L1.fieldTest k Ω ⟶ quotientGraph J B Q i L P,
      a ≫ quotientGraphι J B Q i L P = lift x z) ↔
    Scheme.Pic.map (L1.picardFamilyMap i.hom (L1.fieldTest k Ω))
        (L1.normalizedPolarizationFamily J.X L x) =
      Scheme.Pic.map (JacobianChallenge.baseChangeMap B.X.hom z) P := by
  let T := J.X ⊗ Q.X
  let t : L1.fieldTest k Ω ⟶ T := lift x z
  letI : IsProper T.hom := abVarProduct_proper J Q
  letI : IsLocallyNoetherian T.left := LocallyOfFiniteType.isLocallyNoetherian T.hom
  have hmem := fibreTriviality_mem_fieldTest_iff B.X.hom η[B.X].left (L1.groupUnit_over B.X)
    T (quotientGraphFamily J B Q i L P) (quotientGraphFamily_normalized J B Q i L P hP) t
  rw [quotientGraphFamily_pair, _root_.mul_inv_eq_one] at hmem
  letI : Subsingleton (L1.fieldTest k Ω).left := inferInstanceAs (Subsingleton (Spec (.of Ω)))
  letI : AlgebraicGeometry.IsReduced (L1.fieldTest k Ω).left :=
    inferInstanceAs (AlgebraicGeometry.IsReduced (Spec (.of Ω)))
  constructor
  · rintro ⟨a, ha⟩
    apply hmem.mp
    have hm : (quotientGraphι J B Q i L P).left (a.left (IsLocalRing.closedPoint Ω)) ∈
        (quotientGraphClosed J B Q i L P : Set T.left) := by
      rw [← L1.range_reducedClosedSupportι]
      exact ⟨_, rfl⟩
    change t.left (IsLocalRing.closedPoint Ω) ∈ (quotientGraphClosed J B Q i L P : Set T.left)
    have he : t = a ≫ quotientGraphι J B Q i L P := ha.symm
    rw [he, Over.comp_left, Scheme.Hom.comp_apply]
    exact hm
  · intro hz
    have hm := hmem.mpr hz
    change t.left (IsLocalRing.closedPoint Ω) ∈ (quotientGraphClosed J B Q i L P : Set T.left) at hm
    have hr : Set.range t.left ⊆ quotientGraphClosed J B Q i L P := by
      rintro a ⟨v, rfl⟩
      simpa only [Subsingleton.elim v (IsLocalRing.closedPoint Ω)] using hm
    obtain ⟨b, hb⟩ := L1.exists_factor_reducedClosedSupport (quotientGraphClosed J B Q i L P) t.left hr
    let a : L1.fieldTest k Ω ⟶ quotientGraph J B Q i L P := Over.homMk b (by
      change b ≫ (L1.reducedClosedSupportι T.left (quotientGraphClosed J B Q i L P) ≫ T.hom) =
        Spec.map (CommRingCat.ofHom (algebraMap k Ω))
      rw [← Category.assoc, hb]
      exact Over.w t)
    refine ⟨a, ?_⟩
    apply Over.OverMorphism.ext
    exact hb

end ZInQ.Contrib.CloudR2Poincare.L2

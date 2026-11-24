/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

Geometry-only consumer of the FROZEN actual tensor triple. All chart/base
and generic-open identities needed by Lane6's native line-coherence proof
are DERIVED from the same cartesian squares and nerve equations. No line,
module, psi, hpsi, effective quotient or extra geometry premise is supplied.
The existing geometry-only triple-diagonal lemma is reused from Lane6;
its line/coherence proofs are neither copied nor duplicated.
-/
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.TensorTriple
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.GenericTensor
import ZInQKernel.Contrib.CloudR2NOS.Review.ModuleLineTripleGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective.TensorTripleChartGeometry
open TensorCofaces TensorNerve

variable {R : Type u} [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R']
  (V : (Base R).Opens) (G : Grp (Over (Cover R'))) (A : Grp (Over V.toScheme))
  (e : (Over.pullback ((baseMap R R') ⁻¹ᵁ V).ι).mapGrp.obj G ≅
    (Over.pullback ((baseMap R R') ∣_ V)).mapGrp.obj A)
  [Etale (baseMap R R')] (c : Base R)
  [Mono ((baseMap R R').fiberToSpecResidueField c)]
  (hV : ∀ z : Base R, z ∉ V → z = c)

/-- Literal three original base morphisms in Lane6's requested order. -/
abbrev u1 : model3 (R := R) R' G ⟶ Cover R' :=
  chart13 (R := R) R' G ≫ projection1 (R := R) R' G ≫ G.X.hom
abbrev u2 : model3 (R := R) R' G ⟶ Cover R' :=
  chart23 R' V G A e c hV ≫ projection1 (R := R) R' G ≫ G.X.hom
abbrev u3 : model3 (R := R) R' G ⟶ Cover R' :=
  chart13 (R := R) R' G ≫ projection2 R' V G A e c hV ≫ G.X.hom

/-- Both original projections of EVERY actual scheme test have the same
    composite to the original base. This is a morphism equality, not points. -/
theorem test_pair_base_eq {T : Scheme.{u}} (t : T ⟶ model2 (R := R) R' G) :
    (t ≫ projection1 (R := R) R' G ≫ G.X.hom) ≫ baseMap R R' =
      (t ≫ projection2 R' V G A e c hV ≫ G.X.hom) ≫ baseMap R R' := by
  have h : (projection1 (R := R) R' G ≫ G.X.hom) ≫ baseMap R R' =
      (projection2 R' V G A e c hV ≫ G.X.hom) ≫ baseMap R R' := by
    calc
      (projection1 (R := R) R' G ≫ G.X.hom) ≫ baseMap R R' =
          (structure2 (R := R) R' G ≫ left R R') ≫ baseMap R R' :=
        congrArg (· ≫ baseMap R R') (cartesian1 (R := R) R' G).w
      _ = (structure2 (R := R) R' G ≫ right R R') ≫ baseMap R R' := by
        simp only [Category.assoc, left_base R R']
      _ = (projection2 R' V G A e c hV ≫ G.X.hom) ≫ baseMap R R' :=
        congrArg (· ≫ baseMap R R') (cartesian2 R' V G A e c hV).w.symm
  simpa only [Category.assoc] using congrArg (t ≫ ·) h

/-- The actual 12-chart base pair is precisely (u1,u2). -/
@[reassoc]
theorem chart12_first_base : chart12 (R := R) R' G ≫ projection1 (R := R) R' G ≫ G.X.hom =
    u1 (R := R) R' G := by
  simpa only [u1, Category.assoc] using
    congrArg (fun a : model3 (R := R) R' G ⟶ G.X.left => a ≫ G.X.hom)
      (nerve_eq1 (R := R) R' G)

@[reassoc]
theorem chart12_second_base : chart12 (R := R) R' G ≫ structure2 (R := R) R' G ≫ right R R' =
    u2 R' V G A e c hV := by
  calc
    chart12 (R := R) R' G ≫ structure2 (R := R) R' G ≫ right R R' =
        chart12 (R := R) R' G ≫ projection2 R' V G A e c hV ≫ G.X.hom :=
      congrArg (chart12 (R := R) R' G ≫ ·) (cartesian2 R' V G A e c hV).w.symm
    _ = u2 R' V G A e c hV := by
      simpa only [u2, Category.assoc] using
        congrArg (fun a : model3 (R := R) R' G ⟶ G.X.left => a ≫ G.X.hom)
          (nerve_eq2 R' V G A e c hV)

/-- The actual 23-chart base pair is precisely (u2,u3). -/
@[reassoc]
theorem chart23_second_base : chart23 R' V G A e c hV ≫ structure2 (R := R) R' G ≫ right R R' =
    u3 R' V G A e c hV := by
  calc
    chart23 R' V G A e c hV ≫ structure2 (R := R) R' G ≫ right R R' =
        chart23 R' V G A e c hV ≫ projection2 R' V G A e c hV ≫ G.X.hom :=
      congrArg (chart23 R' V G A e c hV ≫ ·) (cartesian2 R' V G A e c hV).w.symm
    _ = u3 R' V G A e c hV := by
      simpa only [u3, Category.assoc] using
        congrArg (fun a : model3 (R := R) R' G ⟶ G.X.left => a ≫ G.X.hom)
          (nerve_eq3 R' V G A e c hV).symm

/-- The actual 13-chart base pair is precisely (u1,u3). -/
@[reassoc]
theorem chart13_second_base : chart13 (R := R) R' G ≫ structure2 (R := R) R' G ≫ right R R' =
    u3 R' V G A e c hV :=
  congrArg (chart13 (R := R) R' G ≫ ·) (cartesian2 R' V G A e c hV).w.symm

/-- The three requested maps have genuinely equal composites to the original base. -/
theorem base12 : u1 (R := R) R' G ≫ baseMap R R' = u2 R' V G A e c hV ≫ baseMap R R' := by
  have hpair := test_pair_base_eq R' V G A e c hV (chart12 (R := R) R' G)
  have hfirst := congrArg (· ≫ baseMap R R') (chart12_first_base (R := R) R' G)
  have hsecond := congrArg (· ≫ baseMap R R') (chart12_second_base R' V G A e c hV)
  have hcart : (chart12 (R := R) R' G ≫ projection2 R' V G A e c hV ≫ G.X.hom) ≫ baseMap R R' =
      (chart12 (R := R) R' G ≫ structure2 (R := R) R' G ≫ right R R') ≫ baseMap R R' :=
    congrArg (fun a : model2 (R := R) R' G ⟶ Cover R' =>
      (chart12 (R := R) R' G ≫ a) ≫ baseMap R R') (cartesian2 R' V G A e c hV).w
  exact hfirst.symm.trans (hpair.trans (hcart.trans hsecond))

theorem base23 : u2 R' V G A e c hV ≫ baseMap R R' = u3 R' V G A e c hV ≫ baseMap R R' := by
  have hpair := test_pair_base_eq R' V G A e c hV (chart23 R' V G A e c hV)
  have hlast : (chart23 R' V G A e c hV ≫ projection2 R' V G A e c hV ≫ G.X.hom) ≫ baseMap R R' =
      u3 R' V G A e c hV ≫ baseMap R R' := by
    simpa only [u3, Category.assoc] using
      congrArg (fun a : model3 (R := R) R' G ⟶ G.X.left => (a ≫ G.X.hom) ≫ baseMap R R')
        (nerve_eq3 R' V G A e c hV).symm
  exact hpair.trans hlast

theorem base13 : u1 (R := R) R' G ≫ baseMap R R' = u3 R' V G A e c hV ≫ baseMap R R' :=
  (base12 R' V G A e c hV).trans (base23 R' V G A e c hV)

/-- EXACT requested intersection of the 12/23 original equality opens. -/
def D : (model3 (R := R) R' G).Opens :=
  equalityOpen (baseMap R R') (u1 (R := R) R' G) (u2 R' V G A e c hV) (base12 R' V G A e c hV) ⊓
    equalityOpen (baseMap R R') (u2 R' V G A e c hV) (u3 R' V G A e c hV) (base23 R' V G A e c hV)

/-- EXACT requested original-base generic open. -/
def H : (model3 (R := R) R' G).Opens := (u1 (R := R) R' G ≫ baseMap R R') ⁻¹ᵁ V

/-- Reuse the existing scheme-geometry lemma, rather than duplicating the
    triple diagonal/cover proof or taking line/coherence hypotheses. -/
theorem diagonal_base_eqs :
    (D R' V G A e c hV).ι ≫ u1 (R := R) R' G = (D R' V G A e c hV).ι ≫ u2 R' V G A e c hV ∧
    (D R' V G A e c hV).ι ≫ u2 R' V G A e c hV = (D R' V G A e c hV).ι ≫ u3 R' V G A e c hV :=
  ZInQ.Contrib.CloudR2NOS.Review.LineDescent.triple_diagonal_base_eq
    (baseMap R R') (u1 (R := R) R' G) (u2 R' V G A e c hV) (u3 R' V G A e c hV)
    (base12 R' V G A e c hV) (base23 R' V G A e c hV)

/-- Equal FIRST/SECOND base maps on D for the literal 12 test. -/
theorem diagonal_chart12 :
    (D R' V G A e c hV).ι ≫ chart12 (R := R) R' G ≫ projection1 (R := R) R' G ≫ G.X.hom =
      (D R' V G A e c hV).ι ≫ chart12 (R := R) R' G ≫ structure2 (R := R) R' G ≫ right R R' := by
  have hd := (diagonal_base_eqs R' V G A e c hV).1
  exact (congrArg ((D R' V G A e c hV).ι ≫ ·) (chart12_first_base (R := R) R' G)).trans
    (hd.trans (congrArg ((D R' V G A e c hV).ι ≫ ·) (chart12_second_base R' V G A e c hV)).symm)

/-- Equal FIRST/SECOND base maps on D for the literal 23 test. -/
theorem diagonal_chart23 :
    (D R' V G A e c hV).ι ≫ chart23 R' V G A e c hV ≫ projection1 (R := R) R' G ≫ G.X.hom =
      (D R' V G A e c hV).ι ≫ chart23 R' V G A e c hV ≫ structure2 (R := R) R' G ≫ right R R' := by
  have hd := (diagonal_base_eqs R' V G A e c hV).2
  exact hd.trans (congrArg ((D R' V G A e c hV).ι ≫ ·) (chart23_second_base R' V G A e c hV)).symm

/-- Equal FIRST/SECOND base maps on D for the literal 13 test. -/
theorem diagonal_chart13 :
    (D R' V G A e c hV).ι ≫ chart13 (R := R) R' G ≫ projection1 (R := R) R' G ≫ G.X.hom =
      (D R' V G A e c hV).ι ≫ chart13 (R := R) R' G ≫ structure2 (R := R) R' G ≫ right R R' := by
  have hd := (diagonal_base_eqs R' V G A e c hV).1.trans (diagonal_base_eqs R' V G A e c hV).2
  exact hd.trans (congrArg ((D R' V G A e c hV).ι ≫ ·) (chart13_second_base R' V G A e c hV)).symm

/-- Membership in the original square-generic open follows from the actual
    first-projection base coordinate, using its cartesian MORPHISM equality. -/
private theorem test_generic_mem {T : Scheme.{u}} (t : T ⟶ model2 (R := R) R' G)
    (ht : ∀ z : T, ((t ≫ projection1 (R := R) R' G ≫ G.X.hom) ≫ baseMap R R') z ∈ V) :
    ∀ z : T, t z ∈ modelSquareGenericOpen R' V G := by
  intro z
  change (baseMap R R') (left R R' (structure2 (R := R) R' G (t z))) ∈ V
  have h := congrArg (fun a : model2 (R := R) R' G ⟶ Cover R' => a (t z)) (cartesian1 (R := R) R' G).w
  simp only [Scheme.Hom.comp_apply] at h
  rw [← h]
  simpa only [Scheme.Hom.comp_apply] using ht z

private theorem generic12_mem : ∀ z : (H (R := R) R' V G).toScheme,
    ((H (R := R) R' V G).ι ≫ chart12 (R := R) R' G) z ∈ modelSquareGenericOpen R' V G := by
  apply test_generic_mem (R := R) R' V G
  intro z
  change ((chart12 (R := R) R' G ≫ projection1 (R := R) R' G ≫ G.X.hom) ≫ baseMap R R') z.val ∈ V
  rw [chart12_first_base]
  exact z.property

private theorem generic23_mem : ∀ z : (H (R := R) R' V G).toScheme,
    ((H (R := R) R' V G).ι ≫ chart23 R' V G A e c hV) z ∈ modelSquareGenericOpen R' V G := by
  apply test_generic_mem (R := R) R' V G
  intro z
  change (u2 R' V G A e c hV ≫ baseMap R R') z.val ∈ V
  rw [← base12 R' V G A e c hV]
  exact z.property

private theorem generic13_mem : ∀ z : (H (R := R) R' V G).toScheme,
    ((H (R := R) R' V G).ι ≫ chart13 (R := R) R' G) z ∈ modelSquareGenericOpen R' V G := by
  apply test_generic_mem (R := R) R' V G
  intro z
  change (u1 (R := R) R' G ≫ baseMap R R') z.val ∈ V
  exact z.property

/-- Actual factor of Hι≫chart12 through the ORIGINAL modelSquareGenericOpen. -/
def factor12 : (H (R := R) R' V G).toScheme ⟶ (modelSquareGenericOpen R' V G).toScheme :=
  intoOpen ((H (R := R) R' V G).ι ≫ chart12 (R := R) R' G)
    (modelSquareGenericOpen R' V G) (generic12_mem (R := R) R' V G)

/-- Actual factor of Hι≫chart23 through the ORIGINAL modelSquareGenericOpen. -/
def factor23 : (H (R := R) R' V G).toScheme ⟶ (modelSquareGenericOpen R' V G).toScheme :=
  intoOpen ((H (R := R) R' V G).ι ≫ chart23 R' V G A e c hV)
    (modelSquareGenericOpen R' V G) (generic23_mem R' V G A e c hV)

/-- Actual factor of Hι≫chart13 through the ORIGINAL modelSquareGenericOpen. -/
def factor13 : (H (R := R) R' V G).toScheme ⟶ (modelSquareGenericOpen R' V G).toScheme :=
  intoOpen ((H (R := R) R' V G).ι ≫ chart13 (R := R) R' G)
    (modelSquareGenericOpen R' V G) (generic13_mem (R := R) R' V G)

@[reassoc (attr := simp)]
theorem factor12_ι : factor12 (R := R) R' V G ≫ (modelSquareGenericOpen R' V G).ι =
    (H (R := R) R' V G).ι ≫ chart12 (R := R) R' G := intoOpen_ι _ _ _

@[reassoc (attr := simp)]
theorem factor23_ι : factor23 R' V G A e c hV ≫ (modelSquareGenericOpen R' V G).ι =
    (H (R := R) R' V G).ι ≫ chart23 R' V G A e c hV := intoOpen_ι _ _ _

@[reassoc (attr := simp)]
theorem factor13_ι : factor13 (R := R) R' V G ≫ (modelSquareGenericOpen R' V G).ι =
    (H (R := R) R' V G).ι ≫ chart13 (R := R) R' G := intoOpen_ι _ _ _

#print axioms base12
#print axioms base23
#print axioms diagonal_chart12
#print axioms diagonal_chart23
#print axioms diagonal_chart13
#print axioms factor12_ι
#print axioms factor23_ι
#print axioms factor13_ι

end ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective.TensorTripleChartGeometry

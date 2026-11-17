/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

NEW SOURCE EDITION — 2026-11-17, Q0 scheme-only producer integration.
Historical route(c) ProjConstruction eeeee35ef6feb64d0b23963eb8808fd79845aa9b726e7a6623e72cf7f409cbbe
remains frozen. The OLD FLT effective-descent supplier import/call is replaced
by C4's native route-Q Q0 (Descent.Assembly b3ce84fe), on the SAME tensor nerve.
Q0 takes the prior call's arguments minus hM and produces only X/f/q/hq/hco.

ActualLineCocycle and the constructor INPUT telescope are unchanged. Only
its INTERMEDIATE output forgets the unused descended-line witnesses; hM stays
an explicit existing input for caller compatibility, not a Q0 premise.
Public group/good-reduction consumer types remain unchanged. The bound
historical line predicates remain, and Q0's own leaf/import closure needs C6
and Parent validation; NOT a zero-FLT closure or a native/default proof pass.

Source blueprint credit: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2,
Apache-2.0; original copyright/license/attribution notices stay in history.
New Q0 producer credit: H5 lane4 route-Q ledger001 1bc9080f, SOURCE ONLY.
No original O/A/K/group/field map, universe, numeric option or final NOS premise changes.
-/
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.TensorTriple
import ZInQKernel.Contrib.CloudR2NOS.Descent.Assembly
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.AbelianProperties

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective
open TensorCofaces TensorNerve

variable {R : Type u} [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R']
  [Module.FaithfullyFlat R R']
  (V : (Base R).Opens) (G : Grp (Over (Cover R'))) (A : Grp (Over V.toScheme))
  (e : (Over.pullback ((baseMap R R') ⁻¹ᵁ V).ι).mapGrp.obj G ≅
    (Over.pullback ((baseMap R R') ∣_ V)).mapGrp.obj A)
  [Etale (baseMap R R')] (c : Base R)
  [Mono ((baseMap R R').fiberToSpecResidueField c)]
  (hV : ∀ z : Base R, z ∉ V → z = c)

/-- The module-line cocycle type on the ACTUAL computed tensor nerve.
    It is a native sheaf isomorphism/canonical pullback equation, not a
    substitute OModulePresheaf or an assumed scheme descent datum. -/
def ActualLineCocycle (M : G.X.left.Modules)
    (ψ : (Scheme.Modules.pullback (projection1 (R := R) R' G)).obj M ≅
      (Scheme.Modules.pullback (projection2 R' V G A e c hV)).obj M) : Prop :=
  ((Scheme.Modules.pullbackCongr (nerve_eq1 (R := R) R' G)).app M).symm ≪≫
    ((Scheme.Modules.pullbackComp (chart12 (R := R) R' G) (projection1 (R := R) R' G)).app M).symm ≪≫
    (Scheme.Modules.pullback (chart12 (R := R) R' G)).mapIso ψ ≪≫
    ((Scheme.Modules.pullbackComp (chart12 (R := R) R' G) (projection2 R' V G A e c hV)).app M) ≪≫
    ((Scheme.Modules.pullbackCongr (nerve_eq2 R' V G A e c hV)).app M) ≪≫
    ((Scheme.Modules.pullbackComp (chart23 R' V G A e c hV) (projection1 (R := R) R' G)).app M).symm ≪≫
    (Scheme.Modules.pullback (chart23 R' V G A e c hV)).mapIso ψ ≪≫
    ((Scheme.Modules.pullbackComp (chart23 R' V G A e c hV) (projection2 R' V G A e c hV)).app M) ≪≫
    ((Scheme.Modules.pullbackCongr (nerve_eq3 R' V G A e c hV)).app M).symm =
  ((Scheme.Modules.pullbackComp (chart13 (R := R) R' G) (projection1 (R := R) R' G)).app M).symm ≪≫
    (Scheme.Modules.pullback (chart13 (R := R) R' G)).mapIso ψ ≪≫
    ((Scheme.Modules.pullbackComp (chart13 (R := R) R' G) (projection2 R' V G A e c hV)).app M)

/-- Actual EFFECTIVE descended scheme. All scheme projections/cartesian
    squares/cocycle equations are constructed from the existing intermediate
    native line input; no descended line is exported or assumed by Q0. -/
theorem exists_effective_scheme_from_actual_line
    (M : G.X.left.Modules)
    (hM : ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.IsInvertible M)
    (hVA : ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.ClosedImmersionBySections M G.X.hom)
    (ψ : (Scheme.Modules.pullback (projection1 (R := R) R' G)).obj M ≅
      (Scheme.Modules.pullback (projection2 R' V G A e c hV)).obj M)
    (hψ : ActualLineCocycle R' V G A e c hV M ψ) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Base R) (q : G.X.left ⟶ X),
      IsPullback q G.X.hom f (baseMap R R') ∧
      projection1 (R := R) R' G ≫ q = projection2 R' V G A e c hV ≫ q := by
  obtain ⟨X, f, q, hq, hco⟩ :=
    ZInQ.Contrib.CloudR2NOS.Descent.exists_descent_scheme_of_faithfullyFlat_of_cocycle
    R' G.X.left G.X.hom M hVA
    (model2 (R := R) R' G) (structure2 (R := R) R' G)
    (projection1 (R := R) R' G) (projection2 R' V G A e c hV)
    (cartesian1 (R := R) R' G) (cartesian2 R' V G A e c hV)
    (model3 (R := R) R' G) (structure3 (R := R) R' G)
    (chart12 (R := R) R' G) (chart13 (R := R) R' G) (chart23 R' V G A e c hV)
    (cartesian12 (R := R) R' G) (cartesian13 (R := R) R' G) (cartesian23 R' V G A e c hV)
    (nerve_eq1 (R := R) R' G) (nerve_eq2 R' V G A e c hV) (nerve_eq3 R' V G A e c hV) ψ hψ
  exact ⟨X, f, q, hq, hco⟩

#print axioms exists_effective_scheme_from_actual_line

end ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective

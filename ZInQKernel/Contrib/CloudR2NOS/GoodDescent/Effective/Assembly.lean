/-
NEW H5 SOURCE EDITION — 2026-11-17, Q0 scheme-only output integration.
Previous route(c) Assembly a7aa723e948d550acf9118e2df8b5cb539168c415369a34cac8e06e04633fbae
stays frozen as history. ProjConstruction now exports only X/f/q/hq/hco
from C4's Q0. The ONLY change to this proof body is its obtain pattern:
drop the three UNUSED L/hL/hqL slots. This theorem's ENTIRE public written
TYPE, its existing line INPUTS and its native GROUP/cartesian/proper/smooth/
effectiveness outputs are BYTE-IDENTICAL to the route(c) edition.
The historical line predicates remain bound. Q0's Source-only producer and
its leaf/dictionary/default/native checks remain C6/Parent obligations;
no old FLT effective-descent import or descended-line witness is reintroduced.
The notices below are retained historical attribution/context, not a new pass.
-/
/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

Direct effective Proj + native GROUP + proper/smooth assembly on the SAME
actually constructed scheme. No effective quotient, hdesc, group-law,
IsMonHom or desired properness Fact is supplied. The actual extended
invertible very-ample M and native module-line cocycle are ONLY explicit
intermediate producer inputs until lane6 supplies them; never final NOS
assumptions. Geometric connectedness is obtained separately from the
actual original generic and closed fibres, not a stage-GC hypothesis.
-/
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.ProjConstruction
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.GroupConstruction
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.DatumEffective
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.GeometricCover

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective
open TensorCofaces TensorNerve

/-- Actually CONSTRUCT the effective proper smooth native group and its
    cartesian GROUP iso from the actual ordinary-pointed-étale datum and
    the explicit intermediate line supplier. No new stage-GC premise. -/
theorem exists_effective_proper_smooth_group_from_actual_line
    {R : Type u} [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R']
    [Module.FaithfullyFlat R R'] (V : (Base R).Opens)
    (G : Grp (Over (Cover R'))) (A : Grp (Over V.toScheme))
    (e : (Over.pullback ((baseMap R R') ⁻¹ᵁ V).ι).mapGrp.obj G ≅
      (Over.pullback ((baseMap R R') ∣_ V)).mapGrp.obj A)
    [Etale (baseMap R R')] (c : Base R)
    [Mono ((baseMap R R').fiberToSpecResidueField c)]
    (hV : ∀ z : Base R, z ∉ V → z = c) [Smooth G.X.hom] [IsProper G.X.hom]
    (M : G.X.left.Modules)
    (hM : ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.IsInvertible M)
    (hVA : ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.ClosedImmersionBySections M G.X.hom)
    (ψ : (Scheme.Modules.pullback (projection1 (R := R) R' G)).obj M ≅
      (Scheme.Modules.pullback (projection2 R' V G A e c hV)).obj M)
    (hψ : ActualLineCocycle R' V G A e c hV M ψ) :
    ∃ (D : Grp (Over (Base R))) (q : G.X.left ⟶ D.X.left)
      (i : G ≅ (Over.pullback (baseMap R R')).mapGrp.obj D),
      IsPullback q G.X.hom D.X.hom (baseMap R R') ∧
      i.hom.hom.hom.left ≫ pullback.fst D.X.hom (baseMap R R') = q ∧
      projection1 (R := R) R' G ≫ q = projection2 R' V G A e c hV ≫ q ∧
      Smooth D.X.hom ∧ IsProper D.X.hom ∧
      (schemeDatumOfGroupIso (baseMap R R') V G A e c hV).IsEffective := by
  obtain ⟨X, f, q, hq, hco⟩ :=
    exists_effective_scheme_from_actual_line R' V G A e c hV M hM hVA ψ hψ
  obtain ⟨LG, i, hi, hS, hP⟩ :=
    exists_proper_smooth_group_on_effective_tensor_scheme R' V G A e c hV X f q hq hco
  let D : Grp (Over (Base R)) := groupOfRelativeLaw LG
  exact ⟨D, q, i, hq, hi, hco, hS, hP,
    datum_effective_of_tensor_coequalizer R' V G A e c hV X f q hq hco⟩

#print axioms exists_effective_proper_smooth_group_from_actual_line

end ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective

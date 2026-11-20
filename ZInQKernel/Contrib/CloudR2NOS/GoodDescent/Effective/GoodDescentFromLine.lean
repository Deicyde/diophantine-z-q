/-
NEW H5 SOURCE EDITION — 2026-11-17, closedImmersionBySections-free cut.
Historical GoodDescentFromLine body SHA256
 18ca2cf99b50a78af6637050a0c40ff17f1b25b7e76511be4a844518d61338e1
is retained frozen as history. The ENTIRE written public TYPE of
hasGoodReduction_from_actual_line is byte-identical to that historical source.
The ONLY proof-body change removes hline from the Assembly-output obtain pattern.
No original O/A/K/group map, input, universe or public conclusion is altered.
The USED FLT effective-descent import remains a labelled upstream C4 gate;
bound historical line predicates remain in the identical public type.
This is a SOURCE-only new edition, NOT a zero-FLT closure/native/default pass.
-/
/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

Original-O/actual-A good-model INTERMEDIATE constructor. The effective
scheme, group, original-K generic GROUP iso and abelian-scheme properties
are constructed on ONE output. The actual native line inputs remain
explicit until Lane6 supplies their proofs; THIS IS NOT a final NOS theorem
and these inputs are not authorized as new final NOS assumptions.
The cover is ordinary-pointed étale, not a ramified DVR replacement.
-/
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.Assembly
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.GenericGroupOutput
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.OriginalFieldOutput

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective
open TensorCofaces TensorNerve

/-- Construct the exact original `HasGoodReduction` model, INCLUDING the
    original-K GROUP-object iso, from the actual ordinary-pointed-étale
    model/datum and explicit INTERMEDIATE line input. Nothing is changed
    in the original definition or statement; M supply itself is not proved
    by this constructor, and this is not offered as the NOS proof. -/
theorem hasGoodReduction_from_actual_line
    {K : Type u} [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (B : Type u) [CommRing B] [Algebra O B] [Module.FaithfullyFlat O B]
    (V : (Base O).Opens) (iV : V.toScheme ≅ Spec (CommRingCat.of K))
    (hiV : iV.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap O K)) = V.ι)
    (hV : ∀ z : Base O, z ∉ V → z = IsLocalRing.closedPoint O)
    (G : Grp (Over (Cover B))) [PkgI2.IsAbelianScheme G]
    (A : Grp (Over (Spec (CommRingCat.of K))))
    (e : (Over.pullback ((baseMap O B) ⁻¹ᵁ V).ι).mapGrp.obj G ≅
      (Over.pullback ((baseMap O B) ∣_ V)).mapGrp.obj ((Over.pullback iV.hom).mapGrp.obj A))
    [Etale (baseMap O B)] [Mono ((baseMap O B).fiberToSpecResidueField (IsLocalRing.closedPoint O))]
    (M : G.X.left.Modules)
    (hM : ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.IsInvertible M)
    (hVA : ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.ClosedImmersionBySections M G.X.hom)
    (ψ : (Scheme.Modules.pullback (projection1 (R := O) B G)).obj M ≅
      (Scheme.Modules.pullback (projection2 B V G ((Over.pullback iV.hom).mapGrp.obj A) e
        (IsLocalRing.closedPoint O) hV)).obj M)
    (hψ : ActualLineCocycle B V G ((Over.pullback iV.hom).mapGrp.obj A) e (IsLocalRing.closedPoint O) hV M ψ) :
    PkgI2.HasGoodReduction A O := by
  let A₀ := (Over.pullback iV.hom).mapGrp.obj A
  haveI : Smooth G.X.hom := PkgI2.IsAbelianScheme.smooth
  haveI : IsProper G.X.hom := PkgI2.IsAbelianScheme.proper
  haveI : GeometricallyConnected G.X.hom := PkgI2.IsAbelianScheme.geomConnected
  obtain ⟨D, q, iG, hq, hiG, hco, hS, hP, hδ⟩ :=
    exists_effective_proper_smooth_group_from_actual_line B V G A₀ e (IsLocalRing.closedPoint O) hV M hM hVA ψ hψ
  obtain ⟨E⟩ := exists_genericGroupIso_on_effective_output B V G A₀ e (IsLocalRing.closedPoint O) hV D q hq iG hiG hco
  let iK := originalFieldGroupIso_of_open V iV hiV D A E
  haveI : Surjective (baseMap O B) := by
    constructor
    exact PrimeSpectrum.comap_surjective_of_faithfullyFlat
  have hGC : GeometricallyConnected D.X.hom := geometricallyConnected_of_surjective_isPullback hq
  exact ⟨D, ⟨hP, hS, hGC⟩, ⟨iK⟩⟩

#print axioms hasGoodReduction_from_actual_line

end ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective

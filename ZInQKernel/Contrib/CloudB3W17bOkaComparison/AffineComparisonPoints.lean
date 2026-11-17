import ZInQKernel.Contrib.CloudB3W17bOkaComparison.AffineComparisonConstants
import ZInQKernel.Contrib.CloudB3W17bOkaComparison.AffineChartPoints
import ZInQKernel.Contrib.CloudB3W17bOkaComparison.IntrinsicResidueNaturality

/-!
# Original native affine points induced by the genuine analytic comparison

The point is constructed from the ACTUAL analytic stalk residue maps proved
from the real local models in IntrinsicResidueCore. Its original complex
constants, underlying scheme point and EVERY regular value are proved from the
true over-base square and Γ–Spec naturality. No carrier/model compatibility
structure, GAGA or algebraic F/H witness is assumed.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite ComplexAnalytic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bOkaComparison

/-- The actual Γ–Spec point of a genuine analytic space is its actual residue evaluation. -/
theorem analytic_toGammaSpec_base (Z : AnalyticSpace.{0}) (x : Z) :
    Z.toLocallyRingedSpace.toΓSpec.base x =
      Spec.map (CommRingCat.ofHom (intrinsicEval Z (U := ⊤) x trivial)) (IsLocalRing.closedPoint ℂ) := by
  change PrimeSpectrum.comap (Z.presheaf.Γgerm x).hom
      (IsLocalRing.closedPoint (Z.presheaf.stalk x)) =
    PrimeSpectrum.comap ((intrinsicStalkEval Z x).comp (Z.presheaf.Γgerm x).hom) (IsLocalRing.closedPoint ℂ)
  rw [PrimeSpectrum.comap_comp_apply, IsLocalRing.comap_closedPoint (intrinsicStalkEval Z x)]

variable (Y : Over (Spec (CommRingCat.of ℂ))) (e : ℕ) [SmoothOfRelativeDimension e Y.hom]
variable (q : ComplexPoint Y) (Z : AnalyticSpace.{0})

local instance comparisonAffine : IsAffine (actualEtaleNativeScheme Y e q).left :=
  (actualEtaleDatum Y e q).isAffine

local instance comparisonComplexAlgebra : Algebra ℂ Γ((actualEtaleNativeScheme Y e q).left, ⊤) :=
  (actualEtaleDatum Y e q).coordinateRingComplexAlgebra

variable (f : Z.toLocallyRingedSpace ⟶ (actualEtaleNativeScheme Y e q).left.toLocallyRingedSpace)
variable (hbase : f ≫ (overULift (actualEtaleNativeScheme Y e q)).hom.toLRSHom = Z.toSpecℂ)

/-- Actual complex-valued affine Γ coordinates of the genuine comparison's actual point. -/
def affineComparisonAlgHom (x : Z) : Γ((actualEtaleNativeScheme Y e q).left, ⊤) →ₐ[ℂ] ℂ where
  toRingHom := (intrinsicEval Z (U := ⊤) x trivial).comp (LocallyRingedSpace.Γ.map f.op).hom
  commutes' c :=
    (congrArg (intrinsicEval Z (U := ⊤) x trivial) (affineComparison_gamma_constants Y e q Z f hbase c)).trans
      (intrinsicEval_const Z x c)

/-- The ORIGINAL native affine point supplied by the true analytic comparison's actual Γ values. -/
def affineComparisonPoint (x : Z) : ComplexPoint (actualEtaleNativeScheme Y e q) :=
  (actualEtaleDatum Y e q).pointAlgHomHomeomorph.symm (affineComparisonAlgHom Y e q Z f hbase x)

/-- EVERY native regular value is the actual analytic comparison value, not merely coordinates. -/
theorem affineComparisonPoint_eval (x : Z) (r : Γ((actualEtaleNativeScheme Y e q).left, ⊤)) :
    Point.evaluate ⊤ r (affineComparisonPoint Y e q Z f hbase x) =
      intrinsicEval Z (U := ⊤) x trivial ((LocallyRingedSpace.Γ.map f.op).hom r) :=
  ((actualEtaleDatum Y e q).pointAlgHomHomeomorph_apply
    (affineComparisonPoint Y e q Z f hbase x) r).symm.trans
      (congrArg (fun a : Γ((actualEtaleNativeScheme Y e q).left, ⊤) →ₐ[ℂ] ℂ => a r)
        ((actualEtaleDatum Y e q).pointAlgHomHomeomorph.apply_symm_apply
          (affineComparisonAlgHom Y e q Z f hbase x)))

/-- The ORIGINAL underlying scheme point is exactly the genuine comparison's actual base point. -/
theorem affineComparisonPoint_underlying (x : Z) :
    (affineComparisonPoint Y e q Z f hbase x).underlying = f.base x := by
  let V := actualEtaleNativeScheme Y e q
  let E := asIso V.left.toSpecΓ
  let Q := affineComparisonPoint Y e q Z f hbase x
  let a := affineComparisonAlgHom Y e q Z f hbase x
  let v := intrinsicEval Z (U := ⊤) x trivial
  let μ := (LocallyRingedSpace.Γ.map f.op).hom
  have hs : Spec.map (CommRingCat.ofHom v) ≫ Spec.map (CommRingCat.ofHom μ) =
      Spec.map (CommRingCat.ofHom a.toRingHom) := by
    rw [← Spec.map_comp]
    rfl
  have hsp := congrArg (fun g : Spec (CommRingCat.of ℂ) ⟶ Spec Γ(V.left, ⊤) =>
      g (IsLocalRing.closedPoint ℂ)) hs
  have hq : Spec.map (CommRingCat.ofHom a.toRingHom) (IsLocalRing.closedPoint ℂ) =
      E.hom Q.underlying :=
    (congrArg (fun b : Γ(V.left, ⊤) →ₐ[ℂ] ℂ =>
        Spec.map (CommRingCat.ofHom b.toRingHom) (IsLocalRing.closedPoint ℂ))
      ((actualEtaleDatum Y e q).pointAlgHomHomeomorph.apply_symm_apply a)).symm.trans
        (congrArg (fun g : Spec (CommRingCat.of ℂ) ⟶ Spec Γ(V.left, ⊤) =>
          g (IsLocalRing.closedPoint ℂ)) (actualEtalePointAlgHom_spec Y e q Q))
  have hn : E.hom (f.base x) = Spec.map (CommRingCat.ofHom μ) (Z.toLocallyRingedSpace.toΓSpec.base x) :=
    congrArg (fun g : Z.toLocallyRingedSpace ⟶ (Spec Γ(V.left, ⊤)).toLocallyRingedSpace =>
      g.base x) (LocallyRingedSpace.toΓSpec_naturality f)
  have heq : E.hom (f.base x) = E.hom Q.underlying :=
    hn.trans ((congrArg (fun t => Spec.map (CommRingCat.ofHom μ) t)
      (analytic_toGammaSpec_base Z x)).trans (hsp.trans hq))
  have hinv (t : V.left) : E.inv (E.hom t) = t :=
    congrArg (fun g : V.left ⟶ V.left => g t) E.hom_inv_id
  exact ((hinv (f.base x)).symm.trans
    ((congrArg (fun t => E.inv t) heq).trans (hinv Q.underlying))).symm

end ZInQ.Contrib.CloudB3W17bOkaComparison

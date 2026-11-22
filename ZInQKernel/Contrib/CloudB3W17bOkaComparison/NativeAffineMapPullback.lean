import ZInQKernel.Contrib.CloudB3W17bOkaComparison.NativeRegularPullback

/-!
# Genuine affine regular-ring pullback of the original native F in a fixed canonical source chart

Both affine neighbourhoods and all their regular functions are the actual
Hodge algebraic étale data.  F is only the original native manifold map.
Every target regular-ring value is computed at its actual open-subscheme
point and assembled into one actual Oka ring homomorphism, with complex
constant compatibility.  No algebraic F/H or GAGA premise is assumed.
-/

open scoped Manifold ContDiff Topology
open CategoryTheory AlgebraicGeometry TopologicalSpace Set

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bOkaComparison

variable (X Y : Over (Spec (CommRingCat.of ℂ))) (d e : ℕ)
variable [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension e Y.hom]
variable (F : ComplexPoint X → ComplexPoint Y)
variable (hF : MDifferentiable 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin e → ℂ) F) (p : ComplexPoint X)

/-- The actual canonical target étale affine neighbourhood at its specified native point. -/
abbrev nativeMapTargetDatum (Y' : Over (Spec (CommRingCat.of ℂ))) (e' : ℕ)
    [SmoothOfRelativeDimension e' Y'.hom] (q : ComplexPoint Y') := actualEtaleDatum Y' e' q

/-- Its genuine ambient open, retaining the same regular-section ring. -/
abbrev nativeMapTargetOpen (Y' : Over (Spec (CommRingCat.of ℂ))) (e' : ℕ)
    [SmoothOfRelativeDimension e' Y'.hom] (q : ComplexPoint Y') :=
  (nativeMapTargetDatum Y' e' q).ambientCoordinateOpen

/-- The fixed source chart shrunk to the genuine target affine domain. -/
abbrev nativeMapAffineDomain : Opens (Fin d → ℂ) :=
  nativeMapRegularOpen X Y d e F hF p (nativeMapTargetOpen Y e (F p))

local instance targetComplexAlgebra :
    Algebra ℂ Γ((nativeMapTargetDatum Y e (F p)).neighborhood.toScheme, ⊤) :=
  (nativeMapTargetDatum Y e (F p)).coordinateRingComplexAlgebra

/-- The actual target open-subscheme point, not an arbitrary affine-coordinate tuple. -/
def nativeMapTargetPoint (w : nativeMapAffineDomain X Y d e F hF p) :
    ComplexPoint (ComplexPoint.openScheme Y (nativeMapTargetDatum Y e (F p)).neighborhood) :=
  (ComplexPoint.openHomeomorph Y (nativeMapTargetDatum Y e (F p)).neighborhood).symm
    ⟨F ((nativeMapSourceChart X d p).symm w.1), by
      have h := w.2.2
      simpa only [nativeMapTargetOpen, LocalEtaleCoordinates.ambientCoordinateOpen,
        Scheme.Opens.ι_image_top, Set.mem_preimage] using h⟩

/-- The actual affine evaluation is the ambient regular pullback already proved analytic. -/
theorem nativeMapTargetPoint_eval
    (r : Γ((nativeMapTargetDatum Y e (F p)).neighborhood.toScheme, ⊤))
    (w : nativeMapAffineDomain X Y d e F hF p) :
    (nativeMapTargetDatum Y e (F p)).pointAlgHomHomeomorph
      (nativeMapTargetPoint X Y d e F hF p w) r =
      Point.evaluate (nativeMapTargetOpen Y e (F p))
        (((nativeMapTargetDatum Y e (F p)).neighborhood.ι.appIso ⊤).inv r)
          (F ((nativeMapSourceChart X d p).symm w.1)) := by
  let D := nativeMapTargetDatum Y e (F p)
  let q := nativeMapTargetPoint X Y d e F hF p w
  have hq : Point.map (ComplexPoint.openInclusion Y D.neighborhood) q =
      F ((nativeMapSourceChart X d p).symm w.1) :=
    congrArg Subtype.val ((ComplexPoint.openHomeomorph Y D.neighborhood).apply_symm_apply _)
  exact (D.pointAlgHomHomeomorph_apply q r).trans
    ((ComplexPoint.evaluate_openEquiv Y D.neighborhood r q).symm.trans
      (congrArg (Point.evaluate D.ambientCoordinateOpen ((D.neighborhood.ι.appIso ⊤).inv r)) hq))

/-- The actual Γ(target affine,⊤) → OkaRing(source chart) map determined by native F. -/
def nativeMapAffineGammaPullback :
    Γ((nativeMapTargetDatum Y e (F p)).neighborhood.toScheme, ⊤) →+*
      OkaRing (nativeMapAffineDomain X Y d e F hF p) where
  toFun r := OkaRing.mk
    (fun w => (nativeMapTargetDatum Y e (F p)).pointAlgHomHomeomorph
      (nativeMapTargetPoint X Y d e F hF p w) r)
    (by
      have hfun : (fun w : nativeMapAffineDomain X Y d e F hF p =>
          (nativeMapTargetDatum Y e (F p)).pointAlgHomHomeomorph
            (nativeMapTargetPoint X Y d e F hF p w) r) =
          fun w : nativeMapAffineDomain X Y d e F hF p =>
            Point.evaluate (nativeMapTargetOpen Y e (F p))
              (((nativeMapTargetDatum Y e (F p)).neighborhood.ι.appIso ⊤).inv r)
                (F ((nativeMapSourceChart X d p).symm w.1)) :=
        funext (nativeMapTargetPoint_eval X Y d e F hF p r)
      rw [hfun]
      exact (nativeMapRegularSection X Y d e F hF p (nativeMapTargetOpen Y e (F p))
        (((nativeMapTargetDatum Y e (F p)).neighborhood.ι.appIso ⊤).inv r)).2)
  map_one' := by
    apply OkaRing.ext
    funext w
    exact map_one _
  map_mul' r s := by
    apply OkaRing.ext
    funext w
    exact map_mul _ r s
  map_zero' := by
    apply OkaRing.ext
    funext w
    exact map_zero _
  map_add' r s := by
    apply OkaRing.ext
    funext w
    exact map_add _ r s

/-- This genuine regular-ring pullback preserves the actual complex constants. -/
theorem nativeMapAffineGammaPullback_C (c : ℂ) :
    nativeMapAffineGammaPullback X Y d e F hF p
      ((nativeMapTargetDatum Y e (F p)).coordinateRingHomOnOpen (MvPolynomial.C c)) =
      algebraMap ℂ (OkaRing (nativeMapAffineDomain X Y d e F hF p)) c := by
  apply OkaRing.ext
  funext w
  exact ((nativeMapTargetDatum Y e (F p)).pointAlgHomHomeomorph
    (nativeMapTargetPoint X Y d e F hF p w)).commutes c

end ZInQ.Contrib.CloudB3W17bOkaComparison

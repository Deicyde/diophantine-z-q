import ZInQKernel.Contrib.CloudB3W17bOkaComparison.AffinePullbackLaw

/-!
# Actual affine Γ–Spec LRS morphisms from genuine Oka sources

The constructors below use the same actual native affine neighbourhoods and the
same genuine Oka-source global rings as the analytification bridge.  They are
factored before the global analytification import so their LRS and Γ laws can
be independently source-built while the canonical UP port is being rebuilt.
No map/model compatibility witness is assumed.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite ComplexAnalytic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bOkaComparison

/-- Actual holomorphic sections restricted to the same Oka-open source's global ring. -/
def euclideanSectionToGlobal (n : ℕ) (U : Opens (_root_.complexAffineSpace n)) :
    OkaRing U →+* (euclideanOpen n U).presheaf.obj (op ⊤) :=
  ((_root_.complexAffineSpace n).presheaf.map
    (homOfLE (Opens.isOpenEmbedding_obj_top U).le).op).hom

/-- The true restricted constants are the Oka-open source's actual complex structure. -/
theorem euclideanSectionToGlobal_C (n : ℕ) (U : Opens (_root_.complexAffineSpace n)) (c : ℂ) :
    euclideanSectionToGlobal n U (algebraMap ℂ (OkaRing U) c) = (euclideanOpen n U).algebraMap c := rfl

variable (Y : Over (Spec (CommRingCat.of ℂ))) (e : ℕ) [SmoothOfRelativeDimension e Y.hom]
variable (q : ComplexPoint Y) (Z : AnalyticSpace)

local instance affineTarget : IsAffine (actualEtaleNativeScheme Y e q).left :=
  (actualEtaleDatum Y e q).isAffine

variable (μ : Γ((actualEtaleNativeScheme Y e q).left, ⊤) →+* Z.presheaf.obj (op ⊤))
variable (hμ : ∀ c, μ (actualEtaleNativeConst Y e q c) = Z.algebraMap c)

/-- The real affine Γ–Spec LRS morphism, with original native target scheme. -/
def actualAffineGammaLRS : Z.toLocallyRingedSpace ⟶
    (actualEtaleNativeScheme Y e q).left.toLocallyRingedSpace :=
  Z.toLocallyRingedSpace.toSpecOfAlgMap μ ≫
    (asIso (actualEtaleNativeScheme Y e q).left.toSpecΓ).inv.toLRSHom

/-- The actual affine LRS morphism is over Oka's real lifted complex base. -/
theorem actualAffineGammaLRS_over (hμ : ∀ c, μ (actualEtaleNativeConst Y e q c) = Z.algebraMap c) :
    actualAffineGammaLRS Y e q Z μ ≫ (overULift (actualEtaleNativeScheme Y e q)).hom.toLRSHom =
      Z.toSpecℂ := by
  have h := congrArg Scheme.Hom.toLRSHom (actualEtaleFromSpecΓ_overULift Y e q)
  have hc : μ.comp (uliftAlgMap (actualEtaleNativeConst Y e q)) = uliftAlgMap Z.algebraMap :=
    RingHom.ext fun c => hμ c.down
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => Z.toLocallyRingedSpace.toSpecOfAlgMap μ ≫ f) h).trans
      ((toSpecAlg_comp Z.toLocallyRingedSpace μ (uliftAlgMap (actualEtaleNativeConst Y e q))).trans
        (congrArg Z.toLocallyRingedSpace.toSpecOfAlgMap hc)))

/-- The genuine morphism over the exact LRS base required by Oka representability. -/
def actualAffineGammaOver : AnalyticSpace.toOverSpec.obj Z ⟶
    Over.mk (overULift (actualEtaleNativeScheme Y e q)).hom.toLRSHom :=
  Over.homMk (actualAffineGammaLRS Y e q Z μ) (actualAffineGammaLRS_over Y e q Z μ hμ)

/-- All actual target regular sections are pulled back by precisely the supplied real μ. -/
theorem actualAffineGammaLRS_gamma_pullback :
    (LocallyRingedSpace.Γ.map (actualAffineGammaLRS Y e q Z μ).op).hom = μ :=
  affine_lrs_gamma_pullback (actualEtaleNativeScheme Y e q).left Z.toLocallyRingedSpace μ

end ZInQ.Contrib.CloudB3W17bOkaComparison

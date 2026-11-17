import ZInQKernel.Contrib.CloudB3W17bOkaComparison.GermSheafMaps
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.AlgebraicGeometry.GammaSpecAdjunction

/-!
# Actual residue evaluation and the Γ–Spec point dictionary on an open Oka source

Evaluation is obtained from the real Oka germ-colimit map through the actual
restriction stalk isomorphism.  It is proved local and onto, and its global
section values identify the actual Γ–Spec base map.  No point-model/sheaf
compatibility structure is supplied as a hypothesis.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bOkaComparison

variable {ι : Type} [Fintype ι]
variable (U : Opens (complexSpace ι)) (w : (complexSpace ι).restrict U.isOpenEmbedding)

/-- The genuine evaluation map on the stalk of the actual open Oka source. -/
def openOkaGermEval : ((complexSpace ι).restrict U.isOpenEmbedding).presheaf.stalk w →+* ℂ :=
  (okaGermEvalC w.1).hom.comp ((complexSpace ι).restrictStalkIso U.isOpenEmbedding w).hom.hom

/-- The actual ambient open indexing a section on the restricted Oka source. -/
def openOkaSectionImage
    (V : Opens ((complexSpace ι).restrict U.isOpenEmbedding)) : Opens (ι → ℂ) :=
  LocallyRingedSpace.imOpen U V

/-- A point of a source section's domain is in its actual ambient image open. -/
theorem openOkaMemSectionImage
    (V : Opens ((complexSpace ι).restrict U.isOpenEmbedding)) (hw : w ∈ V) :
    w.1 ∈ openOkaSectionImage U V := ⟨w, hw, rfl⟩

/-- The actual germ evaluation is the value of its actual holomorphic representative. -/
theorem openOkaGermEval_germ
    (V : Opens ((complexSpace ι).restrict U.isOpenEmbedding)) (hw : w ∈ V)
    (s : ((complexSpace ι).restrict U.isOpenEmbedding).presheaf.obj (op V)) :
    openOkaGermEval U w
      (((complexSpace ι).restrict U.isOpenEmbedding).presheaf.germ V w hw s) =
        OkaRing.evalHom (U := openOkaSectionImage U V) (x := w.1)
          (openOkaMemSectionImage U w V hw) s :=
  (congrArg (okaGermEvalC w.1).hom
    ((complexSpace ι).restrictStalkIso_hom_eq_germ_apply U.isOpenEmbedding V w hw s)).trans
      (okaGermEvalC_germ w.1 (openOkaSectionImage U V) (openOkaMemSectionImage U w V hw) s)

/-- This actual residue-value map really is a local ring homomorphism. -/
instance openOkaGermEval_isLocalHom : IsLocalHom (openOkaGermEval U w) := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨V, hw, s, rfl⟩ := ((complexSpace ι).restrict U.isOpenEmbedding).presheaf.exists_germ_eq a
  have hne : OkaRing.evalHom (U := openOkaSectionImage U V) (x := w.1)
      (openOkaMemSectionImage U w V hw) s ≠ 0 :=
    isUnit_iff_ne_zero.mp ((congrArg IsUnit (openOkaGermEval_germ U w V hw s)).mp ha)
  have hu := isUnit_okaGerm (U := openOkaSectionImage U V)
    (openOkaMemSectionImage U w V hw) s hne
  have hi := (complexSpace ι).restrictStalkIso_inv_eq_germ_apply U.isOpenEmbedding V w hw s
  exact (congrArg IsUnit hi).mp
    (hu.map ((complexSpace ι).restrictStalkIso U.isOpenEmbedding w).inv.hom)

/-- The same genuine constant sections, restricted to the actual open source. -/
def openOkaConstants : ℂ →+* ((complexSpace ι).restrict U.isOpenEmbedding).presheaf.obj (op ⊤) :=
  (complexSpace ι).resAlgMap (algebraMap ℂ (OkaRing (⊤ : Opens (ι → ℂ)))) U

/-- Actual stalk constants have their literal complex values. -/
theorem openOkaGermEval_const (c : ℂ) :
    openOkaGermEval U w
      (((complexSpace ι).restrict U.isOpenEmbedding).presheaf.Γgerm w (openOkaConstants U c)) = c :=
  (openOkaGermEval_germ U w ⊤ trivial (openOkaConstants U c)).trans rfl

/-- The genuine residue evaluation is surjective, not just nonzero or value-preserving. -/
theorem openOkaGermEval_surjective : Function.Surjective (openOkaGermEval U w) :=
  fun c => ⟨((complexSpace ι).restrict U.isOpenEmbedding).presheaf.Γgerm w (openOkaConstants U c),
    openOkaGermEval_const U w c⟩

/-- The actual values of global sections, as one ring homomorphism. -/
def openOkaGlobalValue :
    ((complexSpace ι).restrict U.isOpenEmbedding).presheaf.obj (op ⊤) →+* ℂ :=
  (openOkaGermEval U w).comp (((complexSpace ι).restrict U.isOpenEmbedding).presheaf.Γgerm w).hom

/-- The actual Γ–Spec base map is the spectrum of this genuine residue-value homomorphism. -/
theorem openOka_toΓSpec_base :
    (((complexSpace ι).restrict U.isOpenEmbedding).toΓSpec).base w =
      (Spec.map (CommRingCat.ofHom (openOkaGlobalValue U w))) (IsLocalRing.closedPoint ℂ) := by
  change PrimeSpectrum.comap
      (((complexSpace ι).restrict U.isOpenEmbedding).presheaf.Γgerm w).hom
        (IsLocalRing.closedPoint (((complexSpace ι).restrict U.isOpenEmbedding).presheaf.stalk w)) =
    PrimeSpectrum.comap (openOkaGlobalValue U w) (IsLocalRing.closedPoint ℂ)
  rw [openOkaGlobalValue, PrimeSpectrum.comap_comp_apply,
    IsLocalRing.comap_closedPoint (openOkaGermEval U w)]

end ZInQ.Contrib.CloudB3W17bOkaComparison

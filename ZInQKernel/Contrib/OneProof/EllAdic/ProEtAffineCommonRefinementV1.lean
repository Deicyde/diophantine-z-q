import ZInQKernel.Contrib.OneProof.EllAdic.ProEtAffineSingletonReceiverV1
import ZInQKernel.Contrib.OneProof.EllAdic.WeaklyEtaleTensorRefinementV1

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

namespace RC53.EllAdic

universe u

/-- Refine countably many affine, surjective, weakly étale morphisms by a
single actual covering arrow. The factoring arrows are spectra of the
canonical factor maps into the quotient tensor colimit. -/
theorem proEt_affine_singleton_common_refinement
    {S : Scheme.{u}} (U : S.ProEt) [IsAffine U.left]
    (V : ℕ → S.ProEt) [∀ n, IsAffine (V n).left]
    (q : ∀ n, V n ⟶ U)
    (hw : ∀ n, WeaklyEtale (q n).left) (hs : ∀ n, Surjective (q n).left) :
    ∃ (W : S.ProEt) (p : W ⟶ U) (r : ∀ n, W ⟶ V n),
      Presieve.singleton p ∈ Scheme.ProEt.precoverage S U ∧ ∀ n, r n ≫ q n = p := by
  let A := Γ(U.left, ⊤)
  let C (n : ℕ) : CommAlgCat.{u} A :=
    let : Algebra A Γ((V n).left, ⊤) := (q n).left.appTop.hom.toAlgebra
    CommAlgCat.of A Γ((V n).left, ⊤)
  let : ∀ n : ℕ, Algebra (↑A : Type u) (↑(C n) : Type u) := fun n => (C n).algebra
  have hCw (n : ℕ) : WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap A (C n)))) := by
    let g : (V n).left ⟶ U.left := (q n).left
    have hg : WeaklyEtale (Spec.map g.appTop) :=
      (MorphismProperty.arrow_mk_iso_iff (@WeaklyEtale : MorphismProperty Scheme.{u})
        (arrowIsoSpecΓOfIsAffine g)).1 (hw n)
    exact hg
  have hCf (n : ℕ) : Module.FaithfullyFlat A (C n) := by
    let g : (V n).left ⟶ U.left := (q n).left
    have hg : Surjective (Spec.map g.appTop) :=
      (MorphismProperty.arrow_mk_iso_iff (@Surjective : MorphismProperty Scheme.{u})
        (arrowIsoSpecΓOfIsAffine g)).1 (hs n)
    have hf : Flat (Spec.map g.appTop) := (hCw n).flat
    have hfg : g.appTop.hom.FaithfullyFlat :=
      (flat_and_surjective_SpecMap_iff g.appTop).1 ⟨hf, hg⟩
    change Module.FaithfullyFlat A (C n) at hfg
    exact hfg
  let B := CountableTensorRefinement.limit C
  let i (n : ℕ) : AffineFactorToLimit (q n).left B :=
    (CountableTensorRefinement.factorToLimit C n).hom
  obtain ⟨s, h, p, r, hcomm, _, _, _, hcover, _, _⟩ :=
    proEt_affineSingleton_of_algebra U V q hw B i
      (faithfullyFlat_tensorRefinement C hCf) (weaklyEtale_specTensorRefinement C hCf hCw)
  let : WeaklyEtale s := h
  exact ⟨Scheme.ProEt.mk s, p, r, hcover, hcomm⟩

end RC53.EllAdic

import ZInQKernel.Contrib.OneProof.EllAdic.ProEtFiniteAffineCoproductV1
import ZInQKernel.Contrib.OneProof.EllAdic.ProEtCoproductImageSieveV1
import ZInQKernel.Contrib.OneProof.EllAdic.ProEtAffineCommonRefinementV1
import ZInQKernel.Contrib.OneProof.EllAdic.AbSheafEpiLocalLiftV1
import ZInQKernel.Contrib.OneProof.EllAdic.SheafProductCoordinateLiftsV1

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace RC53.EllAdic

universe u

/-- Countably many locally surjective maps can lift their specified
coordinates on one arrow over an affine object of the actual site. -/
theorem proEt_affine_section_common_lift
    {S : Scheme.{u}} (U : S.ProEt) [IsAffine U.left]
    {F G : ℕ → Sheaf (Scheme.ProEt.topology S) Ab.{u+1}}
    (f : ∀ n, F n ⟶ G n) (r : ∀ n, ToType ((G n).obj.obj (op U)))
    (hf : ∀ n, Presheaf.IsLocallySurjective (Scheme.ProEt.topology S) (f n).hom) :
    ∃ (V : S.ProEt) (q : V ⟶ U),
      Presieve.singleton q ∈ Scheme.ProEt.precoverage S U ∧
        ∀ n, Presheaf.imageSieve (f n).hom (r n) q := by
  classical
  let R (n : ℕ) : Sieve U := Presheaf.imageSieve (f n).hom (r n)
  let d (n : ℕ) : Scheme.ProEt.FiniteAffineSingletonRefinement U (R n) := Classical.choice
    (Scheme.ProEt.nonempty_finiteAffineSingletonRefinement ((hf n).imageSieve_mem (r n)))
  let W (n : ℕ) := (d n).W
  let p (n : ℕ) : W n ⟶ U := (d n).q
  let : ∀ n, IsAffine (W n).left := fun n => (d n).affineW
  have hlift (n : ℕ) : Presheaf.imageSieve (f n).hom (r n) (p n) := by
    let e := d n
    exact proEt_imageSieve_of_coproductCover e.A e.j e.q e.coproductIso e.j_eq e.coverJ
      (f n) (r n) e.mem
  obtain ⟨V, q, a, hq, ha⟩ := proEt_affine_singleton_common_refinement U W p
    (fun n => (d n).weaklyEtaleQ) (fun n => (d n).surjectiveQ)
  refine ⟨V, q, hq, ?_⟩
  intro n
  have h : R n (a n ≫ p n) := (R n).downward_closed (hlift n) (a n)
  exact ha n ▸ h

/-- The image sieve of the literal countable product map covers each affine
object. At this stage the result is affine-local, not a sheaf-category instance. -/
theorem proEt_affine_piMap_imageSieve_covers
    {S : Scheme.{u}} (U : S.ProEt) [IsAffine U.left]
    {F G : ℕ → Sheaf (Scheme.ProEt.topology S) Ab.{u+1}}
    (f : ∀ n, F n ⟶ G n) (y : (∏ᶜ G).obj.obj (op U))
    (hf : ∀ n, Epi (f n)) :
    Presheaf.imageSieve (Limits.Pi.map f).hom y ∈ Scheme.ProEt.topology S U := by
  let J := Scheme.ProEt.topology S
  let : EssentiallySmall.{u+1} S.ProEt := inferInstance
  let : J.WEqualsLocallyBijective Ab.{u+1} := GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall J
  have hloc (n : ℕ) : Presheaf.IsLocallySurjective J (f n).hom := by
    let : Epi (f n) := hf n
    exact abSheafLocallySurjective_of_epi J (f n)
  let r (n : ℕ) : ToType ((G n).obj.obj (op U)) := (Pi.π G n).hom.app (op U) y
  obtain ⟨V, q, hq, hLift⟩ := proEt_affine_section_common_lift U f r hloc
  have hproduct := sheafPiMap_imageSieve_of_coordinateLifts J f q y hLift
  exact J.superset_covering
    ((Sieve.generate_le_iff _ _).2 (by
      intro W g hg
      cases hg
      exact hproduct))
    (Precoverage.generate_mem_toGrothendieck hq)

end RC53.EllAdic

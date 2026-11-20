import ZInQKernel.Contrib.OneProof.NeronDVR.CartierCocycle
import ZInQKernel.Contrib.OneProof.NeronDVR.TensorDatum
import ZInQKernel.Contrib.OneProof.NeronDVR.ReflectSectionCover

/-!
# Effective descent from an invariant Cartier divisor

The square of the divisor line bundle has a coherent overlap comparison.
If its nonvanishing loci are quasi-affine and cover the scheme, the
compatible global sections give effective descent.
-/

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry
open scoped AlgebraicGeometry.Scheme.Modules

universe u

namespace NeronDVR.TensorDescent

open ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective.TensorCofaces (baseMap)
open AlgebraicGeometry.SectionPencil

set_option backward.isDefEq.respectTransparency false in
/-- If quasi-affine nonvanishing loci of the square of an invariant divisor
line bundle cover the scheme, the descent datum is effective. -/
theorem isEffective_of_invariant_cartierSquare
    (R R' : Type u) [CommRing R] [CommRing R'] [Algebra R R'] [Module.FaithfullyFlat R R']
    (X : Over (Spec (CommRingCat.of R'))) [QuasiCompact X.hom] [QuasiSeparated X.hom]
    (d : Over.DescentDatum (baseMap R R') X) (D : X.left.IdealSheafData) (hD : D.IsInvertible)
    (hinv : D.comap (first R R' X) = D.comap d.toHom)
    (hCover : letI := hD.isInvertible_dual_toModules
      ∀ x : X.left, ∃ s : 𝟙_ X.left.Modules ⟶ D.toModulesᵛ.tensorPow 2,
        x ∈ s.zeroLocus.support.compl)
    (hQA : letI := hD.isInvertible_dual_toModules
      ∀ s : 𝟙_ X.left.Modules ⟶ D.toModulesᵛ.tensorPow 2,
        (Scheme.Opens.toScheme (X := X.left) s.zeroLocus.support.compl).IsQuasiAffine) :
    d.IsEffective := by
  have hp : Flat (baseMap R R') ∧ Surjective (baseMap R R') :=
    (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap R R'))).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr (inferInstance : Module.FaithfullyFlat R R'))
  have : Flat (baseMap R R') := hp.1
  have : Surjective (baseMap R R') := hp.2
  have : QuasiCompact (baseMap R R') := show QuasiCompact (Spec.map _) by infer_instance
  have : Flat (first R R' X) := show Flat (pullback.fst _ (baseMap R R')) by infer_instance
  have : Flat (chart12 R R' X) := show Flat (pullback.fst _ (baseMap R R')) by infer_instance
  have : Flat (chart13 R R' X ≫ first R R' X) := by
    rw [← nerve_eq1 R R' X]
    infer_instance
  let := hD.isInvertible_dual_toModules
  obtain ⟨s, hs⟩ := hD.exists_zeroLocus_tensorSquare
  have hD' : s.zeroLocus.IsInvertible := hs.symm ▸ hD.mul_effectiveCartier hD
  have hI : s.zeroLocus.comap (first R R' X) = s.zeroLocus.comap d.toHom := by
    rw [hs, Scheme.IdealSheafData.comap_mul, Scheme.IdealSheafData.comap_mul, hinv]
  obtain ⟨ψ, hψ⟩ := exists_pullback_comparison_of_cartierSection s hD'
    (first R R' X) d.toHom hI
  have hC : LineCocycle R R' X d _ ψ :=
    cocycle_of_cartierSection s hD' _ _ _ _ _
      (nerve_eq1 R R' X) (nerve_eq2 R R' X d) (nerve_eq3 R R' X d) ψ hψ
  let L := D.toModulesᵛ.tensorPow 2
  have : L.IsInvertible := inferInstance
  have := ZInQ.Contrib.CloudR2NOS.Descent.isQuasicoherent_L X.left L
  exact d.isEffective_of_span_compatible_sections_of_quasiAffine ψ
    ((X.hom.appLE ⊤ ⊤ le_top).hom.comp (Scheme.ΓSpecIso _).inv.hom)
    (span_compatible_sections R R' X d L ψ hC) hCover hQA

/-- The affine nonvanishing cover for an invariant divisor can be proved
after a further faithfully flat affine extension. -/
theorem isEffective_of_invariant_cartierSquare_of_pullback
    (R R' T : Type u) [CommRing R] [CommRing R'] [CommRing T] [Algebra R R'] [Algebra R' T]
    [Module.FaithfullyFlat R R'] [Module.FaithfullyFlat R' T]
    (X : Over (Spec (CommRingCat.of R'))) [QuasiCompact X.hom] [QuasiSeparated X.hom]
    (d : Over.DescentDatum (baseMap R R') X) (D : X.left.IdealSheafData) (hD : D.IsInvertible)
    (hinv : D.comap (first R R' X) = D.comap d.toHom)
    {Y : Scheme.{u}} {g : Y ⟶ Spec (CommRingCat.of T)} {a : Y ⟶ X.left}
    (hBase : IsPullback a g X.hom (baseMap R' T))
    (hCover : letI := hD.isInvertible_dual_toModules
      ∀ y : Y, ∃ s : 𝟙_ Y.Modules ⟶
          (Scheme.Modules.pullback a).obj (D.toModulesᵛ.tensorPow 2),
        y ∈ s.zeroLocus.support.compl ∧ IsAffineOpen s.zeroLocus.support.compl) :
    d.IsEffective := by
  let := hD.isInvertible_dual_toModules
  obtain ⟨cover, quasiAffine⟩ := Scheme.Modules.nonvanishing_cover_of_pullback hBase hCover
  exact isEffective_of_invariant_cartierSquare R R' X d D hD hinv cover quasiAffine

end NeronDVR.TensorDescent

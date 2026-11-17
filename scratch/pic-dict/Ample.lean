import ZInQKernel.Contrib.OneProof.PicDictionary
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.PullbackMonoidal
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.IdealSheaf.Image

/-! # pic-dict: `AmpleBaseChangeAlgClosure` (ampleness is preserved by an affine base change) -/

noncomputable section

set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory Limits

namespace PicDict

open T09Pic PkgI3 PkgI3.AbVar

universe u

/-- Pull-back of a tensor power. -/
def pullbackTensorPowIso {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) :
    ∀ n : ℕ, (Scheme.Modules.pullback f).obj (M.tensorPow n) ≅
      ((Scheme.Modules.pullback f).obj M).tensorPow n
  | 0 => (Functor.Monoidal.εIso (Scheme.Modules.pullback f)).symm
  | n + 1 => Scheme.Modules.pullbackTensorObjIso f M (M.tensorPow n) ≪≫
      (Iso.refl _ ⊗ᵢ pullbackTensorPowIso f M n)

/-- Tensor powers of an isomorphism. -/
def tensorPowIso {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) : ∀ n : ℕ, M.tensorPow n ≅ N.tensorPow n
  | 0 => Iso.refl _
  | n + 1 => e ⊗ᵢ tensorPowIso e n

/-- **Ampleness pulls back along an affine morphism** (for the EGA/Stacks notion `IsAmple`). -/
theorem isAmple_pullback {X Y : Scheme.{0}} (f : X ⟶ Y) [IsAffineHom f] [CompactSpace X]
    (L : Y.Pic) (hL : IsAmple Y L) : IsAmple X (Scheme.Pic.map f L) := by
  refine ⟨inferInstance, fun x => ?_⟩
  obtain ⟨n, hn, s, hx, haff⟩ := hL.2 (f x)
  let M := (fromSkeleton Y.Modules).obj L.val
  let e1 : (fromSkeleton X.Modules).obj (Scheme.Pic.map f L).val ≅ (Scheme.Modules.pullback f).obj M :=
    Scheme.Pic.mkIso _
  let eT : (Scheme.Modules.pullback f).obj (M.tensorPow n) ≅
      ((fromSkeleton X.Modules).obj (Scheme.Pic.map f L).val).tensorPow n :=
    pullbackTensorPowIso f M n ≪≫ tensorPowIso e1.symm n
  let s' : 𝟙_ X.Modules ⟶ ((fromSkeleton X.Modules).obj (Scheme.Pic.map f L).val).tensorPow n :=
    (Functor.Monoidal.εIso (Scheme.Modules.pullback f)).hom ≫ (Scheme.Modules.pullback f).map s ≫ eT.hom
  have hz : Scheme.Modules.Hom.zeroLocus s' = Scheme.Modules.Hom.zeroLocus ((Scheme.Modules.pullback f).map s) :=
    Scheme.Modules.Hom.zeroLocus_eq_of_arrowIso _ _
      (Arrow.isoMk (Functor.Monoidal.εIso (Scheme.Modules.pullback f)) eT.symm (by simp only [s', Arrow.mk_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]))
  have hU : (Scheme.Modules.Hom.zeroLocus s').support.compl = f ⁻¹ᵁ (Scheme.Modules.Hom.zeroLocus s).support.compl := by
    rw [hz, ← Scheme.Modules.Hom.comap_zeroLocus]
    ext y
    simp only [TopologicalSpace.Closeds.compl, TopologicalSpace.Opens.map_coe]
    have h := Scheme.IdealSheafData.coe_support_comap (Scheme.Modules.Hom.zeroLocus s) f
    change y ∈ (((Scheme.Modules.Hom.zeroLocus s).comap f).support : Set X)ᶜ ↔
      f y ∈ ((Scheme.Modules.Hom.zeroLocus s).support : Set Y)ᶜ
    rw [h]
    rfl
  refine ⟨n, hn, s', ?_, ?_⟩
  · rw [hU]; exact hx
  · rw [hU]; exact haff.preimage f

end PicDict

namespace PicDict

open T09Pic PkgI3 PkgI3.AbVar

/-- **`AmpleBaseChangeAlgClosure` is a theorem.** -/
theorem ampleBaseChangeAlgClosure : AmpleBaseChangeAlgClosure := by
  intro K _ A L hL
  haveI : CompactSpace (ptK K).left :=
    inferInstanceAs (CompactSpace (Spec (CommRingCat.of (AlgebraicClosure K))))
  haveI : IsAffineHom (ptK K).hom :=
    inferInstanceAs (IsAffineHom (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))))
  haveI : IsAffineHom (pullback.fst A.X.hom (ptK K).hom) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback _ _).flip inferInstance
  haveI : CompactSpace (AK A) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd A.X.hom (ptK K).hom)
  exact isAmple_pullback (pullback.fst A.X.hom (ptK K).hom) L hL

end PicDict

#print axioms PicDict.ampleBaseChangeAlgClosure

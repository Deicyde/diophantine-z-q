import ZInQKernel.Contrib.OneProof.FaltingsDVR.FaltingsFinalReduction
import ZInQKernel.Contrib.OneProof.FaltingsDVR.FaltingsSemistableKernel
import ZInQKernel.Contrib.OneProof.FaltingsDVR.FaltingsFiniteRational

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace ZInQ.FaltingsRestate

open ZInQ.HeightSplit ZInQ.SemistabAssembly ZInQ.SemiAbDescend
open ZInQ.Contrib.MilneQuasiInverse.Kernel

private def fieldPointIso (k : Type) [Field k] :
    𝟙_ (Over (Spec (.of k))) ≅ algPt k k :=
  Over.isoMk (Iso.refl _) (by simp [algPt])

set_option maxHeartbeats 1200000 in
set_option synthInstance.maxHeartbeats 90000 in
/-- The torus step reduces the finite kernel assertion to the rational
image of a homomorphism into an abelian variety. -/
theorem semiabelianTorsionDetectsFiniteKernel_of_abelian_image
    (hA : FiniteAbelianImageOfNoInvertibleTorsion) :
    SemiabelianTorsionDetectsFiniteKernel := by
  intro k _ _ X Y _ _ _ _ _ _ _ _ _ _ hConn hPicture c hc hf
  have : ConnectedSpace X.left := hConn
  have : IsMonHom c := hc
  obtain ⟨U, hU, j, hOpen, hj, hUConn, B, π, hπ, _hπFlat, _hπSurj, r, e, he, hk, hn⟩ :=
    hPicture
  let : GrpObj U := hU
  have : IsOpenImmersion j.left := hOpen
  have : IsMonHom j := hj
  have : ConnectedSpace U.left := hUConn
  have : IsMonHom π := hπ
  have : LocallyOfFiniteType U.hom := by rw [← Over.w j]; infer_instance
  have : QuasiCompact U.hom := DictModels.RaynaudOr.quasiCompact_of_openImm j
  have hrange : Set.range j.left = Set.univ := by
    rw [range_eq_connectedComponent j, PreconnectedSpace.connectedComponent_eq_univ]
  have hj' : IsIso j.left := (isIso_iff_isOpenImmersion_and_surjective j.left).mpr
    ⟨hOpen, ⟨Set.range_eq_univ.mp hrange⟩⟩
  have : IsIso ((Over.forget _).map j) := hj'
  have : IsIso j := isIso_of_reflects_iso _ (Over.forget _)
  let Pt := algPt k k
  let s := fieldPointIso k
  let g := j ≫ c
  have : IsMonHom g := inferInstance
  have hfU (m : ℕ) (hm : (m : k) ≠ 0) (x : Pt ⟶ U)
      (hx : x ≫ g = 1) (ht : x ^ m = 1) : x = 1 := by
    let y := s.hom ≫ x ≫ j
    have hy : y ^ m = 1 := by
      change (s.hom ≫ x ≫ j) ^ m = 1
      rw [← MonObj.comp_pow, ← MonObj.pow_comp, ht, MonObj.one_comp, MonObj.comp_one]
    have hyc : y ≫ c = 1 := by
      change (s.hom ≫ x ≫ j) ≫ c = 1
      rw [Category.assoc, Category.assoc, ← show g = j ≫ c from rfl, hx, MonObj.comp_one]
    have hy1 : y = 1 := hf y m hm hy hyc
    apply (cancel_mono j).mp
    rw [MonObj.one_comp]
    apply (cancel_epi s.hom).mp
    rw [MonObj.comp_one]
    exact hy1
  have : Finite (Pt ⟶ kernelObject g) :=
    finite_rational_kernel_of_split_presentation hA g B π r e he hk hn hfU
  let toKernel : (Pt ⟶ kernelObject c) → (Pt ⟶ kernelObject g) := fun x =>
    (kernelPointsEquiv g Pt).symm
      ⟨(x ≫ kernelInclusion c) ≫ inv j, by
        change ((x ≫ kernelInclusion c) ≫ inv j) ≫ (j ≫ c) = 1
        rw [Category.assoc, IsIso.inv_hom_id_assoc, Category.assoc,
          kernelInclusion_comp, MonObj.comp_one]⟩
  have : Finite (Pt ⟶ kernelObject c) := Finite.of_injective toKernel (by
    intro x y hxy
    have h' := congrArg (kernelPointsEquiv g Pt) hxy
    have h := congrArg Subtype.val h'
    simp only [toKernel, Equiv.apply_symm_apply] at h
    exact (cancel_mono (kernelInclusion c)).mp ((cancel_mono (inv j)).mp h))
  have : Finite ((𝟙_ (Over (Spec (.of k)))) ⟶ kernelObject c) :=
    Finite.of_injective (fun x => s.inv ≫ x) (fun _ _ h => (cancel_epi s.inv).mp h)
  have : IsClosedImmersion η[Y].left := by
    have : IsClosedImmersion (η[Y].left ≫ Y.hom) := by
      rw [Over.w]
      exact inferInstanceAs (IsClosedImmersion (𝟙 (Spec (.of k))))
    exact IsClosedImmersion.of_comp η[Y].left Y.hom
  have : IsClosedImmersion (kernelInclusion c).left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) (kernel_isPullback c).flip inferInstance
  have : LocallyOfFiniteType (kernelObject c).hom := by
    rw [← Over.w (kernelInclusion c)]
    infer_instance
  exact finite_of_finite_rational_points (kernelObject c)

end ZInQ.FaltingsRestate

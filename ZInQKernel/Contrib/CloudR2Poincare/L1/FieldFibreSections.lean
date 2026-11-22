import ZInQKernel.Contrib.CloudR2Poincare.L1.CechSectionsKernel
import ZInQKernel.Contrib.CloudR2Poincare.L1.NativeTrivialityLocus
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.GlobalSections.Proper

/-! Triviality of actual residue fibres implies triviality on every actual
field-valued base change. This uses the native factorization through the
image point's residue field, not a false field-point cover for Picard classes. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2Poincare.L1

/-- Every field-valued fibre is an actual base change of the residue fibre at its image. -/
theorem fieldBaseChangePicard_eq_one_of_residueFibres
    {X Y : Scheme.{u}} (f : X ⟶ Y) (L : X.Pic)
    (h : ∀ y : Y, Scheme.Pic.map (f.fiberι y) L = 1)
    (K : Type u) [Field K] (g : Spec (.of K) ⟶ Y) :
    Scheme.Pic.map (pullback.fst f g) L = 1 := by
  let y := g (IsLocalRing.closedPoint K)
  let q := Y.descResidueField (Scheme.stalkClosedPointTo g)
  have hg : Spec.map q ≫ Y.fromSpecResidueField y = g :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Y g
  let j : pullback f g ⟶ f.fiber y := pullback.lift (pullback.fst f g)
    (pullback.snd f g ≫ Spec.map q) (by
      rw [Category.assoc, hg]
      exact pullback.condition)
  have hj : j ≫ f.fiberι y = pullback.fst f g := pullback.lift_fst _ _ _
  have ht := congrArg (Scheme.Pic.map j) (h y)
  rw [← Scheme.Pic.map_comp, hj, Scheme.Pic.map_one] at ht
  exact ht

/-- A trivial bundle on a proper geometrically integral field-scheme has
actual base-global-section dimension one, in the original scalar action. -/
theorem finrank_sectionsModule_eq_one_of_iso_unit
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    [IsProper f] [GeometricallyIntegral f] (M : X.Modules)
    (eM : M ≅ Scheme.Modules.unit X) :
    Module.finrank Γ(Spec (.of K), ⊤) (Scheme.Modules.sectionsModule f M ⊤) = 1 := by
  let A := Γ(Spec (.of K), ⊤)
  letI : Field A := (Scheme.isField_Γ_Spec (Field.toIsField K)).toField
  letI (N : X.Modules) : Module Γ(X, ⊤) (Scheme.Modules.sectionsModule f N ⊤) :=
    inferInstanceAs (Module Γ(X, ⊤) Γ(N, ⊤))
  have act (N : X.Modules) (a : A) (x : Scheme.Modules.sectionsModule f N ⊤) :
      (a • x : Scheme.Modules.sectionsModule f N ⊤) =
        (f.appTop a • (x : Γ(N, ⊤)) : Γ(N, ⊤)) := by
    change X.presheaf.map (𝟙 (Opposite.op (⊤ : X.Opens))) (f.appTop a) • x = _
    rw [X.presheaf.map_id]
    rfl
  let e := Scheme.Modules.appLinearEquivOfIso eM ⊤
  let em : Scheme.Modules.sectionsModule f M ⊤ ≃ₗ[A]
      Scheme.Modules.sectionsModule f (Scheme.Modules.unit X) ⊤ :=
    { e.toAddEquiv with
      map_smul' := fun a x ↦ by
        have h1 := act M a x
        have h2 := act (Scheme.Modules.unit X) a
          (show Scheme.Modules.sectionsModule f (Scheme.Modules.unit X) ⊤ from e x)
        exact (congrArg e h1).trans ((e.map_smul (f.appTop a) x).trans h2.symm) }
  let c : A →ₗ[A] Scheme.Modules.sectionsModule f (Scheme.Modules.unit X) ⊤ :=
    { toFun := f.appTop
      map_add' := fun a b ↦ f.appTop.hom.map_add a b
      map_smul' := fun a b ↦ by
        have h := act (Scheme.Modules.unit X) a
          (show Scheme.Modules.sectionsModule f (Scheme.Modules.unit X) ⊤ from f.appTop b)
        exact (f.appTop.hom.map_mul a b).trans h.symm }
  let ec := LinearEquiv.ofBijective c (bijective_appTop_of_isProper_of_geometricallyIntegral f)
  exact em.finrank_eq.trans (ec.finrank_eq.symm.trans (Module.finrank_self A))

/-- The original Čech zero kernel has field dimension one after every actual
field-valued base change of a family with all trivial residue fibres. -/
theorem finrank_cechKernel_fieldBaseChange_eq_one
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [GeometricallyIntegral f]
    (M : X.Modules) [M.IsInvertible]
    (hM : ∀ y : Y, Scheme.Pic.map (f.fiberι y) (Scheme.Pic.mk M) = 1)
    (K : Type u) [Field K] (g : Spec (.of K) ⟶ Y)
    {ι : Type u} (U : ι → X.Opens) (hcover : ⨆ i, U i = ⊤) :
    Module.finrank Γ(Spec (.of K), ⊤)
      (kernel ((Scheme.Modules.cechModuleComplexNat (pullback.snd f g)
        ((Scheme.Modules.pullback (pullback.fst f g)).obj M)
        (fun i ↦ (pullback.fst f g) ⁻¹ᵁ U i)).d 0 1) : ModuleCat.{u} Γ(Spec (.of K), ⊤)) = 1 := by
  let M' := (Scheme.Modules.pullback (pullback.fst f g)).obj M
  have hm : Scheme.Pic.mk M' = 1 := by
    rw [← Scheme.Pic.map_mk]
    exact fieldBaseChangePicard_eq_one_of_residueFibres f (Scheme.Pic.mk M) hM K g
  obtain ⟨e⟩ : Nonempty (M' ≅ Scheme.Modules.unit (pullback f g)) := by
    rw [Scheme.Pic.one_eq_mk_unit] at hm
    exact (Scheme.Pic.mk_eq_mk_iff _ _).mp hm
  have hcover' : ⨆ i, (pullback.fst f g) ⁻¹ᵁ U i = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hcover, Scheme.Hom.preimage_top]
  let iso := cechCoefficientKernelIso (pullback.snd f g) M'
    (fun i ↦ (pullback.fst f g) ⁻¹ᵁ U i) hcover'
  exact iso.toLinearEquiv.finrank_eq.symm.trans
    (finrank_sectionsModule_eq_one_of_iso_unit (pullback.snd f g) M' e)

end ZInQ.Contrib.CloudR2Poincare.L1

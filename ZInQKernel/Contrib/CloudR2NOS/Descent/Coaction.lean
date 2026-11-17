/-
Copyright (c) 2026 H5/NOS Round-2 lane4 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

H5 scheme-only effective descent, route Q. This follows the Parent-approved plan
SCHEME_DESCENT_NATIVE_PLAN_001, sha 7a0aede9.

Sub-statements in this file:
* Q2: flat base change of global sections, for qcqs maps over affine bases, stated with the
  rings themselves rather than `Γ(Spec ·, ⊤)`;
* Q3: the two identifications `E₁, E₂ : S' ⊗[S] Γ(L', ⊤) ≃ Γ(aᵢ^*L', ⊤)`, the coaction
  `θ = E₂⁻¹ ∘ ψ ∘ a₁^*`, and its fixed points (the descended sections).

NATIVE. SOURCE ONLY, UNCOMPILED. Universe u. The only option is autoImplicit false.

Suppliers:
* published W07 `Scheme.Modules.sectionsModuleBaseChange` (Modules/BaseChange) and
  `bijective_cohomologyBaseChange_of_isCompact` (Cohomology/FlatBaseChange), along the same
  route as the reviewed lane4 FinalSmall `surjective_sectionsModuleBaseChange_top`;
* Mathlib `TensorProduct.AlgebraTensorModule.cancelBaseChange` and `Scheme.ΓSpecIso`.

The 4-line equivalence `tensorBaseChangeAddEquiv` is restated from W07 `AffineDescent`
(`TensorProduct.exists_addEquiv_tensor_baseChange`, Apache-2.0, frenzymath/Jacobian-Challenge
c4254cce) so that route Q does not import `AffineDescent`, which carries a raised
`maxHeartbeats`.
-/
import ZInQKernel.Contrib.CloudR2NOS.Descent.DescendedPresentation
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.FlatBaseChange
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.AffineSections

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

namespace ZInQ.Contrib.CloudR2NOS.Descent

local notation "pbSec" => ZInQ.Contrib.CloudR2NOS.ClosedSection.pullbackSection

/-! ### Q2: flat base change of global sections -/

section Q2

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  {X Y : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of A)} {g : Y ⟶ Spec (CommRingCat.of B)}
  {p : Y ⟶ X} (h : IsPullback p g f (Spec.map (CommRingCat.ofHom (algebraMap A B))))
  (F : X.Modules)

/-- The `Γ(Spec A, ⊤)`-algebra structure on `Γ(Spec B, ⊤)` through the base change map. -/
abbrev algebraΓSpec (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    Algebra Γ(Spec (CommRingCat.of A), ⊤) Γ(Spec (CommRingCat.of B), ⊤) :=
  (Spec.map (CommRingCat.ofHom (algebraMap A B))).appTop.hom.toAlgebra

include h in
/-- The W07 base change of global sections is bijective for a flat base change of a
quasi-compact quasi-separated morphism over affine bases. This follows the lane4 FinalSmall
proof, with bijectivity in place of surjectivity. -/
theorem bijective_sectionsModuleBaseChange_top [Module.Flat A B]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F] [QuasiSeparated f] [QuasiCompact f] :
    letI := algebraΓSpec A B
    Function.Bijective (Scheme.Modules.sectionsModuleBaseChange h F rfl ⊤) := by
  letI := algebraΓSpec A B
  haveI : Flat (Spec.map (CommRingCat.ofHom (algebraMap A B))) := flat_specMap_algebraMap A B
  have key : ⇑(Scheme.Modules.pushforwardSectionsAddEquiv g p F ⊤) ∘
      ⇑(Scheme.Modules.cohomologyBaseChange h F rfl (TopCat.Sheaf.freeSheaf ⊤) 0) =
      ⇑(Scheme.Modules.sectionsModuleBaseChange h F rfl ⊤) ∘
        ⇑((Scheme.Modules.sectionsLinearEquiv F ⊤).lTensor Γ(Spec (CommRingCat.of B), ⊤)) := by
    funext tensorElement
    induction tensorElement using TensorProduct.induction_on with
    | zero => simp only [Function.comp_apply, map_zero]
    | add t t' hz hz' =>
      simp only [Function.comp_apply, map_add] at hz hz' ⊢
      rw [hz, hz']
    | tmul extensionScalar element =>
      change TopCat.Sheaf.extFreeSheafZeroAddEquiv ⊤ _ ((WithAction.toExt _ element).comp
          (mk₀ (Scheme.Modules.toSheafUnit p F ≫
            (Scheme.Modules.pushforwardPullbackAction g p F extensionScalar).asHom))
          (add_zero 0)) =
        Scheme.Modules.sectionsModuleBaseChange h F rfl ⊤
          (extensionScalar ⊗ₜ Scheme.Modules.sectionsLinearEquiv F ⊤ element)
      rw [TopCat.Sheaf.extFreeSheafZeroAddEquiv_comp_mk₀,
        Scheme.Modules.sectionsModuleBaseChange_tmul]
      rfl
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have hbij := Scheme.Modules.bijective_cohomologyBaseChange_of_isCompact h F rfl
    (openSubset := ⊤) (by rw [TopologicalSpace.Opens.coe_top]; exact isCompact_univ) 0
  have h2 : Function.Bijective (⇑(Scheme.Modules.sectionsModuleBaseChange h F rfl ⊤) ∘
      ⇑((Scheme.Modules.sectionsLinearEquiv F ⊤).lTensor Γ(Spec (CommRingCat.of B), ⊤))) := by
    rw [← key]
    exact (Scheme.Modules.pushforwardSectionsAddEquiv g p F ⊤).bijective.comp hbij
  exact (Function.Bijective.of_comp_iff _ (LinearEquiv.bijective _)).mp h2

/-- Global functions on `Spec A` are `A`. -/
abbrev ΓinvA (A : Type u) [CommRing A] : A →+* Γ(Spec (CommRingCat.of A), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom

theorem ΓinvA_algebraMap (a : A) :
    ΓinvA B (algebraMap A B a) =
      (Spec.map (CommRingCat.ofHom (algebraMap A B))).appTop (ΓinvA A a) := by
  have := congr($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap A B))) a)
  simpa using this.symm

theorem smul_sectionsModule_top_eq (a : A) (s : Γ(F, ⊤)) :
    ((ΓinvA A a) • (show Scheme.Modules.sectionsModule f F ⊤ from s) :
      Scheme.Modules.sectionsModule f F ⊤) =
      (show Γ(F, ⊤) from (letI := moduleTop f F; a • s)) := by
  letI := moduleTop f F
  change (f.appTop ≫ X.presheaf.map (⊤ : X.Opens).leTop.op).hom (ΓinvA A a) • s =
    (f.appLE ⊤ ⊤ le_top).hom (ΓinvA A a) • s
  rw [show (⊤ : X.Opens).leTop = 𝟙 ⊤ from rfl, op_id, X.presheaf.map_id, Category.comp_id,
    Scheme.Hom.appLE_top_top_eq_appTop]

/-- Change of scalars along `ΓSpecIso`:
`B ⊗[A] Γ(F, ⊤) → Γ(Spec B, ⊤) ⊗[Γ(Spec A, ⊤)] Γ(F, ⊤)`. -/
noncomputable def toΓSpecTensor :
    (letI := moduleTop f F; B ⊗[A] Γ(F, ⊤)) →+
      (letI := algebraΓSpec A B;
        Γ(Spec (CommRingCat.of B), ⊤) ⊗[Γ(Spec (CommRingCat.of A), ⊤)]
          Scheme.Modules.sectionsModule f F ⊤) :=
  letI := moduleTop f F
  letI := algebraΓSpec A B
  TensorProduct.liftAddHom
    { toFun := fun b => (TensorProduct.mk Γ(Spec (CommRingCat.of A), ⊤)
          Γ(Spec (CommRingCat.of B), ⊤) (Scheme.Modules.sectionsModule f F ⊤) (ΓinvA B b)).toAddMonoidHom.comp
          (AddMonoidHom.id Γ(F, ⊤))
      map_zero' := by ext s; simp
      map_add' := fun b b' => by ext s; simp [add_tmul] }
    (fun a b s => by
      change ΓinvA B (a • b) ⊗ₜ (s : Scheme.Modules.sectionsModule f F ⊤) =
        ΓinvA B b ⊗ₜ (show Scheme.Modules.sectionsModule f F ⊤ from (a • s))
      rw [← smul_sectionsModule_top_eq F a s, ← TensorProduct.smul_tmul, Algebra.smul_def,
        Algebra.smul_def, map_mul, ΓinvA_algebraMap]
      rfl)

/-- The inverse change of scalars. -/
noncomputable def ofΓSpecTensor :
    (letI := algebraΓSpec A B;
        Γ(Spec (CommRingCat.of B), ⊤) ⊗[Γ(Spec (CommRingCat.of A), ⊤)]
          Scheme.Modules.sectionsModule f F ⊤) →+
      (letI := moduleTop f F; B ⊗[A] Γ(F, ⊤)) :=
  letI := moduleTop f F
  letI := algebraΓSpec A B
  TensorProduct.liftAddHom
    { toFun := fun c => (TensorProduct.mk A B Γ(F, ⊤)
          ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom c)).toAddMonoidHom.comp
          (AddMonoidHom.id Γ(F, ⊤))
      map_zero' := by ext s; simp
      map_add' := fun c c' => by ext s; simp [add_tmul] }
    (fun a c s => by
      obtain ⟨a₀, rfl⟩ : ∃ a₀ : A, ΓinvA A a₀ = a :=
        ⟨(Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom a,
          congr($((Scheme.ΓSpecIso (CommRingCat.of A)).hom_inv_id) a)⟩
      change (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom (ΓinvA A a₀ • c) ⊗ₜ (s : Γ(F, ⊤)) =
        (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom c ⊗ₜ
          (show Γ(F, ⊤) from ((ΓinvA A a₀) • (show Scheme.Modules.sectionsModule f F ⊤ from s)))
      rw [smul_sectionsModule_top_eq F a₀ s, ← TensorProduct.smul_tmul, Algebra.smul_def,
        map_mul, Algebra.smul_def]
      congr 1
      change (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom
          ((Spec.map (CommRingCat.ofHom (algebraMap A B))).appTop (ΓinvA A a₀)) * _ = _
      rw [← ΓinvA_algebraMap]
      change ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom).hom
          (algebraMap A B a₀) * _ = _
      rw [Iso.inv_hom_id]
      rfl)

theorem ofΓSpecTensor_toΓSpecTensor (x : letI := moduleTop f F; B ⊗[A] Γ(F, ⊤)) :
    ofΓSpecTensor F (toΓSpecTensor F x) = x := by
  letI := moduleTop f F
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul b s =>
    change (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom (ΓinvA B b) ⊗ₜ s = b ⊗ₜ s
    congr 1
    exact congr($((Scheme.ΓSpecIso (CommRingCat.of B)).inv_hom_id) b)

theorem toΓSpecTensor_ofΓSpecTensor
    (x : letI := algebraΓSpec A B;
      Γ(Spec (CommRingCat.of B), ⊤) ⊗[Γ(Spec (CommRingCat.of A), ⊤)]
        Scheme.Modules.sectionsModule f F ⊤) :
    toΓSpecTensor F (ofΓSpecTensor F x) = x := by
  letI := algebraΓSpec A B
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul c s =>
    change ΓinvA B ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom c) ⊗ₜ s = c ⊗ₜ s
    congr 1
    exact congr($((Scheme.ΓSpecIso (CommRingCat.of B)).hom_inv_id) c)

/-- **Q2.** The base change of global sections `B ⊗[A] Γ(F, ⊤) → Γ(p^*F, ⊤)`,
`b ⊗ s ↦ g^♯ b • p^* s`. -/
noncomputable def sectionsBC :
    (letI := moduleTop f F; B ⊗[A] Γ(F, ⊤)) →+ Γ((Scheme.Modules.pullback p).obj F, ⊤) :=
  letI := algebraΓSpec A B
  (Scheme.Modules.sectionsModuleBaseChange h F rfl ⊤).toAddMonoidHom.comp (toΓSpecTensor F)

theorem sectionsBC_tmul (b : B) (s : Γ(F, ⊤)) :
    sectionsBC h F (letI := moduleTop f F; b ⊗ₜ s) =
      (g.appLE ⊤ ⊤ le_top).hom (ΓinvA B b) • pbSec p s := by
  letI := algebraΓSpec A B
  change Scheme.Modules.sectionsModuleBaseChange h F rfl ⊤ (ΓinvA B b ⊗ₜ s) = _
  rw [Scheme.Modules.sectionsModuleBaseChange_tmul, Scheme.Hom.appLE_top_top_eq_appTop]
  change (g.appTop ≫ Y.presheaf.map (p ⁻¹ᵁ ⊤).leTop.op).hom (ΓinvA B b) • pbSec p s = _
  rw [show (p ⁻¹ᵁ ⊤).leTop = 𝟙 _ from rfl, op_id, Y.presheaf.map_id, Category.comp_id]

include h in
/-- **Q2 (bijectivity).** -/
theorem bijective_sectionsBC [Module.Flat A B]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F] [QuasiSeparated f] [QuasiCompact f] :
    Function.Bijective (sectionsBC h F) := by
  letI := algebraΓSpec A B
  have hΛ : Function.Bijective (toΓSpecTensor (B := B) F) :=
    ⟨Function.LeftInverse.injective (g := ofΓSpecTensor F) (ofΓSpecTensor_toΓSpecTensor F),
      Function.RightInverse.surjective (g := ofΓSpecTensor F) (toΓSpecTensor_ofΓSpecTensor F)⟩
  exact (bijective_sectionsModuleBaseChange_top h F).comp hΛ

end Q2

/-! ### The tensor identification `S ⊗[A] M ≃+ (R ⊗[A] S) ⊗[R] M` (restated from W07). -/

/-- `s ⊗ m ↦ (1 ⊗ s) ⊗ m`. Restated from W07 `TensorProduct.exists_addEquiv_tensor_baseChange`
(AffineDescent). -/
noncomputable def tensorBaseChangeAddEquiv (A R S M : Type u) [CommRing A] [CommRing R] [CommRing S]
    [Algebra A R] [Algebra A S] [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower A R M] :
    S ⊗[A] M ≃+ (R ⊗[A] S) ⊗[R] M :=
  ((TensorProduct.comm A S M).toAddEquiv.trans
    (AlgebraTensorModule.cancelBaseChange A R R M S).symm.toAddEquiv).trans
      (TensorProduct.comm R (R ⊗[A] S) M).symm.toAddEquiv

theorem tensorBaseChangeAddEquiv_tmul (A R S M : Type u) [CommRing A] [CommRing R] [CommRing S]
    [Algebra A R] [Algebra A S] [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower A R M]
    (s : S) (m : M) :
    tensorBaseChangeAddEquiv A R S M (s ⊗ₜ m) = (1 ⊗ₜ s) ⊗ₜ m :=
  rfl

/-! ### Q3: the two identifications and the coaction -/

section Q3

variable {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S']
  [Module.FaithfullyFlat S S']
  {X' : Scheme.{u}} (f' : X' ⟶ Spec (CommRingCat.of S')) (L' : X'.Modules)
  {X'' : Scheme.{u}} (f'' : X'' ⟶ Spec (CommRingCat.of (S' ⊗[S] S'))) (a₁ a₂ : X'' ⟶ X')

/-- The `S`-module structure on `Γ(L', ⊤)`, through `S → S'`. -/
abbrev moduleTopS : Module S Γ(L', ⊤) :=
  letI := moduleTop f' L'
  Module.compHom Γ(L', ⊤) (algebraMap S S')

theorem isScalarTower_top : letI := moduleTop f' L'; letI := moduleTopS S' f' L'
    IsScalarTower S S' Γ(L', ⊤) := by
  letI := moduleTop f' L'
  letI := moduleTopS S' f' L'
  exact IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-- The swap of the two factors of `S' ⊗[S] S'`. -/
abbrev swapΓ : S' ⊗[S] S' →+* S' ⊗[S] S' :=
  (Algebra.TensorProduct.comm S S' S').toAlgHom.toRingHom

theorem incL_comp_swap :
    (swapΓ (S := S) S').comp (algebraMap S' (S' ⊗[S] S')) =
      (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom :=
  RingHom.ext fun x => by simp [swapΓ]

/-- The `incR` square, rewritten as an `incL` square through the swap. -/
theorem isPullback_swap
    (ha₂ : IsPullback a₂ f'' f' (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom))) :
    IsPullback a₂ (f'' ≫ Spec.map (CommRingCat.ofHom (swapΓ (S := S) S'))) f'
      (Spec.map (CommRingCat.ofHom (algebraMap S' (S' ⊗[S] S')))) := by
  have hsw : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
      S' →ₐ[S] S' ⊗[S] S').toRingHom) =
      Spec.map (CommRingCat.ofHom (swapΓ (S := S) S')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap S' (S' ⊗[S] S'))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, incL_comp_swap]
  haveI : IsIso (Spec.map (CommRingCat.ofHom (swapΓ (S := S) S'))) := by
    have : IsIso (CommRingCat.ofHom (swapΓ (S := S) S')) :=
      (CommRingCat.isIso_iff_bijective _).mpr (Algebra.TensorProduct.comm S S' S').bijective
    infer_instance
  rw [hsw] at ha₂
  exact IsPullback.of_iso ha₂ (Iso.refl _) (Iso.refl _)
    (asIso (Spec.map (CommRingCat.ofHom (swapΓ (S := S) S')))) (Iso.refl _)
    (by simp) (by simp) (by simp) (by simp)

end Q3

end ZInQ.Contrib.CloudR2NOS.Descent

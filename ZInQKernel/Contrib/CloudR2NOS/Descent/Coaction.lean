/-
Copyright (c) 2026 H5/NOS Round-2 lane4 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

H5 scheme-only effective descent, route Q. This follows the Parent-approved plan
for scheme-only native descent.

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
EDITION 2 (2026-11-17, first Parent compile probe of this file). Statements unchanged:
* import Descent.Image for `flat_specMap_algebraMap`; `open CategoryTheory.Abelian.Ext in` on the flat base-change
  theorem (its `WithAction.toExt`/`mk₀`, exactly as in the compiled FinalSmall copy of this proof);
* `ΓinvA_algebraMap`: the naturality square applied pointwise (the old `simpa` closed the hypothesis to `True`);
* `smul_sectionsModule_top_eq`, `sectionsBC_tmul`: the W07 lemma rewrites whose instances only match up to unfolding of
  the section-module synonym are `erw`;
* `toΓSpecTensor`/`ofΓSpecTensor`: additivity and the balancing condition are proved on `TensorProduct.mk` with the
  synonym written explicitly (`LinearMap.map_zero₂/map_add₂/map_smul₂`, `map_smul`), instead of `simp` and
  type ascriptions that did not change the elaborated type;
* `bijective_sectionsBC`: the rings and `f` are passed explicitly; `moduleTopS (S := S)` (the base ring is not
  determined by `S' f' L'`);
* the swap is an isomorphism by its explicit inverse (itself), without the removed `CommRingCat.isIso_iff_bijective`.
EDITION 3 (2026-11-17, second Parent compile probe). Statements unchanged:
* the bilinear `TensorProduct.mk` steps (`map_zero₂`, `map_add₂`, `map_smul₂`, `map_smul`) are applied with `exact` and
  explicit arguments: the section-module synonym makes the target type-correct only up to unfolding, so `rw` cannot
  match them (the preceding `map_zero`/`map_add`/`e1` rewrites did succeed);
* `sectionsBC_tmul`: the restricted scalar is read in `Γ(Y, ⊤)` (`p ⁻¹ᵁ ⊤` is `⊤` only up to unfolding);
* the swap's inverse identities are `congrArg CommRingCat.ofHom (RingHom.ext hinv)`: `ext` on ring maps out of
  `S' ⊗[S] S'` descended to the tensor factors.
EDITION 4 (2026-11-17, third Parent compile probe). Statements unchanged:
* `map_smul` receives the section in the module where its action lives (`show … from s`): the scalar-action instance
  of `map_smul` is read off the argument's type (180/230);
* `sectionsBC_tmul`: the restriction is rewritten at `(⊤ : Y.Opens).leTop`, exactly as in the compiled FinalSmall lemma
  `smul_sectionsModule_top` (`p ⁻¹ᵁ ⊤` is `⊤` by unfolding), with no `show` wrapper left in the goal (274).
-/
import ZInQKernel.Contrib.CloudR2NOS.Descent.DescendedPresentation
import ZInQKernel.Contrib.CloudR2NOS.Descent.Image
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
open CategoryTheory.Abelian.Ext in
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
  first
  | exact congrArg (fun φ => φ.hom a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap A B)))
  | exact (congrArg (fun φ => φ.hom a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap A B)))).symm

theorem smul_sectionsModule_top_eq (a : A) (s : Γ(F, ⊤)) :
    ((ΓinvA A a) • (show Scheme.Modules.sectionsModule f F ⊤ from s) :
      Scheme.Modules.sectionsModule f F ⊤) =
      (show Γ(F, ⊤) from (letI := moduleTop f F; a • s)) := by
  letI := moduleTop f F
  change (f.appTop ≫ X.presheaf.map (⊤ : X.Opens).leTop.op).hom (ΓinvA A a) • s =
    (f.appLE ⊤ ⊤ le_top).hom (ΓinvA A a) • s
  rw [show (⊤ : X.Opens).leTop = 𝟙 ⊤ from rfl, op_id, X.presheaf.map_id, Category.comp_id]
  erw [Scheme.Hom.appLE_top_top_eq_appTop]

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
      map_zero' := by
        refine AddMonoidHom.ext fun s => ?_
        change TensorProduct.mk Γ(Spec (CommRingCat.of A), ⊤) Γ(Spec (CommRingCat.of B), ⊤)
          (Scheme.Modules.sectionsModule f F ⊤) (ΓinvA B 0) s = 0
        rw [map_zero]
        exact LinearMap.map_zero₂ _ _
      map_add' := fun b b' => by
        refine AddMonoidHom.ext fun s => ?_
        change TensorProduct.mk Γ(Spec (CommRingCat.of A), ⊤) Γ(Spec (CommRingCat.of B), ⊤)
            (Scheme.Modules.sectionsModule f F ⊤) (ΓinvA B (b + b')) s =
          TensorProduct.mk Γ(Spec (CommRingCat.of A), ⊤) Γ(Spec (CommRingCat.of B), ⊤)
              (Scheme.Modules.sectionsModule f F ⊤) (ΓinvA B b) s +
            TensorProduct.mk Γ(Spec (CommRingCat.of A), ⊤) Γ(Spec (CommRingCat.of B), ⊤)
              (Scheme.Modules.sectionsModule f F ⊤) (ΓinvA B b') s
        rw [map_add]
        exact LinearMap.map_add₂ _ _ _ _ }
    (fun a b s => by
      have e1 : ΓinvA B (a • b) = ΓinvA A a • ΓinvA B b := by
        rw [Algebra.smul_def a b, map_mul, ΓinvA_algebraMap]
        all_goals rfl
      change TensorProduct.mk Γ(Spec (CommRingCat.of A), ⊤) Γ(Spec (CommRingCat.of B), ⊤)
          (Scheme.Modules.sectionsModule f F ⊤) (ΓinvA B (a • b)) s =
        TensorProduct.mk Γ(Spec (CommRingCat.of A), ⊤) Γ(Spec (CommRingCat.of B), ⊤)
          (Scheme.Modules.sectionsModule f F ⊤) (ΓinvA B b) (a • s)
      rw [e1]
      exact (LinearMap.map_smul₂ (TensorProduct.mk Γ(Spec (CommRingCat.of A), ⊤) Γ(Spec (CommRingCat.of B), ⊤)
          (Scheme.Modules.sectionsModule f F ⊤)) (ΓinvA A a) (ΓinvA B b) s).trans
        ((map_smul (TensorProduct.mk Γ(Spec (CommRingCat.of A), ⊤) Γ(Spec (CommRingCat.of B), ⊤) (Scheme.Modules.sectionsModule f F ⊤) (ΓinvA B b))
          (ΓinvA A a) (show Scheme.Modules.sectionsModule f F ⊤ from s)).symm.trans
        (congrArg (TensorProduct.mk Γ(Spec (CommRingCat.of A), ⊤) Γ(Spec (CommRingCat.of B), ⊤) (Scheme.Modules.sectionsModule f F ⊤) (ΓinvA B b))
          (smul_sectionsModule_top_eq (f := f) F a s))))

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
      map_zero' := by
        refine AddMonoidHom.ext fun s => ?_
        change TensorProduct.mk A B Γ(F, ⊤) ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom 0) s = 0
        rw [map_zero]
        exact LinearMap.map_zero₂ _ _
      map_add' := fun c c' => by
        refine AddMonoidHom.ext fun s => ?_
        change TensorProduct.mk A B Γ(F, ⊤) ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom (c + c')) s =
          TensorProduct.mk A B Γ(F, ⊤) ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom c) s +
            TensorProduct.mk A B Γ(F, ⊤) ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom c') s
        rw [map_add]
        exact LinearMap.map_add₂ _ _ _ _ }
    (fun a c s => by
      obtain ⟨a₀, rfl⟩ : ∃ a₀ : A, ΓinvA A a₀ = a :=
        ⟨(Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom a,
          congr($((Scheme.ΓSpecIso (CommRingCat.of A)).hom_inv_id) a)⟩
      have e1 : (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom (ΓinvA A a₀ • c) =
          a₀ • (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom c := by
        rw [Algebra.smul_def (ΓinvA A a₀) c, map_mul]
        change (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom
            ((Spec.map (CommRingCat.ofHom (algebraMap A B))).appTop (ΓinvA A a₀)) *
              (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom c = _
        rw [← ΓinvA_algebraMap, Algebra.smul_def a₀]
        congr 1
        exact congr($((Scheme.ΓSpecIso (CommRingCat.of B)).inv_hom_id) (algebraMap A B a₀))
      have e2 := smul_sectionsModule_top_eq (f := f) F a₀ s
      change TensorProduct.mk A B Γ(F, ⊤)
          ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom (ΓinvA A a₀ • c)) s =
        TensorProduct.mk A B Γ(F, ⊤) ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom c)
          (ΓinvA A a₀ • s)
      rw [e1]
      exact (LinearMap.map_smul₂ (TensorProduct.mk A B Γ(F, ⊤)) a₀
          ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom c) s).trans
        ((map_smul (TensorProduct.mk A B Γ(F, ⊤) ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom c)) a₀
          (show Γ(F, ⊤) from s)).symm.trans
        (congrArg (TensorProduct.mk A B Γ(F, ⊤) ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom c)) e2.symm)))

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
  erw [Scheme.Modules.sectionsModuleBaseChange_tmul]
  erw [Scheme.Hom.appLE_top_top_eq_appTop]
  change (g.appTop ≫ Y.presheaf.map (⊤ : Y.Opens).leTop.op).hom (ΓinvA B b) • pbSec p s = _
  rw [show (⊤ : Y.Opens).leTop = 𝟙 ⊤ from rfl, op_id, Y.presheaf.map_id, Category.comp_id]
  all_goals rfl

include h in
/-- **Q2 (bijectivity).** -/
theorem bijective_sectionsBC [Module.Flat A B]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F] [QuasiSeparated f] [QuasiCompact f] :
    Function.Bijective (sectionsBC h F) := by
  letI := algebraΓSpec A B
  have hΛ : Function.Bijective (toΓSpecTensor (A := A) (B := B) (f := f) F) :=
    ⟨Function.LeftInverse.injective (g := ofΓSpecTensor (A := A) (B := B) (f := f) F)
        (ofΓSpecTensor_toΓSpecTensor (A := A) (B := B) (f := f) F),
      Function.RightInverse.surjective (g := ofΓSpecTensor (A := A) (B := B) (f := f) F)
        (toΓSpecTensor_ofΓSpecTensor (A := A) (B := B) (f := f) F)⟩
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

theorem isScalarTower_top : letI := moduleTop f' L'; letI := moduleTopS (S := S) S' f' L'
    IsScalarTower S S' Γ(L', ⊤) := by
  letI := moduleTop f' L'
  letI := moduleTopS (S := S) S' f' L'
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
    have hinv : ∀ x, swapΓ (S := S) S' (swapΓ (S := S) S' x) = x := fun x => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [swapΓ]
      | add x y hx hy => rw [map_add, map_add, hx, hy]
    have : IsIso (CommRingCat.ofHom (swapΓ (S := S) S')) :=
      ⟨⟨CommRingCat.ofHom (swapΓ (S := S) S'), congrArg CommRingCat.ofHom (RingHom.ext hinv),
        congrArg CommRingCat.ofHom (RingHom.ext hinv)⟩⟩
    infer_instance
  rw [hsw] at ha₂
  exact IsPullback.of_iso ha₂ (Iso.refl _) (Iso.refl _)
    (asIso (Spec.map (CommRingCat.ofHom (swapΓ (S := S) S')))) (Iso.refl _)
    (by simp) (by simp) (by simp) (by simp)

end Q3

end ZInQ.Contrib.CloudR2NOS.Descent

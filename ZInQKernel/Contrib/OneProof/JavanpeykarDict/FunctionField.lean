import ZInQKernel.Contrib.OneProof.JavanpeykarDict.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import ZInQKernel.Contrib.OneProof.JavanpeykarDict.BelyiAlgebra

/-! # javanpeykar-dict (part 3): the function field of a base change, and `BelyiBaseChange`

* `functionField_baseChange`: for an integral `K`-scheme `X` with `X_L` integral and `L/K` algebraic,
  `K(X) ⊗_K L → L(X_L)` is bijective (Mathlib `isIso_pushoutSection_of_isAffineOpen` on an affine open
  through the generic point, as in the vendored Jacobian-Challenge `free_finite_app`, then
  `productMap_bijective_of_fraction`);
* `belyiBaseChange_of_unramified : ConstantFieldExtensionUnramified → BelyiBaseChange`.

No `sorry`, no `axiom`. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

namespace JavanpeykarDict

open CategoryTheory AlgebraicGeometry Limits
open scoped TensorProduct

variable {K : Type} [Field K] (X : Over (Spec (CommRingCat.of K))) (L : Type) [Field L] [Algebra K L]

/-- The projection `X_L → X`. -/
def pr : (baseChangeCurve X L).left ⟶ X.left :=
  pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap K L)))

theorem isPullback_pr : IsPullback (pr X L) (baseChangeCurve X L).hom X.hom
    (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
  IsPullback.of_hasPullback _ _

theorem surjective_specMap_algebraMap :
    Surjective (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  have : Subsingleton (Spec (.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have : Nonempty (Spec (.of L)) := inferInstanceAs (Nonempty (PrimeSpectrum L))
  exact ⟨fun _ ↦ ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩

theorem surjective_pr : Surjective (pr X L) :=
  MorphismProperty.of_isPullback (P := @Surjective) (isPullback_pr X L).flip
    (surjective_specMap_algebraMap L)

theorem pr_genericPoint [IsIntegral X.left] [IsIntegral (baseChangeCurve X L).left] :
    pr X L (genericPoint (baseChangeCurve X L).left) = genericPoint X.left := by
  have h := (genericPoint_spec (baseChangeCurve X L).left).image (pr X L).continuous
  rw [Set.image_univ_of_surjective (surjective_pr X L).surj, closure_univ] at h
  exact h.eq (genericPoint_spec X.left)

/-- The map of function fields `K(X) → L(X_L)` induced by the projection. -/
def ffMap [IsIntegral X.left] [IsIntegral (baseChangeCurve X L).left] :
    X.left.functionField ⟶ (baseChangeCurve X L).left.functionField :=
  X.left.presheaf.stalkSpecializes (Inseparable.of_eq (pr_genericPoint X L)).specializes ≫
    (pr X L).stalkMap (genericPoint (baseChangeCurve X L).left)

theorem germ_ffMap [IsIntegral X.left] [IsIntegral (baseChangeCurve X L).left] (U : X.left.Opens)
    (hU : genericPoint X.left ∈ U) (hV : genericPoint (baseChangeCurve X L).left ∈ (pr X L) ⁻¹ᵁ U) :
    X.left.presheaf.germ U _ hU ≫ ffMap X L =
      (pr X L).app U ≫ (baseChangeCurve X L).left.presheaf.germ ((pr X L) ⁻¹ᵁ U) _ hV := by
  rw [ffMap, TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.germ_stalkMap]

end JavanpeykarDict

namespace JavanpeykarDict

open CategoryTheory AlgebraicGeometry Limits
open scoped TensorProduct

variable {K : Type} [Field K] (X : Over (Spec (CommRingCat.of K))) (L : Type) [Field L] [Algebra K L]

/-- `K → Γ(X, ⊤) → K(X)` (the kernel's `ffStructMap`) equals `K → Γ(X, U) → K(X)` for any nonempty
open `U`. -/
theorem ffStructMap_eq [IsIntegral X.left] (U : X.left.Opens) [Nonempty U] :
    ZInQ.LeafPush2.ffStructMap X =
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ X.hom.appLE ⊤ U (by simp) ≫
        X.left.germToFunctionField U).hom := by
  simp [ZInQ.LeafPush2.ffStructMap, Scheme.Hom.appLE, Scheme.germToFunctionField]

/-- **The function field of `X_L` is `K(X) ⊗_K L` (glue, proved).** For an integral `K`-scheme `X`
with `X_L` integral and `L/K` algebraic, the map `K(X) ⊗_K L → L(X_L)` induced by the projection and
the structure map is bijective (affine base change of sections, Mathlib
`isIso_pushoutSection_of_isAffineOpen`, then fraction fields). -/
theorem functionField_baseChange [IsIntegral X.left] [IsIntegral (baseChangeCurve X L).left]
    [Algebra.IsAlgebraic K L] :
    letI := ZInQ.LeafPush2.ffAlgebra X
    letI := ZInQ.LeafPush2.ffAlgebra (baseChangeCurve X L)
    letI : Algebra K (baseChangeCurve X L).left.functionField :=
      ((algebraMap L _).comp (algebraMap K L)).toAlgebra
    haveI : IsScalarTower K L (baseChangeCurve X L).left.functionField :=
      IsScalarTower.of_algebraMap_eq' rfl
    ∃ ι : X.left.functionField →ₐ[K] (baseChangeCurve X L).left.functionField,
      Function.Bijective (Algebra.TensorProduct.productMap ι
        (IsScalarTower.toAlgHom K L (baseChangeCurve X L).left.functionField)) := by
  letI := ZInQ.LeafPush2.ffAlgebra X
  letI := ZInQ.LeafPush2.ffAlgebra (baseChangeCurve X L)
  letI iKM : Algebra K (baseChangeCurve X L).left.functionField :=
    ((algebraMap L _).comp (algebraMap K L)).toAlgebra
  haveI : IsScalarTower K L (baseChangeCurve X L).left.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  -- an affine open containing the generic point
  obtain ⟨_, ⟨U, hU, rfl⟩, hηU, -⟩ := X.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint X.left)) isOpen_univ
  have hU : IsAffineOpen U := hU
  haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
  have hηV : genericPoint (baseChangeCurve X L).left ∈ (pr X L) ⁻¹ᵁ U := by
    show pr X L _ ∈ U
    rw [pr_genericPoint]; exact hηU
  haveI : Nonempty ((pr X L) ⁻¹ᵁ U) := ⟨⟨_, hηV⟩⟩
  haveI : IsAffineHom (pr X L) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) (isPullback_pr X L).flip inferInstance
  have hV : IsAffineOpen ((pr X L) ⁻¹ᵁ U) := hU.preimage (pr X L)
  -- affine base change of sections (as in the vendored `free_finite_app`)
  have hUY : (pr X L) ⁻¹ᵁ U = (pr X L) ⁻¹ᵁ U ⊓ (baseChangeCurve X L).hom ⁻¹ᵁ ⊤ := by simp
  have := isIso_pushoutSection_of_isAffineOpen (isPullback_pr X L) (US := ⊤) (UT := ⊤) (UX := U)
    (by simp) (by simp) hUY (isAffineOpen_top _) (isAffineOpen_top _) hU
  have hpo := (isIso_pushoutSection_iff ..).mp this
  set eA := Scheme.ΓSpecIso (.of K)
  set eB := Scheme.ΓSpecIso (.of L)
  have happ : (pr X L).appLE U ((pr X L) ⁻¹ᵁ U) (by simp) = (pr X L).app U := by
    rw [Scheme.Hom.app_eq_appLE]
  rw [happ] at hpo
  have hpo' := hpo.of_iso eA (Iso.refl _) eB (Iso.refl _) (f' := eA.inv ≫ X.hom.appLE ⊤ U (by simp))
    (g' := CommRingCat.ofHom (algebraMap K L)) (inl' := (pr X L).app U)
    (inr' := eB.inv ≫ (baseChangeCurve X L).hom.appLE ⊤ ((pr X L) ⁻¹ᵁ U) (by simp)) (by simp) (by
      rw [show (Spec.map (CommRingCat.ofHom (algebraMap K L))).appLE ⊤ ⊤ (by simp) =
        (Spec.map (CommRingCat.ofHom (algebraMap K L))).appTop by
          rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl,
        Scheme.ΓSpecIso_naturality]) (by simp) (by simp)
  let A := Γ(X.left, U)
  let B := Γ((baseChangeCurve X L).left, (pr X L) ⁻¹ᵁ U)
  letI iA : Algebra K A := (eA.inv ≫ X.hom.appLE ⊤ U (by simp)).hom.toAlgebra
  letI iB : Algebra L B :=
    (eB.inv ≫ (baseChangeCurve X L).hom.appLE ⊤ ((pr X L) ⁻¹ᵁ U) (by simp)).hom.toAlgebra
  letI iAB : Algebra A B := ((pr X L).app U).hom.toAlgebra
  letI iKB : Algebra K B := ((eA.inv ≫ X.hom.appLE ⊤ U (by simp)) ≫ (pr X L).app U).hom.toAlgebra
  haveI t1 : IsScalarTower K A B := IsScalarTower.of_algebraMap_eq' rfl
  have hw : ((eA.inv ≫ X.hom.appLE ⊤ U (by simp)) ≫ (pr X L).app U).hom =
      (CommRingCat.ofHom (algebraMap K L) ≫
        (eB.inv ≫ (baseChangeCurve X L).hom.appLE ⊤ ((pr X L) ⁻¹ᵁ U) (by simp))).hom := by
    rw [hpo'.w]
  haveI t2 : IsScalarTower K L B := IsScalarTower.of_algebraMap_eq' hw
  have hpush : Algebra.IsPushout K L A B := (CommRingCat.isPushout_iff_isPushout).mp hpo'.flip
  -- fraction fields
  haveI : IsFractionRing A X.left.functionField :=
    functionField_isFractionRing_of_isAffineOpen _ U hU
  haveI : IsFractionRing B (baseChangeCurve X L).left.functionField :=
    functionField_isFractionRing_of_isAffineOpen _ _ hV
  have hXA := ffStructMap_eq X U
  have hXB := ffStructMap_eq (baseChangeCurve X L) ((pr X L) ⁻¹ᵁ U)
  haveI : IsScalarTower K A X.left.functionField := IsScalarTower.of_algebraMap_eq' (by
    change ZInQ.LeafPush2.ffStructMap X = _
    rw [hXA]; rfl)
  have hLB : algebraMap L (baseChangeCurve X L).left.functionField =
      (algebraMap B (baseChangeCurve X L).left.functionField).comp (algebraMap L B) := by
    change ZInQ.LeafPush2.ffStructMap (baseChangeCurve X L) = _
    rw [hXB]
    rfl
  haveI : IsScalarTower K B (baseChangeCurve X L).left.functionField :=
    IsScalarTower.of_algebraMap_eq' (by
      rw [IsScalarTower.algebraMap_eq K L (baseChangeCurve X L).left.functionField, hLB,
        RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq K L B])
  -- the pushout isomorphism `A ⊗_K L ≅ B`
  haveI := hpush.symm
  let β : A ⊗[K] L →ₐ[K] B := ((Algebra.IsPushout.equiv K A L B).restrictScalars K).toAlgHom
  have hβ : Function.Bijective β := (Algebra.IsPushout.equiv K A L B).bijective
  have hβtmul : ∀ (a : A) (l : L), β (a ⊗ₜ[K] l) = algebraMap A B a * algebraMap L B l :=
    fun a l => Algebra.IsPushout.equiv_tmul K A L B a l
  -- the map of function fields
  have hgerm : ∀ a : A, (ffMap X L).hom (algebraMap A X.left.functionField a) =
      algebraMap B (baseChangeCurve X L).left.functionField (algebraMap A B a) := by
    intro a
    have := congrArg (fun f => f.hom a) (germ_ffMap X L U hηU hηV)
    exact this
  have hcomm : ∀ c : K, (ffMap X L).hom (algebraMap K X.left.functionField c) =
      algebraMap K (baseChangeCurve X L).left.functionField c := by
    intro c
    rw [IsScalarTower.algebraMap_apply K A X.left.functionField, hgerm,
      ← IsScalarTower.algebraMap_apply K A B, IsScalarTower.algebraMap_apply K L B,
      ← RingHom.comp_apply, ← hLB]
    rfl
  let ι : X.left.functionField →ₐ[K] (baseChangeCurve X L).left.functionField :=
    { (ffMap X L).hom with commutes' := hcomm }
  refine ⟨ι, productMap_bijective_of_fraction β hβ ι _ ?_ ?_⟩
  · intro a
    rw [hβtmul, map_one, mul_one]
    exact hgerm a
  · intro l
    rw [hβtmul, map_one, one_mul]
    exact RingHom.congr_fun hLB l

/-- **`BelyiBaseChange` from Stichtenoth's theorem (glue, proved).** -/
theorem belyiBaseChange_of_unramified (hS : ConstantFieldExtensionUnramified) : BelyiBaseChange := by
  intro K _ _ X hX _ t ht d hd hd0
  have : SmoothOfRelativeDimension 1 X.hom := hX.smooth
  have : GeometricallyConnected X.hom := hX.geomConnected
  have : Smooth X.hom := SmoothOfRelativeDimension.smooth 1 X.hom
  have : GeometricallyIntegral X.hom :=
    TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral X.hom
  haveI hint : IsIntegral (baseChangeCurve X (AlgebraicClosure K)).left :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ (isPullback_pr X (AlgebraicClosure K))
  obtain ⟨ι, hbij⟩ := functionField_baseChange X (AlgebraicClosure K)
  letI := ZInQ.LeafPush2.ffAlgebra X
  letI := ZInQ.LeafPush2.ffAlgebra (baseChangeCurve X (AlgebraicClosure K))
  letI iKM : Algebra K (baseChangeCurve X (AlgebraicClosure K)).left.functionField :=
    ((algebraMap (AlgebraicClosure K) _).comp (algebraMap K (AlgebraicClosure K))).toAlgebra
  haveI : IsScalarTower K (AlgebraicClosure K)
      (baseChangeCurve X (AlgebraicClosure K)).left.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨h1, h2⟩ := isBelyiFunction_baseChange hS ι hbij t ht d hd hd0
  exact ⟨hint, ι t, h1, h2⟩

end JavanpeykarDict


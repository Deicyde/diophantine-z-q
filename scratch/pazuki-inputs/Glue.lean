import ZInQKernel.Contrib.OneProof.PazukiAlg

noncomputable section

namespace PazukiInputs

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory MonObj
open ZInQ.LeafPush2 (CPts)
open AvSplit.HomLatticeAN3 (bcC ptE)
open PazukiDict (OnZeroLocus IsSymmPrincipal liftPt specMap_comp_eq)
open PazukiAlg (pullbackSec support_zeroLocus_pullbackSec)

variable {K K' : Type} [Field K] [Field K'] [Algebra K K']

/-- The projection `A ×_{K,σ} ℂ → A ×_K K'` over `σ' : K' → ℂ` (on the fibre products). -/
def bcMap' (A : PkgI3.AbVar K) (σ : K →+* ℂ) (σ' : K' →+* ℂ) (hσ : σ'.comp (algebraMap K K') = σ) :
    pullback A.X.hom (Spec.map (CommRingCat.ofHom σ)) ⟶
      pullback A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap K K'))) :=
  pullback.lift (pullback.fst A.X.hom (Spec.map (CommRingCat.ofHom σ)))
    (pullback.snd A.X.hom (Spec.map (CommRingCat.ofHom σ)) ≫ Spec.map (CommRingCat.ofHom σ')) (by
      have h := pullback.condition (f := A.X.hom) (g := Spec.map (CommRingCat.ofHom σ))
      exact h.trans ((congrArg (fun g => pullback.snd A.X.hom (Spec.map (CommRingCat.ofHom σ)) ≫ g)
        (specMap_comp_eq σ σ' hσ).symm).trans (Category.assoc _ _ _).symm))

/-- The projection `A_ℂ = A ×_{K,σ} ℂ → A_{K'} = A ×_K K'` over `σ' : K' → ℂ`. -/
def bcMap (A : PkgI3.AbVar K) (σ : K →+* ℂ) (σ' : K' →+* ℂ) (hσ : σ'.comp (algebraMap K K') = σ) :
    (bcC A σ).X.left ⟶ (A.baseChange K').X.left :=
  bcMap' A σ σ' hσ

theorem liftPt_ptE (A : PkgI3.AbVar K) (σ : K →+* ℂ) (σ' : K' →+* ℂ)
    (hσ : σ'.comp (algebraMap K K') = σ) (p : CPts (bcC A σ) (RingHom.id ℂ)) :
    liftPt A σ σ' hσ (ptE A σ p) = p.left ≫ bcMap A σ σ' hσ := by
  apply pullback.hom_ext
  · unfold liftPt bcMap bcMap'
    erw [Category.assoc, pullback.lift_fst, pullback.lift_fst, AvSplit.HomLatticeAN3.ptE_left]
    rfl
  · have h : p.left ≫ pullback.snd A.X.hom (Spec.map (CommRingCat.ofHom σ)) = 𝟙 _ := by
      have := Over.w p
      refine this.trans ?_
      change Spec.map (CommRingCat.ofHom (RingHom.id ℂ)) = 𝟙 _
      rw [CommRingCat.ofHom_id, Spec.map_id]
    unfold liftPt bcMap bcMap'
    erw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
    exact ((congrArg (fun f => f ≫ Spec.map (CommRingCat.ofHom σ')) h).trans
      (Category.id_comp _)).symm.trans (Category.assoc _ _ _)

theorem bcMap_isPullback (A : PkgI3.AbVar K) (σ : K →+* ℂ) (σ' : K' →+* ℂ)
    (hσ : σ'.comp (algebraMap K K') = σ) :
    IsPullback (bcMap' A σ σ' hσ) (pullback.snd A.X.hom (Spec.map (CommRingCat.ofHom σ)))
      (pullback.snd A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap K K'))))
      (Spec.map (CommRingCat.ofHom σ')) := by
  refine IsPullback.of_right (h₁₂ := pullback.fst A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap K K'))))
    (v₁₃ := A.X.hom) (h₂₂ := Spec.map (CommRingCat.ofHom (algebraMap K K'))) ?_ ?_
    (IsPullback.of_hasPullback _ _)
  · rw [bcMap', pullback.lift_fst]
    have key : ∀ g' : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of K),
        g' = Spec.map (CommRingCat.ofHom σ) →
        IsPullback (pullback.fst A.X.hom (Spec.map (CommRingCat.ofHom σ)))
          (pullback.snd A.X.hom (Spec.map (CommRingCat.ofHom σ))) A.X.hom g' := by
      rintro g' rfl
      exact IsPullback.of_hasPullback _ _
    exact key _ (specMap_comp_eq σ σ' hσ)
  · rw [bcMap', pullback.lift_snd]

instance (L : Type) [Field L] : Subsingleton (Spec (CommRingCat.of L)) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum L))

theorem surjective_bcMap (A : PkgI3.AbVar K) (σ : K →+* ℂ) (σ' : K' →+* ℂ)
    (hσ : σ'.comp (algebraMap K K') = σ) : Surjective (bcMap A σ σ' hσ) := by
  have hs : Surjective (Spec.map (CommRingCat.ofHom σ')) :=
    ⟨fun x => ⟨IsLocalRing.closedPoint ℂ, Subsingleton.elim _ _⟩⟩
  exact MorphismProperty.of_isPullback (P := @Surjective) (bcMap_isPullback A σ σ' hσ).flip hs


/-! ## The core statement and the section glue -/

/-- **The core of the arithmetic half: a symmetric principal polarization of `A_ℂ` is defined over a number
field.** -/
def SymmPrincipalDefinedOver : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (L : (bcC A σ).X.left.Pic),
    IsSymmPrincipal (bcC A σ) L →
    ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (σ' : K' →+* ℂ)
      (hσ : σ'.comp (algebraMap K K') = σ) (M : (A.baseChange K').X.left.Pic),
      IsSymmPrincipal (A.baseChange K') M ∧ Scheme.Pic.map (bcMap A σ σ' hσ) M = L

open Scheme.Modules in
theorem onZeroLocus_zero {X : Scheme.{0}} {M : X.Modules} [M.IsInvertible]
    (q : Spec (CommRingCat.of ℂ) ⟶ X) : OnZeroLocus (0 : 𝟙_ X.Modules ⟶ M) q := by
  intro x
  rw [(Hom.zeroLocus_eq_bot_iff _).2 rfl, Scheme.IdealSheafData.support_bot]
  trivial

open Scheme.Modules in
/-- A section whose pullback along a surjective morphism to a reduced scheme vanishes is zero. -/
theorem eq_zero_of_pullbackSec_eq_zero {X Y : Scheme.{0}} [IsReduced Y] (f : X ⟶ Y) [Surjective f]
    {N : Y.Modules} {N' : X.Modules} [N.IsInvertible] [N'.IsInvertible]
    (iN : N' ≅ (Scheme.Modules.pullback f).obj N) (t : 𝟙_ Y.Modules ⟶ N)
    (h : pullbackSec f iN t = 0) : t = 0 := by
  have hs := support_zeroLocus_pullbackSec f iN t
  rw [h, (Hom.zeroLocus_eq_bot_iff _).2 rfl, Scheme.IdealSheafData.support_bot] at hs
  refine (Hom.zeroLocus_eq_bot_iff _).1 ((Scheme.IdealSheafData.support_eq_top_iff).1 ?_)
  refine eq_top_iff.2 fun y _ => ?_
  obtain ⟨x, rfl⟩ := f.surjective y
  have hx : x ∈ ((⊤ : TopologicalSpace.Closeds X) : Set X) := trivial
  rw [hs] at hx
  exact hx

theorem isIntegral_abVar {L : Type} [Field L] (B : PkgI3.AbVar L) : IsIntegral B.X.left :=
  GeometricallyIntegral.isIntegral_of_subsingleton B.X.hom

theorem isField_Γ_abVar {L : Type} [Field L] (B : PkgI3.AbVar L) : IsField Γ(B.X.left, ⊤) := by
  have := isIntegral_abVar B
  exact isField_of_universallyClosed_of_isField (Field.toIsField L) B.X.hom

open Scheme.Modules in
/-- If `s = μ ≫ t` and `t = μ' ≫ s`, the two sections have the same zero locus. -/
theorem zeroLocus_eq_of_factor {X : Scheme.{0}} {M : X.Modules} [M.IsInvertible]
    (s t : 𝟙_ X.Modules ⟶ M) (u u' : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules) (h1 : s = u ≫ t) (h2 : t = u' ≫ s) :
    Hom.zeroLocus s = Hom.zeroLocus t := by
  apply le_antisymm
  · conv_lhs => rw [h1]
    exact Hom.zeroLocus_comp_le u t
  · conv_lhs => rw [h2]
    exact Hom.zeroLocus_comp_le u' s


/-- Multiplication by a global function `c`, as an endomorphism of `𝒪_X`. -/
def scal {X : Scheme.{0}} (c : Γ(X, ⊤)) : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules :=
  Scheme.Modules.homOfGlobalSection (𝟙_ X.Modules) c

open Scheme.Modules in
theorem scal_comp_app {X : Scheme.{0}} {M : X.Modules} (c : Γ(X, ⊤))
    (t : 𝟙_ X.Modules ⟶ M) :
    (scal c ≫ t).app ⊤ (1 : Γ(X, ⊤)) = c • t.app ⊤ (1 : Γ(X, ⊤)) := by
  have hmid : (homOfGlobalSection (𝟙_ X.Modules) c).app ⊤ (1 : Γ(X, ⊤)) = c • (1 : Γ(X, ⊤)) := by
    refine (homOfGlobalSection_app (𝟙_ X.Modules) c ⊤ (1 : Γ(X, ⊤))).trans ?_
    have e : (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 _ := rfl
    rw [e, CategoryTheory.Functor.map_id, one_smul]
    change c = c * 1
    exact (_root_.mul_one c).symm
  change t.app ⊤ ((homOfGlobalSection (𝟙_ X.Modules) c).app ⊤ (1 : Γ(X, ⊤))) = _
  rw [hmid]
  exact Hom.app_smul t c (1 : Γ(X, ⊤))

open Scheme.Modules in
/-- **Glue (proved): `SymmPrincipalDescends` from its core `SymmPrincipalDefinedOver`.** -/
theorem symmPrincipalDescends_of_definedOver (h : SymmPrincipalDefinedOver) :
    PazukiDict.SymmPrincipalDescends := by
  intro K _ _ A σ L s hL
  obtain ⟨K', iF, iN, iA, σ', hσ, M, hM, rfl⟩ := h K A σ L hL
  by_cases hs : s = 0
  · refine ⟨K', iF, iN, iA, σ', hσ, M, 0, hM, fun p => ?_⟩
    subst hs
    exact iff_of_true (onZeroLocus_zero _) (onZeroLocus_zero _)
  · let q := bcMap A σ σ' hσ
    let M₀ := (fromSkeleton (A.baseChange K').X.left.Modules).obj M.val
    let iE : (fromSkeleton (bcC A σ).X.left.Modules).obj (Scheme.Pic.map q M).val ≅
        (Scheme.Modules.pullback q).obj M₀ := Scheme.Pic.mkIso ((Scheme.Modules.pullback q).obj M₀)
    have hpos : 0 < Module.finrank Γ((A.baseChange K').X.left, ⊤) Γ(M₀, ⊤) := by
      rw [hM.2.2]; exact one_pos
    have := Module.nontrivial_of_finrank_pos hpos
    obtain ⟨u, hu⟩ := exists_ne (0 : Γ(M₀, ⊤))
    let s' : 𝟙_ (A.baseChange K').X.left.Modules ⟶ M₀ := homOfGlobalSection M₀ u
    have hs' : s' ≠ 0 := by
      intro h0
      apply hu
      rw [← (unitHomAddEquiv M₀).apply_symm_apply u]
      change unitHomAddEquiv M₀ s' = 0
      rw [h0, map_zero]
    let t := pullbackSec q iE s'
    have : IsReduced (A.baseChange K').X.left := by
      have := isIntegral_abVar (A.baseChange K'); infer_instance
    have : Surjective q := surjective_bcMap A σ σ' hσ
    have ht : t ≠ 0 := fun h0 => hs' (eq_zero_of_pullbackSec_eq_zero q iE s' h0)
    let _ : Field Γ((bcC A σ).X.left, ⊤) := (isField_Γ_abVar (bcC A σ)).toField
    have hut : t.app ⊤ (1 : Γ((bcC A σ).X.left, ⊤)) ≠ 0 := by
      intro h0
      apply ht
      apply (unitHomAddEquiv _).injective
      rw [unitHomAddEquiv_apply, h0, map_zero]
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hut).1 hL.2.2 (s.app ⊤ (1 : Γ((bcC A σ).X.left, ⊤)))
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply hs
      apply (unitHomAddEquiv _).injective
      rw [unitHomAddEquiv_apply, ← hc, zero_smul, map_zero]
    have h1 : s = scal c ≫ t := by
      apply (unitHomAddEquiv _).injective
      rw [unitHomAddEquiv_apply, unitHomAddEquiv_apply, scal_comp_app, hc]
    have h2 : t = scal c⁻¹ ≫ s := by
      apply (unitHomAddEquiv _).injective
      rw [unitHomAddEquiv_apply, unitHomAddEquiv_apply, scal_comp_app, ← hc, smul_smul,
        inv_mul_cancel₀ hc0, one_smul]
    refine ⟨K', iF, iN, iA, σ', hσ, M, s', hM, fun p => ?_⟩
    rw [liftPt_ptE]
    unfold OnZeroLocus
    rw [zeroLocus_eq_of_factor s t _ _ h1 h2, support_zeroLocus_pullbackSec]
    rfl

end PazukiInputs

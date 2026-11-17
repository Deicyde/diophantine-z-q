/-
Copyright (c) 2026 H5/NOS Round-2 lane4 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

H5 Step-2 final small obligations for C3 (statements used verbatim through the imports), PROVED
natively. SOURCE ONLY, UNCOMPILED. Native HELD. Universe u, default options.

* `fromSpecImageCompat` (`Step2B1/L1b.lean` 036834de, `FromSpecImageCompat`): Mathlib
  `IsAffineOpen.SpecMap_appLE_fromSpec` with `appIso_hom'`, evaluated at the point.
* `integralOnIrreducible` (`Step2B2/Minkowski.lean` d42be255, `IntegralOnIrreducible`): exactly
  `NonFiniteContracts.isIntegral_subscheme_vanishingIdeal` (batch 11).
* `pulledSectionsSpan` (`Step2B3/FieldDescent.lean` 1c49e9c7, `PulledSectionsSpan`):
  1. `surjective_sectionsModuleBaseChange_top`: the GLOBAL section base change
     `Γ(Spec K) ⊗ Γ(X, L) → Γ(X_K, L_K)` is surjective. W07 proves flat base change in degree 0
     for the quasi-compact open `⊤` (`bijective_cohomologyBaseChange_of_isCompact`), and the
     identification of the degree-0 base change map with the section base change map in W07
     `bijective_cohomologyBaseChange_zero_of_isAffineOpen` does not use affineness: it is
     repeated here verbatim for the open `⊤`.
  2. `Γ(X, L)` is finite over `k` (W07 `hasFiniteH_of_isProper` and `H.zeroLinearEquiv`), so a
     finite family `s` spans; padding by `0` gives the `Fin (m + 1)` family.
  3. Every element of the tensor product maps to a `K`-combination of the pulled-back `s j`
     (tensor induction; `ΓSpecIso` naturality for the scalars).
Truth: all TRUE (these are the proofs).
-/
import ZInQKernel.Contrib.CloudR2NOS.Step2B1.L1b
import ZInQKernel.Contrib.CloudR2NOS.Step2B2.Minkowski
import ZInQKernel.Contrib.CloudR2NOS.Step2B3.FieldDescent
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.NonFiniteContracts
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.FlatBaseChange
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.Proper
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace TensorProduct
open CategoryTheory.Abelian.Ext

namespace ZInQ.Contrib.CloudR2NOS.ClosedSection.Step2Small

/-! ### `FromSpecImageCompat` and `IntegralOnIrreducible` -/

/-- **`FromSpecImageCompat` proved.** -/
theorem fromSpecImageCompat : ZInQ.Contrib.CloudR2NOS.Step2B1.FromSpecImageCompat.{u} := by
  intro X φ _ U p
  have h := IsAffineOpen.SpecMap_appLE_fromSpec φ (U.2.image_of_isOpenImmersion φ) U.2
    (φ.preimage_image_eq U.1).ge
  rw [← Scheme.Hom.appIso_hom'] at h
  have h1 := congrArg (fun ψ : Spec Γ(X, U.1) ⟶ X => ψ.base p) h
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h1
  exact h1

/-- **`IntegralOnIrreducible` proved.** -/
theorem integralOnIrreducible : ZInQ.Contrib.CloudR2NOS.Step2B2.IntegralOnIrreducible.{u} :=
  fun Z hZ => NonFiniteContracts.isIntegral_subscheme_vanishingIdeal Z hZ

/-! ### Global flat base change of sections -/

section GlobalBaseChange

variable {X Y S T : Scheme.{u}} {f : X ⟶ S} {f' : Y ⟶ T} {g : T ⟶ S} {g' : Y ⟶ X}
  (cart : IsPullback g' f' f g) (F : X.Modules) [Algebra Γ(S, ⊤) Γ(T, ⊤)]
  (hg : algebraMap Γ(S, ⊤) Γ(T, ⊤) = g.appTop.hom)

include cart hg in
/-- The section base change `Γ(T, ⊤) ⊗ Γ(F, ⊤) → Γ(g'^*F, ⊤)` is surjective for a flat base
change of a quasi-compact quasi-separated `f` over affine bases. -/
theorem surjective_sectionsModuleBaseChange_top [IsAffine S] [IsAffine T]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F] [Flat g] [QuasiSeparated f]
    [QuasiCompact f] :
    Function.Surjective (Scheme.Modules.sectionsModuleBaseChange cart F hg ⊤) := by
  -- the identification of W07 `bijective_cohomologyBaseChange_zero_of_isAffineOpen`, for `⊤`
  have key : ⇑(Scheme.Modules.pushforwardSectionsAddEquiv f' g' F ⊤) ∘
      ⇑(Scheme.Modules.cohomologyBaseChange cart F hg (TopCat.Sheaf.freeSheaf ⊤) 0) =
      ⇑(Scheme.Modules.sectionsModuleBaseChange cart F hg ⊤) ∘
        ⇑((Scheme.Modules.sectionsLinearEquiv F ⊤).lTensor Γ(T, ⊤)) := by
    funext tensorElement
    induction tensorElement using TensorProduct.induction_on with
    | zero => simp only [Function.comp_apply, map_zero]
    | add t t' hz hz' =>
      simp only [Function.comp_apply, map_add] at hz hz' ⊢
      rw [hz, hz']
    | tmul extensionScalar element =>
      change TopCat.Sheaf.extFreeSheafZeroAddEquiv ⊤ _ ((WithAction.toExt _ element).comp
          (mk₀ (Scheme.Modules.toSheafUnit g' F ≫
            (Scheme.Modules.pushforwardPullbackAction f' g' F extensionScalar).asHom))
          (add_zero 0)) =
        Scheme.Modules.sectionsModuleBaseChange cart F hg ⊤
          (extensionScalar ⊗ₜ Scheme.Modules.sectionsLinearEquiv F ⊤ element)
      rw [TopCat.Sheaf.extFreeSheafZeroAddEquiv_comp_mk₀,
        Scheme.Modules.sectionsModuleBaseChange_tmul]
      rfl
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have hbij := Scheme.Modules.bijective_cohomologyBaseChange_of_isCompact cart F hg
    (openSubset := ⊤) (by rw [TopologicalSpace.Opens.coe_top]; exact isCompact_univ) 0
  intro τ
  obtain ⟨y, hy⟩ :=
    ((Scheme.Modules.pushforwardSectionsAddEquiv f' g' F ⊤).bijective.comp hbij).2 τ
  exact ⟨(Scheme.Modules.sectionsLinearEquiv F ⊤).lTensor Γ(T, ⊤) y,
    (congrFun key y).symm.trans hy⟩

end GlobalBaseChange

/-- The base action on `sectionsModule h G ⊤` is the action through `h.appTop`. -/
theorem smul_sectionsModule_top {Z W : Scheme.{u}} (h : Z ⟶ W) (G : Z.Modules) (a : Γ(W, ⊤))
    (y : Γ(G, ⊤)) :
    (a • (show Scheme.Modules.sectionsModule h G ⊤ from y) : Scheme.Modules.sectionsModule h G ⊤) =
      (h.appTop a • y : Γ(G, ⊤)) := by
  change (h.appTop ≫ Z.presheaf.map (⊤ : Z.Opens).leTop.op).hom a • y = _
  rw [show (⊤ : Z.Opens).leTop = 𝟙 ⊤ from rfl, op_id, Z.presheaf.map_id, Category.comp_id]

/-- **`PulledSectionsSpan` proved.** -/
theorem pulledSectionsSpan : ZInQ.Contrib.CloudR2NOS.Step2B3.PulledSectionsSpan.{u} := by
  intro k K _ _ _ X f _ L _
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let p := pullback.fst f g
  let q := pullback.snd f g
  have cart : IsPullback p q f g := IsPullback.of_hasPullback f g
  letI : Algebra Γ(Spec (CommRingCat.of k), ⊤) Γ(Spec (CommRingCat.of K), ⊤) :=
    g.appTop.hom.toAlgebra
  have hg : algebraMap Γ(Spec (CommRingCat.of k), ⊤) Γ(Spec (CommRingCat.of K), ⊤) =
      g.appTop.hom := rfl
  haveI : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) L :=
    SheafOfModules.IsInvertible.isQuasicoherent inferInstance
  haveI : L.IsFiniteLocallyFree := SheafOfModules.IsInvertible.isFiniteLocallyFree L
  haveI : L.IsFinitePresentation := inferInstance
  -- (1) global section base change is surjective
  have hsurj := surjective_sectionsModuleBaseChange_top cart L hg
  -- (2) a finite family spanning `Γ(X, L)` over `k`
  letI : Module k (L.H 0) := Scheme.Modules.moduleHOfSpec f L 0
  haveI : Module.Finite k (L.H 0) := Scheme.Modules.hasFiniteH_of_isProper f L 0
  obtain ⟨n, x, hx⟩ := Module.Finite.exists_fin (R := k) (M := L.H 0)
  let s0 : Fin n → Γ(L, ⊤) := fun j => Scheme.Modules.H.zeroLinearEquiv L (x j)
  have hspan : ∀ m : Γ(L, ⊤), ∃ c : Fin n → k,
      m = ∑ j, f.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv (c j)) • s0 j := by
    intro m
    have hm : (Scheme.Modules.H.zeroLinearEquiv L).symm m ∈ Submodule.span k (Set.range x) := by
      rw [hx]
      trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).1 hm
    refine ⟨c, ?_⟩
    have h1 := congrArg (Scheme.Modules.H.zeroLinearEquiv L) hc
    rw [LinearEquiv.apply_symm_apply, map_sum] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    show Scheme.Modules.H.zeroLinearEquiv L
        (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv (c j)) • x j) = _
    exact LinearEquiv.map_smul _ _ _
  -- the same family, with the action of `Γ(Spec k, ⊤)` on `sectionsModule f L ⊤`
  have hspanA : ∀ m : Scheme.Modules.sectionsModule f L ⊤, ∃ c : Fin n → k,
      m = ∑ j, (Scheme.ΓSpecIso (CommRingCat.of k)).inv (c j) •
        (show Scheme.Modules.sectionsModule f L ⊤ from s0 j) := by
    intro m
    obtain ⟨c, hc⟩ := hspan m
    refine ⟨c, hc.trans (Finset.sum_congr rfl fun j _ => ?_)⟩
    exact (smul_sectionsModule_top f L _ (s0 j)).symm
  -- scalar compatibility of the pullback square
  have hscal : ∀ c : k, q.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv (algebraMap k K c)) =
      q.appTop (g.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)) := by
    intro c
    have h := ConcreteCategory.congr_hom
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k K))) c
    simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom] at h
    rw [h]
  -- (3) every tensor maps to a `K`-combination of the pulled-back family
  refine ⟨n, Fin.cons 0 s0, fun τ => ?_⟩
  suffices H : ∀ t : Γ(Spec (CommRingCat.of K), ⊤) ⊗[Γ(Spec (CommRingCat.of k), ⊤)]
        Scheme.Modules.sectionsModule f L ⊤, ∃ c : Fin (n + 1) → K,
      (Scheme.Modules.sectionsModuleBaseChange cart L hg ⊤ t : Γ((Scheme.Modules.pullback p).obj L, ⊤)) =
        ∑ j, (q.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv (c j))) •
          ZInQ.Contrib.CloudR2NOS.ClosedSection.pullbackSection p ((Fin.cons 0 s0 : Fin (n + 1) → Γ(L, ⊤)) j) by
    obtain ⟨t, ht⟩ := hsurj (show Scheme.Modules.sectionsModule q ((Scheme.Modules.pullback p).obj L)
      (p ⁻¹ᵁ ⊤) from τ)
    obtain ⟨c, hc⟩ := H t
    exact ⟨c, ht.symm.trans hc⟩
  intro t
  induction t using TensorProduct.induction_on with
  | zero =>
    refine ⟨0, ?_⟩
    simp only [map_zero, Pi.zero_apply, zero_smul, Finset.sum_const_zero]
  | add t₁ t₂ h₁ h₂ =>
    obtain ⟨c₁, hc₁⟩ := h₁
    obtain ⟨c₂, hc₂⟩ := h₂
    refine ⟨c₁ + c₂, ?_⟩
    rw [map_add]
    change (Scheme.Modules.sectionsModuleBaseChange cart L hg ⊤ t₁ :
        Γ((Scheme.Modules.pullback p).obj L, ⊤)) +
      Scheme.Modules.sectionsModuleBaseChange cart L hg ⊤ t₂ = _
    rw [hc₁, hc₂, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Pi.add_apply, map_add, map_add, add_smul]
  | tmul b m =>
    obtain ⟨c, hc⟩ := hspanA m
    refine ⟨Fin.cons 0 fun j => algebraMap k K (c j) * (Scheme.ΓSpecIso (CommRingCat.of K)).hom b,
      ?_⟩
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, map_zero, zero_smul, zero_add]
    rw [hc, TensorProduct.tmul_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← TensorProduct.smul_tmul, Scheme.Modules.sectionsModuleBaseChange_tmul]
    change ((((Scheme.ΓSpecIso (CommRingCat.of k)).inv (c j)) • b) •
        (show Scheme.Modules.sectionsModule q ((Scheme.Modules.pullback p).obj L) ⊤ from
          ZInQ.Contrib.CloudR2NOS.ClosedSection.pullbackSection p (s0 j)) :
        Scheme.Modules.sectionsModule q ((Scheme.Modules.pullback p).obj L) ⊤) = _
    rw [smul_sectionsModule_top q ((Scheme.Modules.pullback p).obj L), Algebra.smul_def, hg,
      map_mul, map_mul, map_mul, Iso.hom_inv_id_apply, hscal]
    rfl

end ZInQ.Contrib.CloudR2NOS.ClosedSection.Step2Small

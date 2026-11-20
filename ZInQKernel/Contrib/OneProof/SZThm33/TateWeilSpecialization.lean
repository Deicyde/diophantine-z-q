import ZInQKernel.Contrib.OneProof.SZThm33.ValuationToricPairing
import ZInQKernel.Contrib.OneProof.SZThm33.ConnectedTateLift
import ZInQKernel.Contrib.OneProof.SZThm33.SemistableWeilLevels
import ZInQKernel.Contrib.OneProof.SZThm33.ToricIdentitySpecialFibre
import ZInQKernel.Contrib.OneProof.DirectWeil.VeryAmplePolarizationKernel

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReductSplit SmoothGroup PicDict.DirectPairing ZInQ.HeightSplit ZInQ.FaltingsRestate
open ZInQ.Contrib.CloudR2Poincare.L2 (VeryAmple)
open scoped CategoryTheory.MonObj

namespace SZRaynaud

private theorem tateEquiv_reflexive {K E : Type} [Field K] [Field E] [Algebra K E]
    (A : PkgI3.AbVar K) {ℓ : ℕ} [Fact ℓ.Prime] :
    tateEquiv A (AlgEquiv.refl : E ≃ₐ[K] E) (ℓ := ℓ) = LinearEquiv.refl ℤ_[ℓ] (TΩ A E ℓ) := by
  ext x : 1
  apply Subtype.ext
  funext n
  apply Additive.toMul.injective
  apply Over.OverMorphism.ext
  let z : Spec (CommRingCat.of E) ⟶ A.X.left := (Additive.toMul (x.1 n)).left
  change Spec.map (CommRingCat.ofHom (RingHom.id E)) ≫ z = z
  rw [show CommRingCat.ofHom (RingHom.id E) = 𝟙 (CommRingCat.of E) from rfl,
    Spec.map_id, Category.id_comp]

namespace Ambient

variable {K : Type} [Field K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  {w : ValuationSubring (AlgebraicClosure K)} (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O)
  (A : PkgI3.AbVar K) (H M : GroupModelO A O)
  {ℓ : ℕ} [Fact ℓ.Prime] (hu : IsUnit (ℓ : O))

attribute [local instance] isCommMonObj_geomSpecialFibre
attribute [local instance] isCommMonObj_groupModelO

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2400000 in
include hw hu in
/-- A relative polarization on an identity model gives the two-factor inertia
condition for every algebraic-closure prolongation over its base. -/
theorem levelTwo_of_semistable_identityModel (hM : M.IsNeronModel) (hS : M.IsSemistable)
    (i : H.G ⟶ M.G) [IsOpenImmersion i.left] [IsMonHom i]
    (hi : Set.range i.left = CToPrinted.idCompSet M.G)
    [GeometricallyIntegral H.G.hom]
    (hg : (Over.pullback (jO O)).map i ≫ M.gen.hom = H.gen.hom)
    (L : H.G.left.Modules) [SheafOfModules.IsInvertible L]
    (hL : VeryAmple A.X.hom (Relative.genericModelLine H L)) :
    ∀ σ : (AlgebraicClosure K) ≃ₐ[K] (AlgebraicClosure K), PkgI2.IsInertia w σ →
      ∀ τ : (AlgebraicClosure K) ≃ₐ[K] (AlgebraicClosure K), PkgI2.IsInertia w τ →
        ∀ x : VΩ A (AlgebraicClosure K) ℓ,
          galVΩ A ℓ τ (galVΩ A ℓ σ x - x) = galVΩ A ℓ σ x - x := by
  obtain ⟨U, hGrp, inc, hOpen, hMon, hConn, B, π, hπ, hflat, hsurj, r, e, he, hk, hn⟩ := hS
  have : SheafOfModules.IsInvertible (Relative.genericModelLine H L) := by
    unfold Relative.genericModelLine
    infer_instance
  let Lη := Scheme.Pic.mk (Relative.genericModelLine H L)
  have hfin : {x : A.Pt (AlgebraicClosure K) | polarization A Lη x = 1}.Finite :=
    finite_polarization_kernel_veryAmple A _ hL
  have hℓ : (ℓ : K) ≠ 0 := by
    simpa only [map_natCast] using (hu.map (algebraMap O K)).ne_zero
  refine levelTwo_of_semistable_weil_levels hw A M hu hM U inc B π r e he hk
    (fun R S _ _ _ _ f t => hn R S f t) Lη hfin AlgEquiv.refl hℓ ?_
  obtain ⟨toric, htoric, hfac⟩ := exists_identitySpecialToricInclusion H M i hi inc r e
    (fun R S _ _ _ _ f t => hn R S f t)
  let f := geomSpecialModelMap H M i
  have : IsMonHom f := geomSpecialModelMap_isMonHom A H M i
  have : IsOpenImmersion f.left := ZInQ.H5Glue.isOpenImmersion_pullback_map (Spec.map (CommRingCat.ofHom (algebraMap O (ResBarO O)))) i
  intro x y k
  let yM := integralTatePointMap inc (e (ResBarO O)) y
  obtain ⟨xH, _, hxH⟩ := exists_connectedModelTate hw A H M hu i hg x
  obtain ⟨yH, hyH₀, hyH⟩ := exists_connectedModelTate hw A H M hu i hg yM
  obtain ⟨xV, hxres, hxgen⟩ := exists_geomSpecialLiftTate hw A H hu xH
  obtain ⟨yV, hyres, hygen⟩ := exists_geomSpecialLiftTate hw A H hu yH
  let xw := Additive.toMul (xV.1 k)
  let yw := Additive.toMul (yV.1 k)
  let xb := Additive.toMul (xH.1 k)
  let yb := Additive.toMul (yH.1 k)
  have hxw : xw ^ (ℓ ^ k) = 1 := pow_smul_tate xV k
  have hyw : yw ^ (ℓ ^ k) = 1 := pow_smul_tate yV k
  have hxb : xb ^ (ℓ ^ k) = 1 := pow_smul_tate xH k
  have hxR : restrictPoint res xw = geomSpecialPointEquiv hw A H xb :=
    congrArg (fun t => Additive.toMul (t.1 k)) hxres
  have hyR : restrictPoint res yw = geomSpecialPointEquiv hw A H yb :=
    congrArg (fun t => Additive.toMul (t.1 k)) hyres
  let z : (algPt (ResBarO O) (ResBarO O)) ⟶ splitTorus (ResBarO O) r := (splitTorusPoints (ResBarO O)).symm (Additive.toMul (y.1 k))
  have hz : z ^ (ℓ ^ k) = 1 := by
    change ((splitTorusPoints (ResBarO O)).symm (Additive.toMul (y.1 k))) ^ (ℓ ^ k) = 1
    have hp : (Additive.toMul (y.1 k)) ^ (ℓ ^ k) = 1 := pow_smul_tate y k
    rw [← map_pow, hp, map_one]
  have hycomp : yb ≫ f = e (ResBarO O) (Additive.toMul (y.1 k)) ≫ inc :=
    congrArg (fun t => Additive.toMul (t.1 k)) hyH₀
  have hyb : z ≫ toric = yb := by
    apply Over.OverMorphism.ext
    apply (cancel_mono f.left).mp
    have hzcomp := hfac (ResBarO O) z
    have hez : splitTorusPoints (ResBarO O) z = Additive.toMul (y.1 k) :=
      (splitTorusPoints (ResBarO O)).apply_symm_apply _
    change (z ≫ toric).left ≫ f.left = yb.left ≫ f.left
    exact congrArg Over.Hom.left ((Category.assoc _ _ _).trans
      (hzcomp.trans ((congrArg (fun t => e (ResBarO O) t ≫ inc) hez).trans hycomp.symm)))
  have hnpos : 0 < ℓ ^ k := pow_pos (Fact.out : ℓ.Prime).pos k
  have hnunit : IsUnit ((ℓ ^ k : ℕ) : O) := by simpa only [Nat.cast_pow] using hu.pow k
  have hnchar : ((ℓ ^ k : ℕ) : K) ≠ 0 := by simpa only [Nat.cast_pow] using pow_ne_zero k hℓ
  have hv := valuationWeilValue_eq_one_of_toric hw A H hnpos hnunit hnchar toric yw xw hyw hxw
    z xb hz hxb (by rw [hyb]; exact hyR) hxR L
  have hxcoord : levelPoint A (geomSpecialEmbedTate hw A M hu x) k =
      valuationTorsionPoint hw A H xw hxw := by
    apply Subtype.ext
    exact congrArg (fun t : TΩ A (AlgebraicClosure K) ℓ => t.1 k) (hxH.symm.trans hxgen)
  have hycoord : levelPoint A (geomSpecialEmbedTate hw A M hu yM) k =
      valuationTorsionPoint hw A H yw hyw := by
    apply Subtype.ext
    exact congrArg (fun t : TΩ A (AlgebraicClosure K) ℓ => t.1 k) (hyH.symm.trans hygen)
  simp only [tateEquiv_reflexive, LinearEquiv.refl_symm, LinearEquiv.refl_apply]
  change value A Lη hnpos hnchar (levelPoint A (geomSpecialEmbedTate hw A M hu x) k)
    (levelPoint A (geomSpecialEmbedTate hw A M hu yM) k) = 1
  rw [hxcoord, hycoord]
  exact value_eq_one_of_swap A Lη hnpos hnchar _ _ hv

end Ambient
end SZRaynaud

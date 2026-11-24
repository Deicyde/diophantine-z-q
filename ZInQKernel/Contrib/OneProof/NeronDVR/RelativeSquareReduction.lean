import ZInQKernel.Contrib.OneProof.NeronDVR.CartierEffectivity
import ZInQKernel.Contrib.OneProof.NeronDVR.EtaleStage
import ZInQKernel.Contrib.OneProof.NeronDVR.EffectiveDescent
import ZInQKernel.Contrib.OneProof.NeronDVR.GenericAffine
import ZInQKernel.Contrib.OneProof.NeronDVR.StrictHenselization
import ZInQKernel.Contrib.OneProof.NeronDVR.FibreDensityBaseChange
import ZInQKernel.Contrib.OneProof.NeronDVR.GenericIntegral
import ZInQKernel.Contrib.OneProof.NeronDVR.IdentitySubgroup
import ZInQKernel.Contrib.OneProof.NeronDVR.InvariantCartier

/-!
# Dedekind Néron existence from the relative square

The strictly henselian affine nonvanishing cover descends through the
étale stage using a compatible Cartier square on the overlaps.
-/

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory IsLocalRing
open scoped AlgebraicGeometry.Scheme.Modules
open ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective.TensorCofaces (baseMap)

namespace NeronDVR

open ZInQ.Contrib.GroupLawNeron ReductSplit ReductGlue NeronSH CToPrinted

/-- The relative theorem of the square for translations specializing to the
identity component of a strictly henselian Néron model. -/
def RelativeSquareStrictNeron : Prop :=
  ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [IsSepClosed (ResidueField R)]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    (_ : CToPrinted.IsNeronModelOver R K G) (A : PkgI3.AbVar K)
    (_ : (Over.pullback (genMap R K)).obj G ≅ A.X)
    (D : G.left.IdealSheafData) (hD : D.IsInvertible),
    letI := hD.isInvertible_dual_toModules
    let L := Scheme.Pic.mk D.toModulesᵛ
    ∀ (a : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G),
      a.left (IsLocalRing.closedPoint R) ∈ idCompSet G →
      Scheme.Pic.map (leftTranslationIso G a).hom.left L *
        Scheme.Pic.map (leftTranslationIso G a).inv.left L = L ^ 2

private theorem isIntegral_scheme_of_abelian_iso {K : Type} [Field K]
    (G : Over (Spec (CommRingCat.of K))) (A : PkgI3.AbVar K) (e : G ≅ A.X) : IsIntegral G.left := by
  have : IsIntegral ((Over.forget _).obj A.X) :=
    GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom
  exact IsIntegral.of_isIso ((Over.forget _).mapIso e.symm).hom

set_option backward.isDefEq.respectTransparency false in
/-- Néron descent from strict henselizations follows from the relative
square identity on the strict model. -/
theorem strictHenselizationDescent_of_relativeSquare
    (square : RelativeSquareStrictNeron) : NeronDescentFromStrictHenselization := by
  intro K _ O _ E _ _ P hP hSH A N hN e
  let _ : Algebra O P := (comapHom hP).toAlgebra
  let _ : Algebra O E := ((algebraMap K E).comp (algebraMap O K)).toAlgebra
  have : IsScalarTower O P E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower O K E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsLocalHom (algebraMap O P) := comapHom_isLocalHom hP
  have : IsDiscreteValuationRing P := hSH.1.1
  have : HenselianLocalRing P := hSH.1.2.1
  have : IsSepClosed (ResidueField P) := hSH.1.2.2
  have : Algebra.IsSeparable K E := hSH.2.1
  have : Algebra.IsSeparable (ResidueField O) (ResidueField P) := by
    have h : (inferInstance : Algebra (ResidueField O) (ResidueField P)) =
        (resMap hP).toAlgebra := by
      apply Algebra.algebra_ext
      intro x
      obtain ⟨a, rfl⟩ := residue_surjective x
      rw [ResidueField.algebraMap_residue]
      exact (resMap_residue hP a).symm
    have hsep : @Algebra.IsSeparable _ _ _ _ (resMap hP).toAlgebra := hSH.2.2.2
    rwa [← h] at hsep
  have hunr : ∀ π : O, Irreducible π → Irreducible (algebraMap O P π) := hSH.2.2.1
  have hA : FinitePresentation A.X.hom := by
    have : Smooth A.X.hom := A.smooth
    have : IsProper A.X.hom := A.proper
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨e⟩ := e
  obtain ⟨s, M, hM, ⟨eM⟩, ⟨eStrict⟩⟩ := exists_neron_model_etale_stage_with_strict_model
    (K := K) P hunr (isPullback_spec hP hunr) N hN A.X hA e
  let R := Dn O K P s
  let F := StageFraction (O := O) (K := K) P s
  let _ : Field F := stageFractionField (O := O) (K := K) P s
  let _ : Algebra R F := stageFractionAlgebra (O := O) (K := K) P s
  have : IsFractionRing R F := stageIsFractionRing (O := O) (K := K) P s
  have : IsDomain R := isDomain_Dn (O := O) (K := K) P s
  have : IsDiscreteValuationRing R := isDVR_Dn (O := O) (K := K) P hunr s
  have : Algebra.Etale O R := etale_Dn (O := O) (K := K) P hunr s
  have hff : Module.FaithfullyFlat O R := faithfullyFlat_Dn (O := O) (K := K) P hunr s
  let _ : Algebra R P := (ψ O K P s).toAlgebra
  have hffStrict : Module.FaithfullyFlat R P := faithfullyFlat_ψ (O := O) (K := K) P hunr s
  let p := baseMap O R
  let q := baseMap R P
  let t := Spec.map (CommRingCat.ofHom (stageBaseMap (O := O) (K := K) P s))
  have hpb : IsPullback (genMap R F) t p (genMap O K) :=
    isPullback_stage_base (O := O) (K := K) P hunr s
  have : Smooth p := by
    change Smooth (Spec.map _)
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    exact RingHom.smooth_algebraMap.mpr inferInstance
  let fOR := CommRingCat.ofHom (R := O) (S := R) (algebraMap O R)
  have : Surjective p := by
    change Surjective (Spec.map fOR)
    exact ((flat_and_surjective_SpecMap_iff fOR).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr hff)).2
  have : QuasiCompact p := show QuasiCompact (Spec.map _) from inferInstance
  let fRP := CommRingCat.ofHom (R := R) (S := P) (algebraMap R P)
  have : Flat q := by
    change Flat (Spec.map fRP)
    exact ((flat_and_surjective_SpecMap_iff fRP).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr hffStrict)).1
  have : IsAffineHom q := show IsAffineHom (Spec.map _) from inferInstance
  let _ : GrpObj A.X := A.grp
  refine neron_model_of_compatible_effectivity p t hpb M hM A.X eM ?_
  intro _ _ _ _ d _
  obtain ⟨U, hInv, hU, hDense⟩ :=
    neronDescentDatum_exists_invariant_affine_open p t hpb M A.X eM hM.2.2.2.2
  let _ : Algebra K F := (stageBaseMap (O := O) (K := K) P s).toAlgebra
  have : IsIntegral (Limits.pullback M.hom (genMap R F)) :=
    isIntegral_scheme_of_abelian_iso _ (A.baseChange F) eM
  have : IsIntegral M.left := isIntegral_of_integral_generic_fibre M.hom (K := F)
  have : IsLocallyNoetherian M.left := LocallyOfFiniteType.isLocallyNoetherian M.hom
  have : CompactSpace M.left := QuasiCompact.compactSpace_of_compactSpace M.hom
  have : IsNoetherian M.left := {}
  have : M.left.IsSeparated := ⟨by rw [← terminal.comp_from M.hom]; infer_instance⟩
  have hne : (U : Set M.left).Nonempty := by
    refine ⟨genericPoint M.left, hDense _ (fun y hy _ => ?_)⟩
    exact (hy.antisymm ((genericPoint_spec M.left).specializes (Set.mem_univ y))).eq
  obtain ⟨D, hD, hDU, hDescend⟩ := d.exists_invariant_effectiveCartier_of_affine_open hInv hU hne
  let G := (Over.pullback q).obj M
  let _ : GrpObj G := Functor.grpObjObj
  let a : G.left ⟶ M.left := pullback.fst M.hom q
  have hBase : IsPullback a G.hom M.hom q := IsPullback.of_hasPullback _ _
  have hG : CToPrinted.IsNeronModelOver P E G :=
    NeronExt.isNeronModelOver_of_iso eStrict hN
  have : Smooth G.hom := hG.1
  have : QuasiCompact G.hom := hG.2.2.2.1
  have : IsSeparated G.hom := hG.2.1
  have : G.left.IsSeparated := ⟨by rw [← terminal.comp_from G.hom]; infer_instance⟩
  let eG : (Over.pullback (genMap P E)).obj G ≅ (A.baseChange E).X :=
    (Over.pullback (genMap P E)).mapIso eStrict ≪≫ e
  have : IsIntegral (Limits.pullback G.hom (genMap P E)) :=
    isIntegral_scheme_of_abelian_iso _ (A.baseChange E) eG
  have hConnected : ConnectedSpace ↥(Limits.pullback G.hom (genMap P E)) := inferInstance
  have hDaff : IsAffineOpen D.support.compl := hDU.symm ▸ hU
  have hDdense : ∀ x : M.left, (∀ y, y ⤳ x → M.hom y = M.hom x → y = x) →
      x ∈ D.support.compl := by simpa only [hDU] using hDense
  obtain ⟨hD', hAff', hDense'⟩ :=
    effectiveCartier_comap_of_fibre_dense_affine hBase D hD hDaff hDdense
  have hCover := exists_affine_nonvanishing_cover_of_relative_square (K := E)
    G hConnected (D.comap a) hD' hAff' hDense'
    (square P E G hG (A.baseChange E) eG (D.comap a) hD')
  exact TensorDescent.isEffective_of_invariant_cartierSquare_of_pullback
    O R P M d D hD hDescend.symm hBase
    (affine_nonvanishing_cover_pullback_squared_dual_of_comap a D hD hD' hCover)

/-- The project's Dedekind Néron existence statement follows from the
relative theorem of the square on strict models. -/
theorem neronSchemeExtensionDedekind_of_relativeSquare
    (square : RelativeSquareStrictNeron) : NeronSchemeExtensionDedekind :=
  neronSchemeExtensionDedekind_of_strictHenselizationDescent
    (strictHenselizationDescent_of_relativeSquare square)

end NeronDVR

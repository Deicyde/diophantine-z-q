import ZInQKernel.Contrib.OneProof.SZThm33.DominantGeometricComparison
import ZInQKernel.Contrib.OneProof.SZThm33.SameDimGroupComparison
import ZInQKernel.Contrib.OneProof.SZThm33.OpenComparisonSemistable
import ZInQKernel.Contrib.OneProof.FaltingsDVR.FaltingsDVRReduction
import ZInQKernel.Contrib.OneProof.NeronDVR.RelativeSquare

/-! The level-two condition descends geometric semistability along a finite
extension admitting a semistable Néron model. -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open TopologicalSpace Topology
open ReductSplit ReductGlue SmoothGroup ZInQ.HeightSplit ZInQ.FaltingsRestate DictModels.RaynaudOr

set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 140000
set_option linter.style.haveILetI false

namespace SZRaynaud

set_option backward.isDefEq.respectTransparency false in
/-- Local quasi-finiteness on the prescribed geometric closed fibre reflects
to the ordinary closed fibre. -/
theorem locallyQuasiFinite_closedFibre_of_geomSpecialFibre
    {K : Type} [Field K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
    {A : PkgI3.AbVar K} (G N : GroupModelO A O) (i : G.G ⟶ N.G) [IsMonHom i]
    (h : LocallyQuasiFinite (geomSpecialModelMap G N i).left) :
    LocallyQuasiFinite ((Over.pullback (closedFibreMap O)).map i).left := by
  let k := IsLocalRing.ResidueField O
  let d := closedFibreMap O
  let s := sφ (φbar k)
  let F₀ := Over.pullback d
  let F₁ := Over.pullback s
  let t := Spec.map (CommRingCat.ofHom (algebraMap O (ResBarO O)))
  let F := Over.pullback t
  have he : s ≫ d = t := by
    change sφ (φbar k) ≫ closedFibreMap O = t
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let eG : F₁.obj (F₀.obj G.G) ≅ F.obj G.G := isoX (pbCompIso s d (t) he (Grp.mk G.G))
  let eN : F₁.obj (F₀.obj N.G) ≅ F.obj N.G := isoX (pbCompIso s d (t) he (Grp.mk N.G))
  have hnat : F₁.map (F₀.map i) ≫ eN.hom = eG.hom ≫ F.map i :=
    pbCompIso_natural' s d (t) he i
  have h' : F₁.map (F₀.map i) = eG.hom ≫ F.map i ≫ eN.inv := by
    apply (cancel_mono eN.hom).mp
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, hnat]
  have h'' : (F₁.map (F₀.map i)).left = eG.hom.left ≫ (F.map i).left ≫ eN.inv.left := by
    simpa only [Over.comp_left] using congrArg CommaMorphism.left h'
  haveI : LocallyQuasiFinite (F.map i).left := h
  apply locallyQuasiFinite_closedFibre_of_fieldExtension G N i (ResBarO O)
  change LocallyQuasiFinite (F₁.map (F₀.map i)).left
  rw [h'']
  infer_instance

namespace Ambient

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
  (E : IntermediateField K Ω) [FiniteDimensional K E]
  [IsAlgClosure K Ω] [IsAlgClosure E Ω] [IsAlgClosed Ω]
  {O : ValuationSubring K} {P : ValuationSubring E} {w : ValuationSubring Ω}
  [IsDiscreteValuationRing O] [IsDiscreteValuationRing P]
  (hw : w.comap (algebraMap K Ω) = O) (hp : w.comap (algebraMap E Ω) = P)
  (hP : P.comap (algebraMap K E) = O)
  (A : PkgI3.AbVar K) (M : GroupModelO A O) (hM : M.IsNeronModel)
  (N : GroupModelO (A.baseChange E) P) (hN : N.IsNeronModel)
  (ℓ : ℕ) [Fact ℓ.Prime] (hu : IsUnit (ℓ : O))

set_option backward.isDefEq.respectTransparency false in
include hw hp hP hM hN hu in
/-- If inertia acts with level-two unipotence and the extended Néron
model is geometrically semistable, the original model is geometrically
semistable. -/
theorem isSemistable_of_finiteExtension_of_levelTwo
    (hNss : N.IsSemistable)
    (hTwo : ∀ σ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w σ → ∀ t : VΩ A Ω ℓ,
      galVΩ A ℓ σ (galVΩ A ℓ σ t - t) = galVΩ A ℓ σ t - t) :
    M.IsSemistable := by
  obtain ⟨H, a, U, hU, b, f, ha, haM, haGen, hIntH, hIntU, hb, hbM, hfM, hfEq, hd, hfD⟩ :=
    dominant_identity_comparison_of_levelTwo E hw hp hP A M hM N hN ℓ hu hNss hTwo
  letI : GrpObj U := hU
  haveI : IsMonHom a := haM
  haveI : IsOpenImmersion a.left := ha
  haveI : IsMonHom b := hbM
  haveI : IsOpenImmersion b.left := hb
  haveI : IsMonHom f := hfM
  haveI : IsDominant f.left := hfD
  haveI : IsIntegral (geomSpecialFibre H).left := hIntH
  haveI : IsIntegral U.left := hIntU
  haveI : LocallyOfFiniteType (geomSpecialFibre H).hom :=
    show LocallyOfFiniteType (pullback.snd H.G.hom (Spec.map (CommRingCat.ofHom (algebraMap P (ResBarO P))))) by infer_instance
  haveI : LocallyOfFiniteType (geomSpecialFibre N).hom :=
    show LocallyOfFiniteType (pullback.snd N.G.hom (Spec.map (CommRingCat.ofHom (algebraMap P (ResBarO P))))) by infer_instance
  haveI : LocallyOfFiniteType U.hom := by rw [← Over.w b]; infer_instance
  haveI : QuasiCompact (geomSpecialFibre H).hom :=
    show QuasiCompact (pullback.snd H.G.hom (Spec.map (CommRingCat.ofHom (algebraMap P (ResBarO P))))) by infer_instance
  haveI : IsLocallyNoetherian (geomSpecialFibre H).left :=
    LocallyOfFiniteType.isLocallyNoetherian (geomSpecialFibre H).hom
  haveI : CompactSpace (geomSpecialFibre H).left :=
    QuasiCompact.compactSpace_of_compactSpace (geomSpecialFibre H).hom
  haveI : IsNoetherian (geomSpecialFibre H).left := {}
  haveI : QuasiCompact f.left := inferInstance
  let g := a ≫ (neronModelComparison (bcDVR hP M) N hN)
  haveI : IsMonHom (neronModelComparison (bcDVR hP M) N hN) := neronModelComparison_hom (bcDVR hP M) N hN
  haveI : IsMonHom g := inferInstanceAs (IsMonHom (a ≫ (neronModelComparison (bcDVR hP M) N hN)))
  haveI : LocallyQuasiFinite f.left := locallyQuasiFinite_of_dominant_sameDim f hd
  have hs : LocallyQuasiFinite (geomSpecialModelMap H N g).left := by
    rw [← hfEq]
    change LocallyQuasiFinite (f.left ≫ b.left)
    infer_instance
  haveI : LocallyQuasiFinite ((Over.pullback (closedFibreMap P)).map g).left :=
    locallyQuasiFinite_closedFibre_of_geomSpecialFibre H N g hs
  let F := Over.pullback (jO P)
  haveI : IsIso (F.map a) := haGen
  haveI : IsIso (F.map (neronModelComparison (bcDVR hP M) N hN)) := neronModelComparison_generic_isIso (bcDVR hP M) N hN
  haveI : IsIso (F.map g) := by change IsIso (F.map (a ≫ (neronModelComparison (bcDVR hP M) N hN))); rw [F.map_comp]; infer_instance
  haveI : LocallyQuasiFinite g.left := locallyQuasiFinite_of_comparison_closedFibre H N g
  haveI : IsOpenImmersion g.left := isOpenImmersion_of_comparison H N g
  let v := geomSpecialModelMap H N g
  haveI : IsOpenImmersion v.left := ZInQ.H5Glue.isOpenImmersion_pullback_map (Spec.map (CommRingCat.ofHom (algebraMap P (ResBarO P)))) g
  obtain ⟨V, hV, u, huOpen, huM, hConn, rest⟩ :=
    hasSemiAbelianIdentityComponent_of_openSubgroup v hNss
  letI : GrpObj V := hV
  haveI : IsOpenImmersion u.left := huOpen
  haveI : IsMonHom u := huM
  let q := geomSpecialModelMap H (bcDVR hP M) a
  haveI : IsOpenImmersion q.left := ZInQ.H5Glue.isOpenImmersion_pullback_map (Spec.map (CommRingCat.ofHom (algebraMap P (ResBarO P)))) a
  apply (isSemistable_bcDVR_iff hP (GapPersists.isAlgebraic_resMap hP) M).mpr
  exact ⟨V, hV, u ≫ q, inferInstanceAs (IsOpenImmersion (u.left ≫ q.left)), inferInstance,
    hConn, rest⟩

end Ambient

set_option backward.isDefEq.respectTransparency false in
/-- The reverse implication in Silverberg–Zarhin 3.3 follows from reflection
of geometric semistability to a semiabelian presentation over the residue field. -/
theorem silverbergZarhinThm33_reverse_of_geometric_descent
    (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) (A : PkgI3.AbVar K)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : O))
    (hdesc : ∀ M : GroupModelO A O, M.IsSemistable → IsSemistableResT M)
    (hpot : HasSemistableReductionSZ A O ∨
      ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧ Algebra.IsSeparable K E ∧
        IsDiscreteValuationRing (w.comap (algebraMap E Ω)) ∧
        HasSemistableReductionSZ (A.baseChange E) (w.comap (algebraMap E Ω)))
    (hI : ∀ σ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w σ → ∀ τ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w τ →
      ∀ x : VΩ A Ω ℓ, galVΩ A ℓ τ (galVΩ A ℓ σ x - x) = galVΩ A ℓ σ x - x) :
    HasSemistableReductionSZ A O := by
  rcases hpot with h | ⟨E, hE, -, hPE, N, hN, hNss⟩
  · exact h
  haveI : FiniteDimensional K E := hE
  let P := w.comap (algebraMap E Ω)
  haveI : IsDiscreteValuationRing P := hPE
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  haveI : IsAlgClosure E Ω := ⟨inferInstance, Algebra.IsAlgebraic.extendScalars (algebraMap K E).injective⟩
  have hP : P.comap (algebraMap K E) = O := by
    change (w.comap (algebraMap E Ω)).comap (algebraMap K E) = O
    rw [ValuationSubring.comap_comap, ← IsScalarTower.algebraMap_eq]
    exact hw
  obtain ⟨M, hM⟩ := exists_neron_groupModel
    (neronSchemeModelExistsDVR_of_dedekind NeronDVR.neronSchemeExtensionDedekind_proof) O A
  have hMs := Ambient.isSemistable_of_finiteExtension_of_levelTwo E hw (P := P) rfl hP
    A M hM N hN ℓ hℓ (isSemistable_of_sz N hNss) (fun σ hσ => hI σ hσ σ hσ)
  exact ⟨M, hM, hdesc M hMs⟩

#print axioms locallyQuasiFinite_closedFibre_of_geomSpecialFibre
#print axioms Ambient.isSemistable_of_finiteExtension_of_levelTwo
#print axioms silverbergZarhinThm33_reverse_of_geometric_descent

end SZRaynaud

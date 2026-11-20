import ZInQKernel.Contrib.OneProof.MumfordGroupLawNeron
import ZInQKernel.Contrib.OneProof.NeronDVR.EtaleNeighborhoods
import ZInQKernel.Contrib.OneProof.NeronDVR.MappingDescent
import ZInQKernel.Contrib.OneProof.NeronDVR.SpreadModel

/-!
# Spreading a Néron model to an étale DVR

A smooth separated quasi-compact model and a specified generic-fibre
isomorphism spread to a common étale stage. Faithfully flat descent of the
mapping property makes this stage model a Néron model.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open ZInQ.Contrib.GroupLawNeron (genMap)

namespace NeronDVR

universe u

open NeronSH

private theorem specMap_range {O R P : Type} [CommRing O] [CommRing R] [CommRing P]
    [Algebra O R] [Algebra O P] (a : R →ₐ[O] P) (ha : Function.Injective a) :
    Spec.map (CommRingCat.ofHom a.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (AlgEquiv.ofInjective a ha).symm.toRingHom) =
        Spec.map (CommRingCat.ofHom a.range.val.toRingHom) := by
  let e := AlgEquiv.ofInjective a ha
  have h : a.toRingHom.comp e.symm.toRingHom = a.range.val.toRingHom :=
    RingHom.ext (fun x => congrArg Subtype.val (e.apply_symm_apply x))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

private theorem specMap_algebraMap {O R B : Type} [CommRing O] [CommRing R] [CommRing B]
    [Algebra O R] [Algebra O B] (e : B ≃ₐ[O] R) :
    Spec.map (CommRingCat.ofHom e.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap O B)) =
      Spec.map (CommRingCat.ofHom (algebraMap O R)) := by
  have h : e.toRingHom.comp (algebraMap O B) = algebraMap O R := RingHom.ext e.commutes
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

private theorem model_of_stage_comparison
    {O P R K E F : Type} [CommRing O] [CommRing P] [CommRing R] [IsDomain R]
    [Algebra O P] [Algebra O R]
    [Field K] [Field E] [Field F] [Algebra O K] [Algebra P E] [Algebra R F] [IsFractionRing R F]
    (a : R →ₐ[O] P) (ha : Function.Injective a) (hff : a.toRingHom.FaithfullyFlat)
    (t : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of K))
    (t' : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of F))
    (hbase : IsPullback (genMap R F) t (Spec.map (CommRingCat.ofHom (algebraMap O R))) (genMap O K))
    (hpb : IsPullback (genMap P E) t' (Spec.map (CommRingCat.ofHom a.toRingHom)) (genMap R F))
    (N : Over (Spec (CommRingCat.of P))) (hN : CToPrinted.IsNeronModelOver P E N)
    (A : Over (Spec (CommRingCat.of K))) (X : Over (Spec (CommRingCat.of a.range)))
    (eN : (Over.pullback (Spec.map (CommRingCat.ofHom a.range.val.toRingHom))).obj X ≅ N)
    (eA : let q := Spec.map (CommRingCat.ofHom (algebraMap O a.range))
      (Over.pullback (pullback.fst q (genMap O K))).obj X ≅
        (Over.pullback (pullback.snd q (genMap O K))).obj A) :
    ∃ M : Over (Spec (CommRingCat.of R)), CToPrinted.IsNeronModelOver R F M ∧
      Nonempty ((Over.pullback (genMap R F)).obj M ≅ (Over.pullback t).obj A) ∧
      Nonempty ((Over.pullback (Spec.map (CommRingCat.ofHom a.toRingHom))).obj M ≅ N) := by
  let ι := AlgEquiv.ofInjective a ha
  let k := Spec.map (CommRingCat.ofHom ι.symm.toRingHom)
  let p := Spec.map (CommRingCat.ofHom a.toRingHom)
  let π := Spec.map (CommRingCat.ofHom a.range.val.toRingHom)
  let q := Spec.map (CommRingCat.ofHom (algebraMap O a.range))
  have hp : p ≫ k = π := specMap_range a ha
  have hk : k ≫ q = Spec.map (CommRingCat.ofHom (algebraMap O R)) := specMap_algebraMap ι.symm
  obtain ⟨hf, hs⟩ := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom a.toRingHom)).mpr hff
  have : Flat p := hf
  have : Surjective p := hs
  have : QuasiCompact p := show QuasiCompact (Spec.map _) from inferInstance
  let M := (Over.pullback k).obj X
  have eM : (Over.pullback p).obj M ≅ N :=
    (Over.pullbackComp p k).symm.app X ≪≫ NeronExt.pbCongr hp X ≪≫ eN
  have hM : CToPrinted.IsNeronModelOver R F M :=
    isNeronModelOver_of_fpqc p t' hpb M (NeronExt.isNeronModelOver_of_iso eM hN)
  let d := genMap R F
  have hdt : (d ≫ k) ≫ q = t ≫ genMap O K :=
    (Category.assoc _ _ _).trans ((congrArg (d ≫ ·) hk).trans hbase.w)
  let u := pullback.lift (d ≫ k) t hdt
  let e₀ : (Over.pullback d).obj M ≅ (Over.pullback t).obj A :=
    (Over.pullbackComp d k).symm.app X ≪≫
      NeronExt.pbCongr (pullback.lift_fst _ _ _).symm X ≪≫
      (Over.pullbackComp u _).app X ≪≫ (Over.pullback u).mapIso eA ≪≫
      (Over.pullbackComp u _).symm.app A ≪≫ NeronExt.pbCongr (pullback.lift_snd _ _ _) A
  exact ⟨M, hM, ⟨e₀⟩, ⟨eM⟩⟩

section

variable {O K E : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Field K] [Algebra O K] [IsFractionRing O K] [Field E] [Algebra K E]
  [Algebra O E] [IsScalarTower O K E] (P : ValuationSubring E)
  [Algebra O P] [IsScalarTower O P E] [IsLocalHom (algebraMap O P)]
  [IsDiscreteValuationRing P] [Algebra.IsSeparable K E]
  [Algebra.IsSeparable (ResidueField O) (ResidueField P)]

private noncomputable abbrev stageDiagram :
    (Finset P)ᵒᵖ ⥤ Over (Spec (CommRingCat.of O)) := by
  let B := fun s : Finset P => (ψa O K P s).range
  let hB := monotone_range_ψa (O := O) (K := K) P
  exact
    { obj i := Over.mk (ej B hB i)
      map a := Over.homMk ((specDiag B hB).map a) (map_ej B hB a)
      map_id i := by ext1; exact (specDiag B hB).map_id i
      map_comp a b := by ext1; exact (specDiag B hB).map_comp a b }

private noncomputable abbrev stageCone : Cone (stageDiagram (O := O) (K := K) P) := by
  let B := fun s : Finset P => (ψa O K P s).range
  let hB := monotone_range_ψa (O := O) (K := K) P
  exact
    { pt := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap O P)))
      π := {
        app i := Over.homMk ((specCone B hB).π.app i) (π_ej B hB i)
        naturality i k a := by ext1; exact (specCone B hB).π.naturality a } }

private noncomputable def stageConeIsLimit
    (hunr : ∀ π : O, Irreducible π → Irreducible (algebraMap O P π)) :
    IsLimit (stageCone (O := O) (K := K) P) := by
  let B := fun s : Finset P => (ψa O K P s).range
  let hB := monotone_range_ψa (O := O) (K := K) P
  have : CategoryTheory.IsConnected (Finset P)ᵒᵖ := IsCofiltered.isConnected _
  apply isLimitOfReflects (Over.forget _)
  refine (IsLimit.equivOfNatIsoOfIso (NatIso.ofComponents (fun _ => Iso.refl _) ?_) _ _
    (Cone.ext (Iso.refl _) ?_)) (specConeIsLimit B hB (fun x => ?_))
  · intro i k a
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · intro i
    simp only [Iso.refl_hom, Category.id_comp]
  · exact ⟨{x}, subset_range_ψa P hunr {x} (Finset.mem_singleton_self x)⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 450000 in
/-- The strict model and the prescribed generic isomorphism can both be
realized over the same étale DVR stage. -/
theorem exists_neron_model_etale_stage_with_strict_model
    (hunr : ∀ π : O, Irreducible π → Irreducible (algebraMap O P π))
    (hpb : IsPullback (genMap P E)
      (Spec.map (CommRingCat.ofHom (algebraMap K E)))
      (Spec.map (CommRingCat.ofHom (algebraMap O P))) (genMap O K))
    (N : Over (Spec (CommRingCat.of P))) (hN : CToPrinted.IsNeronModelOver P E N)
    (A : Over (Spec (CommRingCat.of K))) (hA : FinitePresentation A.hom)
    (e : (Over.pullback (genMap P E)).obj N ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K E)))).obj A) :
    ∃ s : Finset P,
      let _ := stageFractionField (O := O) (K := K) P s
      let _ := stageFractionAlgebra (O := O) (K := K) P s
      ∃ M : Over (Spec (CommRingCat.of (Dn O K P s))),
        CToPrinted.IsNeronModelOver (Dn O K P s) (StageFraction (O := O) (K := K) P s) M ∧
        Nonempty ((Over.pullback (genMap (Dn O K P s) (StageFraction (O := O) (K := K) P s))).obj M ≅
          (Over.pullback (Spec.map (CommRingCat.ofHom (stageBaseMap (O := O) (K := K) P s)))).obj A) ∧
        Nonempty ((Over.pullback (Spec.map (CommRingCat.ofHom (ψa O K P s).toRingHom))).obj M ≅ N) := by
  let D := stageDiagram (O := O) (K := K) P
  let c := stageCone (O := O) (K := K) P
  have hc : IsLimit c := stageConeIsLimit P hunr
  have {i k} (a : i ⟶ k) : IsAffineHom (D.map a).left := show IsAffineHom (Spec.map _) from inferInstance
  have (i : (Finset P)ᵒᵖ) : IsAffineHom (D.obj i).hom :=
    show IsAffineHom (Spec.map _) from inferInstance
  have (i : (Finset P)ᵒᵖ) : CompactSpace (D.obj i).left :=
    show CompactSpace (Spec _) from inferInstance
  have (i : (Finset P)ᵒᵖ) : QuasiSeparatedSpace (D.obj i).left :=
    show QuasiSeparatedSpace (Spec _) from inferInstance
  let V : Over c.pt.left := N
  have hVsm : Smooth V.hom := hN.1
  have hVsep : IsSeparated V.hom := hN.2.1
  have hVqc : QuasiCompact V.hom := hN.2.2.2.1
  let j := genMap O K
  obtain ⟨i, X, ⟨eN⟩, ⟨eA⟩⟩ :=
    exists_spread_model_over j D c hc (genMap P E) _ hpb V A hA e
  let s := i.unop
  let R := Dn O K P s
  let F := StageFraction (O := O) (K := K) P s
  let _ : Field F := stageFractionField (O := O) (K := K) P s
  let _ : Algebra R F := stageFractionAlgebra (O := O) (K := K) P s
  have : IsFractionRing R F := stageIsFractionRing (O := O) (K := K) P s
  have : IsDomain R := isDomain_Dn (O := O) (K := K) P s
  let a := ψa O K P s
  have ha : Function.Injective a := injective_ψ (O := O) (K := K) P s
  have hff : RingHom.FaithfullyFlat (R := R) (S := P) a.toRingHom :=
    faithfullyFlat_ψ (O := O) (K := K) P hunr s
  let d := genMap R F
  let t : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (R := K) (S := F) (stageBaseMap (O := O) (K := K) P s))
  let t' : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of F) :=
    Spec.map (CommRingCat.ofHom (R := F) (S := E) (stageStrictMap (O := O) (K := K) P s))
  have hb : IsPullback d t (Spec.map (CommRingCat.ofHom (R := O) (S := R) (algebraMap O R))) j :=
    isPullback_stage_base (O := O) (K := K) P hunr s
  have hs : IsPullback (genMap P E) t' (Spec.map (CommRingCat.ofHom (R := R) (S := P) a.toRingHom)) d :=
    isPullback_stage_strict (O := O) (K := K) P hunr s
  let B := a.range
  let π := Spec.map (CommRingCat.ofHom (R := B) (S := P) B.val.toRingHom)
  let q := Spec.map (CommRingCat.ofHom (R := O) (S := B) (algebraMap O B))
  let XB : Over (Spec (CommRingCat.of B)) := X
  have eNB : (Over.pullback π).obj XB ≅ N := eN
  have eAB : (Over.pullback (pullback.fst q j)).obj XB ≅
      (Over.pullback (pullback.snd q j)).obj A := eA
  have transfer := @model_of_stage_comparison O P R K E F
    inferInstance inferInstance inferInstance ‹IsDomain R› inferInstance inferInstance
    inferInstance inferInstance ‹Field F› inferInstance inferInstance ‹Algebra R F› ‹IsFractionRing R F›
  have transferBase := transfer a ha hff t t' hb hs
  have transferModel := transferBase N hN A XB eNB eAB
  obtain ⟨M, hM, eM, eStrict⟩ := transferModel
  exact ⟨s, M, hM, eM, eStrict⟩

/-- A Néron model and its prescribed generic isomorphism spread together
to an étale DVR stage. -/
theorem exists_neron_model_etale_stage
    (hunr : ∀ π : O, Irreducible π → Irreducible (algebraMap O P π))
    (hpb : IsPullback (genMap P E)
      (Spec.map (CommRingCat.ofHom (algebraMap K E)))
      (Spec.map (CommRingCat.ofHom (algebraMap O P))) (genMap O K))
    (N : Over (Spec (CommRingCat.of P))) (hN : CToPrinted.IsNeronModelOver P E N)
    (A : Over (Spec (CommRingCat.of K))) (hA : FinitePresentation A.hom)
    (e : (Over.pullback (genMap P E)).obj N ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K E)))).obj A) :
    ∃ s : Finset P,
      let _ := stageFractionField (O := O) (K := K) P s
      let _ := stageFractionAlgebra (O := O) (K := K) P s
      ∃ M : Over (Spec (CommRingCat.of (Dn O K P s))),
        CToPrinted.IsNeronModelOver (Dn O K P s) (StageFraction (O := O) (K := K) P s) M ∧
        Nonempty ((Over.pullback (genMap (Dn O K P s) (StageFraction (O := O) (K := K) P s))).obj M ≅
          (Over.pullback (Spec.map (CommRingCat.ofHom (stageBaseMap (O := O) (K := K) P s)))).obj A) := by
  obtain ⟨s, M, hM, eM, _⟩ :=
    exists_neron_model_etale_stage_with_strict_model P hunr hpb N hN A hA e
  exact ⟨s, M, hM, eM⟩

end

/-- A specified transport from the base-changed model identifies the target
with the same Cartesian pullback via its projection to the original model. -/
theorem isPullback_of_pullback_iso {S S' : Scheme.{u}} (p : S' ⟶ S)
    (M : Over S) (N : Over S') (e : (Over.pullback p).obj M ≅ N) :
    IsPullback (e.inv.left ≫ pullback.fst M.hom p) N.hom M.hom p := by
  have hw : e.inv.left ≫ pullback.snd M.hom p = N.hom := Over.w e.inv
  refine IsPullback.of_iso_pullback ⟨?_⟩ ((Over.forget S').mapIso e.symm) rfl hw
  rw [Category.assoc, pullback.condition, ← Category.assoc, hw]

end NeronDVR

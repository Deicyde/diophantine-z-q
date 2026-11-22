import ZInQKernel.Contrib.OneProof.DirectWeil.RelativeModelSquare
import ZInQKernel.Contrib.OneProof.NeronDVR.IdentitySubgroup
import ZInQKernel.Contrib.OneProof.NeronDVR.InvariantCartier
import ZInQKernel.Contrib.CloudR2Poincare.L2.VeryAmpleBaseChange
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveSpace.Embedding

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace
open Scheme.Modules ProjectiveSpace
open scoped AlgebraicGeometry.Scheme.Modules CategoryTheory.MonObj

namespace SZRaynaud.Relative

open NeronDVR
open ZInQ.Contrib.CloudR2Poincare.L2 (VeryAmple)

private theorem eq_fibreGeneric {X Y : Scheme} (f : X ⟶ Y) [GeometricallyIntegral f]
    (x : X) (hx : ∀ z, z ⤳ x → f z = f x → z = x) :
    f.fiberι (f x) (genericPoint (f.fiber (f x))) = x := by
  let v := f.fiberι (f x)
  have h : x ∈ Set.range v := by
    change x ∈ Set.range (f.fiberι (f x))
    rw [f.range_fiberι]
    rfl
  obtain ⟨y, hy⟩ := h
  have hs : genericPoint (f.fiber (f x)) ⤳ y := (genericPoint_spec _).specializes trivial
  have hss : v (genericPoint (f.fiber (f x))) ⤳ x := by
    simpa only [hy] using hs.map v.continuous
  have hr : f.fiberι (f x) (genericPoint (f.fiber (f x))) ∈ Set.range (f.fiberι (f x)) := ⟨_, rfl⟩
  rw [f.range_fiberι] at hr
  exact hx _ hss hr

variable {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

private theorem eq_genericPoint_or_closedPoint (y : Spec (.of R)) :
    y = genericPoint (Spec (.of R)) ∨ y = IsLocalRing.closedPoint R := by
  by_cases h : y.asIdeal = ⊥
  · exact Or.inl (by rw [genericPoint_eq_bot_of_affine]; exact PrimeSpectrum.ext h)
  · exact Or.inr (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal
      (Ring.DimensionLEOne.maximalOfPrime h y.isPrime)))

/-- An affine neighbourhood of the closed fibre generic point contains all
fibre generic points of a smooth geometrically integral DVR scheme. -/
theorem exists_affineOpen_containing_fibreGenerics {X : Scheme} (f : X ⟶ Spec (.of R))
    [Smooth f] [GeometricallyIntegral f] :
    ∃ (U : X.Opens), IsAffineOpen U ∧ (U : Set X).Nonempty ∧
      ∀ x : X, (∀ z, z ⤳ x → f z = f x → z = x) → x ∈ U := by
  let s : Spec (.of R) := IsLocalRing.closedPoint R
  let p : X := f.fiberι s (genericPoint (f.fiber s))
  obtain ⟨U, hU, hp, -⟩ := exists_isAffineOpen_mem_and_subset (x := p) (U := ⊤) trivial
  have : IsIntegral X := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian f
  refine ⟨U, hU, ⟨p, hp⟩, fun x hx => ?_⟩
  rcases eq_genericPoint_or_closedPoint (f x) with he | he
  · have hη : f (genericPoint X) = genericPoint (Spec (.of R)) := by
      have hs := ((genericPoint_spec X).specializes (Set.mem_univ x)).map f.continuous
      rw [he] at hs
      rw [genericPoint_eq_bot_of_affine] at hs ⊢
      have hle := (PrimeSpectrum.le_iff_specializes
        (f (genericPoint X) : PrimeSpectrum R) (⊥ : PrimeSpectrum R)).mpr hs
      exact @le_antisymm (PrimeSpectrum R) _ _ _ hle bot_le
    rw [← hx _ ((genericPoint_spec X).specializes (Set.mem_univ x)) (hη.trans he.symm)]
    exact ((genericPoint_spec X).specializes (Set.mem_univ p)).mem_open U.isOpen hp
  · have hex := eq_fibreGeneric f x hx
    rw [show f x = s from he] at hex
    exact hex ▸ hp

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 500000 in
/-- A smooth group with geometrically integral fibres and abelian generic
fibre has a projective immersion over a strictly henselian DVR. -/
theorem exists_projectiveImmersion [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]
    (G : Over (Spec (.of R))) [GrpObj G] [Smooth G.hom] [GeometricallyIntegral G.hom]
    [QuasiCompact G.hom] [IsSeparated G.hom] [IsProper (Generic (K := K) G).hom] :
    ∃ (coords : Type) (_ : Finite coords) (e : G.left ⟶ ℙ(coords; Spec (.of R))),
      IsImmersion e ∧ e ≫ ℙ(coords; Spec (.of R)) ↘ Spec (.of R) = G.hom := by
  obtain ⟨U, hU, hne, hDense⟩ := exists_affineOpen_containing_fibreGenerics G.hom
  have : IsIntegral G.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian G.hom
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have : IsNoetherian G.left := {}
  have : G.left.IsSeparated := ⟨by rw [← terminal.comp_from G.hom]; infer_instance⟩
  let Z : Closeds G.left := ⟨(U : Set G.left)ᶜ, U.isOpen.isClosed_compl⟩
  let D := Scheme.IdealSheafData.vanishingIdeal Z
  have : AlgebraicGeometry.IsRegular G.left :=
    ⟨ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Smooth.isRegularLocalRing_stalk_of_isDiscreteValuationRing
      R G.hom⟩
  have hD : D.IsInvertible := G.left.isInvertible_vanishingIdeal_compl_of_isAffineOpen
    IsRegular.uniqueFactorizationMonoid_stalk hU hne
  have hDU : D.support.compl = U := by
    ext x
    change x ∉ (D.support : Set G.left) ↔ x ∈ (U : Set G.left)
    simp [D, Z, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  let : D.toModulesᵛ.IsInvertible := hD.isInvertible_dual_toModules
  have hConnected : ConnectedSpace ↥(pullback G.hom (genericMap R K)) := by
    have : GeometricallyIntegral (Generic (K := K) G).hom := by
      change GeometricallyIntegral (pullback.snd G.hom (genericMap R K))
      infer_instance
    have : IsIntegral (Generic (K := K) G).left :=
      GeometricallyIntegral.isIntegral_of_subsingleton (Generic (K := K) G).hom
    change ConnectedSpace ↥(Generic (K := K) G).left
    infer_instance
  have hCover := exists_affine_nonvanishing_cover_of_relative_square (K := K) G hConnected
    D hD (hDU.symm ▸ hU) (fun x hx => hDU.symm ▸ hDense x hx)
    (fun a _ => square_of_geometricallyIntegral (K := K) G (Scheme.Pic.mk _) a)
  choose s hxs hs using hCover
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover
    (fun x => ((Hom.zeroLocus (s x)).support.compl : Set G.left))
    (fun x => (Hom.zeroLocus (s x)).support.compl.isOpen)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hxs x⟩)
  exact exists_isImmersion_projectiveSpace_of_isAffineOpen G.hom _
    (fun i : S => s i) (fun i : S => hs i) (eq_top_iff.mpr fun x _ => by
      obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hS (Set.mem_univ x))
      exact Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hxi⟩)

set_option backward.isDefEq.respectTransparency false in
/-- A projective immersion of the model supplies a line whose actual
restriction to the proper generic fibre is very ample. -/
theorem exists_genericVeryAmple_of_projectiveImmersion {X S S' : Scheme} {coords : Type} [Finite coords]
    (e : X ⟶ ℙ(coords; S)) [IsImmersion e] {f : X ⟶ S}
    (he : e ≫ ℙ(coords; S) ↘ S = f) (q : S' ⟶ S) [IsProper (pullback.snd f q)] :
    ∃ L : X.Modules, L.IsInvertible ∧
      VeryAmple (pullback.snd f q) ((Scheme.Modules.pullback (pullback.fst f q)).obj L) := by
  let p := pullback.fst f q
  let r := pullback.snd f q
  have hcompat : r ≫ q = (p ≫ e) ≫ ℙ(coords; S) ↘ S := by
    rw [Category.assoc, he, pullback.condition]
  let e' := ProjectiveSpace.liftBaseChange r (p ≫ e) hcompat
  have hpull : IsPullback p e' e (ProjectiveSpace.map coords q) := by
    apply ProjectiveSpace.isPullback_liftBaseChange
    rw [he]
    exact IsPullback.of_hasPullback _ _
  have : IsImmersion e' := MorphismProperty.of_isPullback hpull inferInstance
  have hr : e' ≫ ℙ(coords; S') ↘ S' = r := ProjectiveSpace.liftBaseChange_over _ _ _
  have : IsProper (e' ≫ ℙ(coords; S') ↘ S') := by rw [hr]; infer_instance
  have : IsProper e' := IsProper.of_comp e' (ℙ(coords; S') ↘ S')
  have hc : IsClosedImmersion e' := IsClosedImmersion.of_isPreimmersion e' e'.isClosedMap.isClosed_range
  let L := ProjectiveSpace.twistRestrict e 1
  refine ⟨L, inferInstance, coords, inferInstance, e', hc, hr, ⟨?_⟩⟩
  exact (Scheme.Modules.pullbackComp p e).app (twist coords S 1) ≪≫
    (Scheme.Modules.pullbackCongr hpull.w).app (twist coords S 1) ≪≫
    ((Scheme.Modules.pullbackComp e' (ProjectiveSpace.map coords q)).app (twist coords S 1)).symm ≪≫
    (Scheme.Modules.pullback e').mapIso (ProjectiveSpace.pullbackMapTwistIso coords q 1)

/-- A line on the actual relative group whose generic restriction polarizes
the abelian generic fibre. -/
theorem exists_modelLine_genericVeryAmple [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]
    (G : Over (Spec (.of R))) [GrpObj G] [Smooth G.hom] [GeometricallyIntegral G.hom]
    [QuasiCompact G.hom] [IsSeparated G.hom] [IsProper (Generic (K := K) G).hom] :
    ∃ L : G.left.Modules, L.IsInvertible ∧ VeryAmple (Generic (K := K) G).hom
      ((Scheme.Modules.pullback (pullback.fst G.hom (genericMap R K))).obj L) := by
  obtain ⟨coords, _, e, he, h⟩ := exists_projectiveImmersion (K := K) G
  have : IsImmersion e := he
  have : IsProper (pullback.snd G.hom (genericMap R K)) :=
    (show IsProper (Generic (K := K) G).hom from inferInstance)
  exact exists_genericVeryAmple_of_projectiveImmersion e h (genericMap R K)

end SZRaynaud.Relative

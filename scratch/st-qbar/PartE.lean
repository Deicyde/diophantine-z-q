import ZInQKernel.OneProof.H.TailO

open CategoryTheory AlgebraicGeometry Limits

set_option linter.style.haveILetI false

namespace GapST
open _root_.LeafQM _root_.LeafQM.AV

/-- A non-closed point of an irreducible proper smooth curve over a field is dense. -/
theorem closure_eq_univ_of_not_closed {K : Type} [Field K] {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    [IrreducibleSpace X] (p : X) (hp : ¬ IsClosed ({p} : Set X)) :
    closure ({p} : Set X) = Set.univ := by
  haveI : LocallyOfFiniteType f := inferInstance
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨z, hzZ, hzc⟩ := nonempty_inter_closedPoints (Z := closure {p})
    ⟨p, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
  have hz : IsClosed ({z} : Set X) := mem_closedPoints_iff.mp hzc
  have hpz : p ⤳ z := specializes_iff_mem_closure.mpr hzZ
  obtain ⟨h1, h2⟩ := InfraSmoothDim.stalk_dim_of_smoothOfRelativeDimension f 1 z hz
  haveI : IsDomain (X.presheaf.stalk z) :=
    HDec.CIcopy.CurveGlueCI.isDomain_of_dim_one (by exact_mod_cast h1) h2
  haveI : Ring.KrullDimLE 1 (X.presheaf.stalk z) := by
    rw [Ring.krullDimLE_iff]; exact h1.le
  obtain ⟨P, hP⟩ : p ∈ Set.range (X.fromSpecStalk z) := by
    rw [Scheme.range_fromSpecStalk]; exact hpz
  have hPbot : P.asIdeal = ⊥ := by
    by_contra hne
    have hmax : P.asIdeal.IsMaximal := P.2.isMaximal_of_ne_bot hne
    have : P = IsLocalRing.closedPoint _ :=
      PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hmax)
    apply hp
    rw [← hP, this, Scheme.fromSpecStalk_closedPoint]; exact hz
  have hηz : genericPoint X ⤳ z := (genericPoint_spec X).specializes (Set.mem_univ z)
  obtain ⟨Q, hQ⟩ : genericPoint X ∈ Set.range (X.fromSpecStalk z) := by
    rw [Scheme.range_fromSpecStalk]; exact hηz
  have hPQ : P ⤳ Q := (PrimeSpectrum.le_iff_specializes P Q).mp
    (by change P.asIdeal ≤ Q.asIdeal; rw [hPbot]; exact bot_le)
  have hpη : p ⤳ genericPoint X := by
    rw [← hP, ← hQ]; exact hPQ.map (X.fromSpecStalk z).continuous
  refine Set.eq_univ_of_univ_subset ?_
  rw [← (genericPoint_spec X).def]
  exact closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hpη))
    isClosed_closure

/-- **A fixed `ℂ`-point of a nontrivial endomorphism of an irreducible proper smooth curve over `ℚ`
comes from a `ℚ̄`-point.** -/
theorem exists_qbar_factor (Y : Over (Spec (CommRingCat.of ℚ))) [IsProper Y.hom]
    [SmoothOfRelativeDimension 1 Y.hom] [IrreducibleSpace Y.left]
    (y : fieldPt ℂ ⟶ Y) (h : Y ⟶ Y) (hy : y ≫ h = y) (s : fieldPt Qbar ⟶ Y) (hs : s ≫ h ≠ s) :
    ∃ (ιe : Qbar →+* ℂ) (y₀ : fieldPt Qbar ⟶ Y), fieldMap ιe.toRatAlgHom ≫ y₀ = y := by
  obtain ⟨⟨p, e⟩, hpe⟩ : ∃ q, Scheme.SpecToEquivOfField ℂ Y.left y.left = q := ⟨_, rfl⟩
  have hyl : y.left = Spec.map e ≫ Y.left.fromSpecResidueField p := by
    rw [← (Scheme.SpecToEquivOfField ℂ Y.left).symm_apply_apply y.left, hpe]; rfl
  by_cases hc : IsClosed ({p} : Set Y.left)
  · have : IsClosedImmersion (Y.left.fromSpecResidueField p) :=
      isClosed_singleton_iff_isClosedImmersion.mp hc
    haveI : LocallyOfFiniteType Y.hom := inferInstance
    have : IsFinite (Y.left.fromSpecResidueField p ≫ Y.hom) :=
      (isFinite_iff_locallyOfFiniteType_of_jacobsonSpace
        (f := Y.left.fromSpecResidueField p ≫ Y.hom)).mpr inferInstance
    let φ := Spec.preimage (Y.left.fromSpecResidueField p ≫ Y.hom)
    letI : Algebra ℚ (Y.left.residueField p) := φ.hom.toAlgebra
    have hφ : φ.hom.IsIntegral := by
      rw [← IsIntegralHom.SpecMap_iff, Spec.map_preimage]
      infer_instance
    haveI : Algebra.IsIntegral ℚ (Y.left.residueField p) := ⟨fun x => hφ x⟩
    haveI : Algebra.IsAlgebraic ℚ (Y.left.residueField p) := Algebra.IsIntegral.isAlgebraic
    let j : Y.left.residueField p →ₐ[ℚ] Qbar := IsAlgClosed.lift
    letI : Algebra (Y.left.residueField p) Qbar := j.toRingHom.toAlgebra
    letI : Algebra (Y.left.residueField p) ℂ := e.hom.toAlgebra
    haveI : IsScalarTower ℚ (Y.left.residueField p) Qbar :=
      IsScalarTower.of_algebraMap_eq (fun x => (j.commutes x).symm)
    haveI : Algebra.IsAlgebraic (Y.left.residueField p) Qbar :=
      Algebra.IsAlgebraic.tower_top (K := ℚ) _
    let ι : Qbar →ₐ[Y.left.residueField p] ℂ := IsAlgClosed.lift
    have hιj : ∀ x, ι (j x) = e.hom x := fun x => ι.commutes x
    let y₀ : fieldPt Qbar ⟶ Y :=
      Over.homMk (Spec.map (CommRingCat.ofHom j.toRingHom) ≫ Y.left.fromSpecResidueField p)
        (HDec.TSHeckeGal.specQbar_to_specQ_eq' _ _)
    refine ⟨ι.toRingHom, y₀, ?_⟩
    apply Over.OverMorphism.ext
    rw [hyl]
    change Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ Spec.map (CommRingCat.ofHom j.toRingHom) ≫
      Y.left.fromSpecResidueField p = _
    rw [← Category.assoc, ← Spec.map_comp]
    congr 2
    ext x
    exact hιj x
  · exfalso
    apply hs
    have hcl := closure_eq_univ_of_not_closed Y.hom p hc
    haveI : IsReduced Y.left := by
      haveI : Smooth Y.hom := SmoothOfRelativeDimension.smooth 1 Y.hom
      exact HDec.ModelGlue.isReduced_of_smooth_domain Y.hom
    haveI : IsDominant y.left := by
      constructor
      rw [DenseRange, dense_iff_closure_eq, ← Set.univ_subset_iff, ← hcl]
      apply closure_mono
      rw [Set.singleton_subset_iff]
      refine ⟨IsLocalRing.closedPoint ℂ, ?_⟩
      rw [hyl]; exact Y.left.fromSpecResidueField_apply p _
    have hl : h.left = 𝟙 Y.left :=
      ext_of_isDominant_of_isSeparated Y.hom (by rw [Over.w h, Category.id_comp]) y.left
        (by rw [Category.comp_id, ← Over.comp_left, hy])
    apply Over.OverMorphism.ext
    rw [Over.comp_left, hl, Category.comp_id]

end GapST

import ZInQKernel.Contrib.OneProof.ShimuraPointDictGeometry
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Birational.ValuativeExtension

/-! ON THE SPOT (c): extension from the generic point of the curve and application
of the pointed Albanese property to a morphism into the Jacobian. -/

noncomputable section

namespace BShStandard

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter
open LeafModCurves PkgI3 PkgI3.AbVar AfTateLam

set_option backward.isDefEq.respectTransparency false

theorem spec_to_rat_eq {S : CommRingCat} (f g : Spec S ⟶ SpecQ) : f = g := by
  rw [← Spec.map_preimage f, ← Spec.map_preimage g]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext_rat _ _)

variable {X : Over SpecQ} [IsIntegral X.left] {Y : Over SpecQ}

theorem exists_extension (hC : IsCurve X) [IsProper Y.hom]
    (f : Spec X.left.functionField ⟶ Y.left) :
    ∃ F : X ⟶ Y, X.left.fromSpecFunctionField ≫ F.left = f := by
  letI : X.left.Over SpecQ := ⟨X.hom⟩
  letI : Y.left.Over SpecQ := ⟨Y.hom⟩
  haveI : IsProper (Y.left ↘ SpecQ) := ‹IsProper Y.hom›
  haveI : Y.left.IsSeparated := ⟨by
    rw [show terminal.from Y.left = Y.hom ≫ terminal.from SpecQ from terminal.hom_ext _ _]
    infer_instance⟩
  letI := hC.smooth
  obtain ⟨F, hF, he⟩ := Scheme.exists_hom_of_valuationRing_stalk
    (fun x => Scheme.valuationRing_stalk X.hom x) f (spec_to_rat_eq _ _)
  exact ⟨Over.homMk F hF.1, he⟩

/-- A map to the Jacobian induces an endomorphism acting on differences of points
by differences of their images. Translation removes its value at the base point. -/
theorem exists_end_of_morphism {P₀ : RatPt X} {J : AbVar ℚ} {aj : X ⟶ J.X}
    (hJ : IsJacobian X P₀ J aj) (F : X ⟶ J.X) :
    ∃ t : AbVar.End J, ∀ x x' : CPt X,
      endC t (ajC aj x / ajC aj x') = (x ≫ F) / (x' ≫ F) := by
  let c := toUnit X ≫ P₀ ≫ F
  let f := F / c
  have hP : P₀ ≫ f = η[J.X] := by
    rw [show η[J.X] = (1 : 𝟙_ (Over SpecQ) ⟶ J.X) from by
      rw [CategoryTheory.Hom.one_def, Subsingleton.elim (toUnit _) (𝟙 _), Category.id_comp]]
    have hc : P₀ ≫ c = P₀ ≫ F := by
      have h : P₀ ≫ toUnit X = 𝟙 _ := Subsingleton.elim _ _
      simp [c, ← Category.assoc, h]
    rw [GrpObj.comp_div, hc, div_self']
  obtain ⟨φ, ⟨hφ, hfac⟩, _⟩ := hJ.univ J f hP
  letI : IsMonHom φ := hφ
  refine ⟨Hom.mk' φ, fun x x' => ?_⟩
  change (x ≫ aj / x' ≫ aj) ≫ φ = _
  rw [GrpObj.div_comp]
  simp only [Category.assoc, hfac, f, GrpObj.comp_div]
  have hc : x ≫ c = x' ≫ c := by
    have h : x ≫ toUnit X = x' ≫ toUnit X := Subsingleton.elim _ _
    simpa only [c, ← Category.assoc] using congrArg (fun t => t ≫ P₀ ≫ F) h
  rw [hc]
  exact div_div_div_cancel_right _ _ _

open ShimuraPointDict in
/-- Compare specialized points using a valuation ring in the source field. The
two target lifts have the same generic map, so separatedness identifies them. -/
theorem point_eq_of_specialization (hC : IsCurve X) (f : X ⟶ X)
    (φ : X.left.functionField →+* X.left.functionField)
    (hf : X.left.fromSpecFunctionField ≫ f.left =
      Spec.map (CommRingCat.ofHom φ) ≫ X.left.fromSpecFunctionField)
    (A : ValuationSubring X.left.functionField) (base : ℚ →+* A) (e : A →+* ℂ)
    {x z : CPt X}
    (vx : X.left.presheaf.stalk (complexMap x (IsLocalRing.closedPoint ℂ)) →+* A)
    (vz : X.left.presheaf.stalk (complexMap z (IsLocalRing.closedPoint ℂ)) →+* A)
    (hx : A.subtype.comp vx = algebraMap _ X.left.functionField)
    (hz : A.subtype.comp vz = φ.comp (algebraMap _ X.left.functionField))
    (hex : e.comp vx = (Scheme.stalkClosedPointTo (complexMap x)).hom)
    (hez : e.comp vz = (Scheme.stalkClosedPointTo (complexMap z)).hom) :
    x ≫ f = z := by
  let i := Spec.map (CommRingCat.ofHom A.subtype)
  let LX := Spec.map (CommRingCat.ofHom vx) ≫ X.left.fromSpecStalk _
  let LZ := Spec.map (CommRingCat.ofHom vz) ≫ X.left.fromSpecStalk _
  have generic (w : X.left) :
      Spec.map (CommRingCat.ofHom (algebraMap (X.left.presheaf.stalk w) X.left.functionField)) ≫
        X.left.fromSpecStalk w = X.left.fromSpecFunctionField :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes w)
  have hxg : i ≫ LX = X.left.fromSpecFunctionField := by
    dsimp only [i, LX]
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, hx, generic]
  have hzg : i ≫ LZ = Spec.map (CommRingCat.ofHom φ) ≫ X.left.fromSpecFunctionField := by
    dsimp only [i, LZ]
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, hz, CommRingCat.ofHom_comp,
      Spec.map_comp, Category.assoc, generic]
  let sq : ValuativeCommSq X.hom :=
    { R := A
      K := X.left.functionField
      i₁ := Spec.map (CommRingCat.ofHom φ) ≫ X.left.fromSpecFunctionField
      i₂ := Spec.map (CommRingCat.ofHom base)
      commSq := ⟨spec_to_rat_eq _ _⟩ }
  let lx : sq.commSq.LiftStruct :=
    ⟨LX ≫ f.left, by
      change i ≫ (LX ≫ f.left) = _
      rw [← Category.assoc, hxg, hf], spec_to_rat_eq _ _⟩
  let lz : sq.commSq.LiftStruct := ⟨LZ, hzg, spec_to_rat_eq _ _⟩
  letI := hC.proper
  letI := IsSeparated.valuativeCriterion X.hom sq
  have hl : LX ≫ f.left = LZ := congrArg CommSq.LiftStruct.l (Subsingleton.elim lx lz)
  have evx : Spec.map (CommRingCat.ofHom e) ≫ LX = complexMap x := by
    dsimp only [LX]
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, hex]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk _
  have evz : Spec.map (CommRingCat.ofHom e) ≫ LZ = complexMap z := by
    dsimp only [LZ]
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, hez]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk _
  apply Over.OverMorphism.ext
  exact calc
    (x ≫ f).left = (Spec.map (CommRingCat.ofHom e) ≫ LX) ≫ f.left := by rw [evx]; rfl
    _ = z.left := by rw [Category.assoc, hl, evz]

universe u

/-- A field-valued point fixed by a finite Galois group descends. Its stalk
evaluation takes values in the fixed field, and gives the descended map. -/
theorem exists_descend_galois {Y : Scheme.{u}} {K L : Type u} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (P : Spec (CommRingCat.of L) ⟶ Y)
    (hP : ∀ σ : L ≃ₐ[K] L, Spec.map (CommRingCat.ofHom (σ : L →+* L)) ≫ P = P) :
    ∃ Q : Spec (CommRingCat.of K) ⟶ Y,
      Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ Q = P := by
  let y := P (IsLocalRing.closedPoint (CommRingCat.of L))
  let e := Scheme.stalkClosedPointTo P
  let iy := Y.fromSpecStalk y
  have hfac : Spec.map e ≫ iy = P := Scheme.Spec_stalkClosedPointTo_fromSpecStalk P
  have hfix (r : Y.presheaf.stalk y) (σ : L ≃ₐ[K] L) : σ (e r) = e r := by
    have h : (Spec.map (CommRingCat.ofHom (σ : L →+* L)) ≫ Spec.map e) ≫ iy = Spec.map e ≫ iy := by
      rw [Category.assoc, hfac, hP σ]
    have hh := (cancel_mono iy).mp h
    rw [← Spec.map_comp] at hh
    exact congrArg (fun f : Y.presheaf.stalk y ⟶ CommRingCat.of L => f r) (Spec.map_injective hh)
  let a := algebraMap K L
  let k : Y.presheaf.stalk y →+* a.fieldRange :=
    e.hom.codRestrict a.fieldRange.toSubring (fun r =>
      (IsGalois.mem_range_algebraMap_iff_fixed (e r)).mpr (hfix r))
  let ev := a.rangeRestrictFieldEquiv.symm.toRingHom.comp k
  have hev : a.comp ev = e.hom := by
    apply RingHom.ext
    intro r
    exact a.rangeRestrictFieldEquiv_apply_symm_apply (k r)
  refine ⟨Spec.map (CommRingCat.ofHom ev) ≫ iy, ?_⟩
  rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, hev]
  exact hfac

#print axioms spec_to_rat_eq
#print axioms exists_extension
#print axioms exists_end_of_morphism
#print axioms point_eq_of_specialization
#print axioms exists_descend_galois

end BShStandard

import ZInQKernel.Contrib.CloudR2Poincare.L3.B2LocalModel
import ZInQKernel.Contrib.CloudR2Poincare.L3.B2ClosedPointDetection
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.Vanishing
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! Rational closed fibres, the actual native model, Jacobson detection and
open restriction are coupled here. No coefficient/model/support Fact is added. -/

noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory

namespace ZInQ.Contrib.CloudR2Poincare.L3
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

/-- Zero homology of a field-valued pullback detects zero actual residue-fibre
rank at its image point, by the proved native upper-semicontinuity inequality. -/
theorem derivedFiberDimension_zero_of_field_model_zero
    {Y : Scheme.{u}} (P : CochainComplex Y.Modules ℤ)
    (hP : ∀ n, ∃ r : ℕ, Nonempty (P.X n ≅
      SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin r))))
    {k : Type u} [Field k] (g : Spec (.of k) ⟶ Y) (x : Spec (.of k)) (q : ℤ)
    (hzero : IsZero ((((Scheme.Modules.pullback g).mapHomologicalComplex _).obj P).homology q)) :
    L1.derivedFiberDimension P q (g x) = 0 := by
  letI : (moduleSpecΓFunctor (R := .of k)).Additive :=
    AlgebraicGeometry.moduleSpecΓFunctorAdditive
  haveI : Subsingleton ((moduleSpecΓFunctor (R := .of k)).obj
      ((((Scheme.Modules.pullback g).mapHomologicalComplex _).obj P).homology q)) :=
    ModuleCat.subsingleton_of_isZero ((moduleSpecΓFunctor (R := .of k)).map_isZero hzero)
  have hz : Module.finrank k ((moduleSpecΓFunctor (R := .of k)).obj
      ((((Scheme.Modules.pullback g).mapHomologicalComplex _).obj P).homology q)) = 0 :=
    Module.finrank_zero_of_subsingleton
  obtain ⟨W, hgW, hle⟩ := Scheme.Modules.exists_finrank_homology_pullback_le hP q
    (Field.toIsField k) g
  have hrange : Set.range (Y.fromSpecResidueField (g x)) ⊆ W := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.fromSpecResidueField_apply]
    exact hgW ⟨x, rfl⟩
  have h := hle (Field.toIsField (Y.residueField (g x)))
    (Y.fromSpecResidueField (g x)) hrange
  rw [hz] at h
  exact Nat.eq_zero_of_le_zero h

/-- Zero restriction near a point gives zero stalk on the original sheaf. -/
theorem subsingleton_stalk_of_isZero_restrict
    {Y : Scheme.{u}} (F : Y.Modules) (U : Y.Opens) (y : Y) (hy : y ∈ U)
    (hzero : IsZero (F.restrict U.ι)) : Subsingleton (F.presheaf.stalk y) := by
  have hsec := (Scheme.Modules.isZero_restrict_iff F U).mp hzero
  have hz (a : F.presheaf.stalk y) : a = 0 := by
    obtain ⟨V, hyV, s, rfl⟩ := F.presheaf.exists_germ_eq a
    have hym : y ∈ V ⊓ U := ⟨hyV, hy⟩
    haveI : Subsingleton Γ(F, V ⊓ U) := hsec (V ⊓ U) inf_le_right
    rw [← F.presheaf.germ_res_apply (homOfLE inf_le_left) y hym s]
    rw [Subsingleton.elim (F.presheaf.map (homOfLE inf_le_left).op s) 0, map_zero]
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

/-- Actual rational fibre vanishing on an open of the abelian base gives a
single neighborhood with all genuine higher direct images zero. -/
theorem exists_zero_higherDirectImage_restriction_of_rational_fibres
    {k : Type u} [Field k] [IsAlgClosed k] (B : PkgI3.AbVar k)
    {X : Scheme.{u}} (f : X ⟶ B.X.left) [IsProper f] [Flat f]
    (F : X.Modules) [F.IsInvertible]
    (slice : (𝟙_ (Over (Spec (.of k))) ⟶ B.X) → (B.X.left ⟶ X))
    (hsquare : ∀ b, IsPullback (slice b) B.X.hom f b.left)
    (V : B.X.left.Opens)
    (hH : ∀ b : 𝟙_ (Over (Spec (.of k))) ⟶ B.X,
      b.left (IsLocalRing.closedPoint k) ∈ V →
      ∀ q : ℕ, Subsingleton (((Scheme.Modules.pullback (slice b)).obj F).H q))
    (y : B.X.left) (hyV : y ∈ V) :
    ∃ W : B.X.left.Opens, y ∈ W ∧
      ∀ q : ℕ, IsZero (((Scheme.Modules.higherDirectImage f q).obj F).restrict W.ι) := by
  classical
  haveI : IsLocallyNoetherian B.X.left := LocallyOfFiniteType.isLocallyNoetherian B.X.hom
  obtain ⟨U, P, bound, hyU, hP, comparison⟩ := exists_local_native_model f F y
  let D : B.X.left.Opens := U ⊓ V
  have hDU : Set.range D.ι ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    exact inf_le_left
  let j : D.toScheme ⟶ U.toScheme := IsOpenImmersion.lift U.ι D.ι hDU
  have hj : j ≫ U.ι = D.ι := IsOpenImmersion.lift_fac _ _ _
  let Q := ((Scheme.Modules.pullback j).mapHomologicalComplex (.up ℤ)).obj P
  have hQ : Scheme.Modules.IsFiniteFreeComplex Q bound := hP.pullback_complex j
  have comparisonQ : UniversalModelComparison f F D Q := comparison.pullback_open j hj
  obtain ⟨r, hr, ⟨e⟩⟩ := hQ.exists_iso_free_of_rank_eq_zero
  let π : D.toScheme ⟶ Spec (.of k) := D.ι ≫ B.X.hom
  haveI : JacobsonSpace D.toScheme := LocallyOfFiniteType.jacobsonSpace π
  have hclosed (z : D.toScheme) (hz : IsClosed ({z} : Set D.toScheme)) (q : ℤ) :
      L1.derivedFiberDimension Q q z = 0 := by
    by_cases hq : q < 0
    · exact derivedFiberDimension_zero_of_rank_zero Q r e q (hr q (Or.inl hq)) z
    · have hn : (q.toNat : ℤ) = q := Int.toNat_of_nonneg (by omega)
      let g : Spec (.of k) ⟶ D.toScheme := pointOfClosedPoint π z hz
      let b : 𝟙_ (Over (Spec (.of k))) ⟶ B.X := Over.homMk (g ≫ D.ι) (by
        change (g ≫ D.ι) ≫ B.X.hom = 𝟙 (Spec (.of k))
        simpa only [Category.assoc, π, g] using pointOfClosedPoint_comp π z hz)
      have hbV : b.left (IsLocalRing.closedPoint k) ∈ V := by
        change D.ι (g (IsLocalRing.closedPoint k)) ∈ V
        rw [pointOfClosedPoint_apply]
        exact z.property.2
      have hzero := model_rational_fibre_homology_zero B f F D Q comparisonQ g (slice b)
        (by exact hsquare b) q.toNat (hH b hbV q.toNat)
      have hd := derivedFiberDimension_zero_of_field_model_zero Q hQ.exists_iso_free g
        (IsLocalRing.closedPoint k) (q.toNat : ℤ) hzero
      simpa only [g, pointOfClosedPoint_apply, hn] using hd
  let yd : D.toScheme := ⟨y, hyU, hyV⟩
  obtain ⟨W, hyW, zero⟩ := locally_universally_zero_of_closed_fibre_zero Q r e bound hr hclosed yd
  let T : B.X.left.Opens := D.ι ''ᵁ W
  have hTD : Set.range T.ι ⊆ Set.range D.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨z, rfl⟩
  let g : T.toScheme ⟶ D.toScheme := IsOpenImmersion.lift D.ι T.ι hTD
  have hg : g ≫ D.ι = T.ι := IsOpenImmersion.lift_fac _ _ _
  have hgW : Set.range g ⊆ W := by
    rintro _ ⟨z, rfl⟩
    rw [← Scheme.Hom.preimage_image_eq D.ι W]
    change D.ι (g z) ∈ T
    rw [← Scheme.Hom.comp_apply, hg]
    exact z.property
  refine ⟨T, ⟨yd, hyW, rfl⟩, fun q => ?_⟩
  obtain ⟨eR⟩ := nonempty_model_restriction_iso f F comparisonQ g hg q
  exact (zero g hgW q).of_iso eR

end ZInQ.Contrib.CloudR2Poincare.L3

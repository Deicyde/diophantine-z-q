import ZInQKernel.Contrib.OneProof.FaltingsDVR.FaltingsImageGroup
import ZInQKernel.Contrib.OneProof.FaltingsDVR.FaltingsImagePoints
import ZInQKernel.Contrib.OneProof.FaltingsDVR.FaltingsSemistableKernel
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_isReduced_of_smooth_of_field
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_smoothOfRelativeDimension_range_eq_connectedComponent_of_perfectField

/-! A rational group image in an abelian variety with no invertible-order torsion is finite. -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ.HeightSplit ZInQ.SemiAbDescend ZInQ.Contrib.MilneQuasiInverse.Kernel
open ZInQ.Contrib.CloudW03NeronSurj.FLT
open ZInQ.Contrib.CloudW03NeronSurj.FLT.GoodReductionJacobian
open ZInQ.Contrib.CloudW03NeronSurj.FLT.NeronModelInfra

set_option linter.style.haveILetI false
set_option maxHeartbeats 1200000

namespace ZInQ.FaltingsRestate

/-- Consequence of the prime-to-characteristic torsion count for abelian
varieties over an algebraically closed field. -/
def AbelianPointsSubsingletonOfNoInvertibleTorsion : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (A : PkgI3.AbVar k) (n : ℕ)
    (_hn : topologicalKrullDim A.X.left = (n : WithBot ℕ∞)),
    (∀ m : ℕ, (m : k) ≠ 0 → ∀ p : algPt k k ⟶ A.X, p ^ m = 1 → p = 1) →
    Subsingleton (algPt k k ⟶ A.X)

section Groups

variable {k : Type} [Field k] [IsAlgClosed k]
local notation "Sch" => Over (Spec (CommRingCat.of k))
local notation "Pt" => 𝟙_ Sch

private def algPtUnitIso : algPt k k ≅ Pt :=
  Over.isoMk (Iso.refl _) (by simp [algPt])

private def algPtEquivUnit (G : Sch) [GrpObj G] :
    (algPt k k ⟶ G) ≃* (Pt ⟶ G) where
  toFun p := algPtUnitIso.inv ≫ p
  invFun p := algPtUnitIso.hom ≫ p
  left_inv p := by
    change algPtUnitIso.hom ≫ algPtUnitIso.inv ≫ p = p
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  right_inv p := by
    change algPtUnitIso.inv ≫ algPtUnitIso.hom ≫ p = p
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  map_mul' x y := MonObj.comp_mul algPtUnitIso.inv x y

set_option backward.isDefEq.respectTransparency false in
/-- A proper algebraic group with no invertible-order torsion has finitely
many rational points if the torsion count holds for its abelian component. -/
theorem finite_points_of_proper_group_no_invertible_torsion
    (hA : AbelianPointsSubsingletonOfNoInvertibleTorsion)
    (G : Sch) [GrpObj G] [IsProper G.hom]
    (hG : ∀ m : ℕ, (m : k) ≠ 0 → ∀ p : algPt k k ⟶ G, p ^ m = 1 → p = 1) :
    Finite (algPt k k ⟶ G) := by
  letI : GrpObj (Over.mk G.hom) := inferInstanceAs (GrpObj G)
  let L := relativeGroupLawOfGrpObj k G.hom
  obtain ⟨X, i, L₀, n, hi, hir, hsm, hgi, _, _, hdim, hmul, _, reps, hRepFin, hRep⟩ :=
    L.exists_isClosedImmersion_smoothOfRelativeDimension_range_eq_connectedComponent_of_perfectField k
  let G₀ := Over.mk (i ≫ G.hom)
  let j : G₀ ⟶ G := Over.homMk i rfl
  letI : GrpObj G₀ := L₀.grpObjOverMk
  haveI : IsClosedImmersion j.left := hi
  haveI : IsClosedImmersion i := hi
  haveI : Mono j := Over.mono_of_mono_left j
  haveI : IsMonHom j := isMonHom_of_relativeGroupLaw_mul G G₀ L₀ j hmul
  haveI : SmoothOfRelativeDimension n G₀.hom := hsm
  haveI : Smooth G₀.hom := SmoothOfRelativeDimension.smooth (n := n) G₀.hom
  haveI : IsProper G₀.hom := show IsProper (i ≫ G.hom) by infer_instance
  haveI : GeometricallyIrreducible G₀.hom := hgi
  haveI : GeometricallyReduced G₀.hom := by
    refine ⟨fun K _ y Z fst snd h => ?_⟩
    haveI : Smooth snd := MorphismProperty.of_isPullback (P := @Smooth) h inferInstance
    exact ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.isReduced_of_smooth_of_field snd
  haveI : GeometricallyIntegral G₀.hom := by
    rw [GeometricallyIntegral.eq_geometricallyReduced_inf_geometricallyIrreducible]
    exact ⟨inferInstance, inferInstance⟩
  let A : PkgI3.AbVar k :=
    { X := G₀
      grp := inferInstance
      proper := inferInstance
      smooth := inferInstance
      geomInt := inferInstance }
  have h₀ : ∀ m : ℕ, (m : k) ≠ 0 → ∀ p : algPt k k ⟶ G₀, p ^ m = 1 → p = 1 := by
    intro m hm p hp
    apply (cancel_mono j).mp
    rw [MonObj.one_comp]
    apply hG m hm
    change pointsMap j (algPt k k) p ^ m = 1
    rw [← map_pow, hp, map_one]
  haveI : Subsingleton (algPt k k ⟶ G₀) := hA k A n hdim h₀
  haveI : Finite (Pt ⟶ G₀) := Finite.of_equiv _ (algPtEquivUnit G₀).toEquiv
  let repsToPt : reps → (Pt ⟶ G) := fun x =>
    (overHomEquivSchemeHomOver Pt G.hom).symm x.1
  let v : reps × (Pt ⟶ G₀) → (Pt ⟶ G) :=
    fun a => repsToPt a.1 * (a.2 ≫ j)
  haveI : Finite reps := hRepFin
  have hv : Function.Surjective v := by
    intro z
    let e := overHomEquivSchemeHomOver Pt G.hom
    let e₀ := overHomEquivSchemeHomOver Pt G₀.hom
    obtain ⟨s, hs, a, ha⟩ := hRep (e z)
    let t := e₀.symm a
    refine ⟨(⟨s, hs⟩, t), ?_⟩
    apply e.injective
    change e (repsToPt ⟨s, hs⟩ * (t ≫ j)) = e z
    rw [ha]
    apply Subtype.ext
    rfl
  haveI : Finite (Pt ⟶ G) := Finite.of_surjective v hv
  exact Finite.of_injective (algPtEquivUnit G) (algPtEquivUnit G).injective

set_option backward.isDefEq.respectTransparency false in
/-- The remaining abelian image assertion in the semiabelian kernel proof. -/
theorem finiteAbelianImageOfNoInvertibleTorsion
    (hA : AbelianPointsSubsingletonOfNoInvertibleTorsion) :
    FiniteAbelianImageOfNoInvertibleTorsion := by
  intro k _ _ B X _ _ _ g _ h
  haveI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  haveI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  haveI : IsNoetherian X.left := {}
  haveI : QuasiCompact g.left := inferInstance
  obtain ⟨Z, hZG, i, hiM, hi, q, hqM, hqD, hqC, hfac⟩ := exists_group_scheme_image g
  letI : GrpObj Z := hZG
  haveI : IsMonHom i := hiM
  haveI : IsClosedImmersion i.left := hi
  haveI : Mono i := Over.mono_of_mono_left i
  haveI : IsMonHom q := hqM
  haveI : IsDominant q.left := hqD
  haveI : QuasiCompact q.left := hqC
  haveI : IsProper Z.hom := by
    rw [← Over.w i]
    infer_instance
  have hs : Function.Surjective (pointsMap q (algPt k k)) := by
    intro z
    let eZ := algPtEquivUnit Z
    let eX := algPtEquivUnit X
    obtain ⟨x, hx⟩ := surjective_points_of_dominant_group_hom q (eZ z)
    refine ⟨eX.symm x, eZ.injective ?_⟩
    change (algPtUnitIso.inv ≫ eX.symm x ≫ q) = eZ z
    rw [← Category.assoc]
    exact (congrArg (fun u => u ≫ q) (eX.apply_symm_apply x)).trans hx
  have hZ (m : ℕ) (hm : (m : k) ≠ 0) (z : algPt k k ⟶ Z) (hz : z ^ m = 1) : z = 1 := by
    obtain ⟨x, hx⟩ := hs z
    change x ≫ q = z at hx
    subst z
    apply (cancel_mono i).mp
    rw [MonObj.one_comp]
    change (x ≫ q) ≫ i = 1
    rw [Category.assoc, hfac]
    apply h m hm x
    change (x ≫ q) ^ m = 1 at hz
    rw [← hfac, ← Category.assoc]
    change pointsMap i (algPt k k) (x ≫ q) ^ m = 1
    rw [← map_pow, hz, map_one]
  haveI : Finite (algPt k k ⟶ Z) := finite_points_of_proper_group_no_invertible_torsion hA Z hZ
  have hsub : Set.range (pointsMap g (algPt k k)) ⊆ Set.range (pointsMap i (algPt k k)) := by
    rintro _ ⟨x, rfl⟩
    refine ⟨x ≫ q, ?_⟩
    change (x ≫ q) ≫ i = x ≫ g
    rw [Category.assoc, hfac]
  exact (Set.finite_range (pointsMap i (algPt k k))).subset hsub

end Groups

end ZInQ.FaltingsRestate

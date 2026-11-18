import ZInQKernel.Contrib.MulEtale.Direct.OriginNeighbourhood
import ZInQKernel.Contrib.MulEtale.Direct.FieldTranslationDescent
import ZInQKernel.Contrib.MulEtale.Direct.FibreMultiplication
import ZInQKernel.Contrib.MulEtale.Direct.Global.SmoothFiberDetector

/-!
# Multiplication by a unit is étale on every smooth commutative group scheme

Generalization of the H-101 multiplication-étale theorem from abelian schemes to arbitrary smooth
commutative group schemes `A` over `Spec O`, `O` any commutative ring, `m` invertible in `O`:
`[m] = (𝟙 A ^ m).left` is étale. No properness, no connectedness or geometric integrality of the
fibres, and no finiteness of `[m]` is used: the statement applies to Néron models with toric or
disconnected special fibre.

The route is the one of H-101 with its only use of properness removed:
* over a field, the actual étale neighbourhood of the unit for `[m]`
  (`LocalPromotion.exists_etale_open_mul_at_unit_of_isUnit`, smooth group objects) is translated
  to every closed point over an algebraic closure (`Translation.etale_pow_id_left_of_isAlgClosed`,
  commutative locally finite type group objects) and descended along the faithfully flat field
  extension. The base-changed group's commutativity is derived from the commutativity of `G`
  through the braided base-change functor, where H-101 derived it from properness and geometric
  integrality. The base-changed group law is the one of `Functor.grpObjObj`, whose underlying
  monoid structure is `Functor.monObjObj` by definition (`grpObjObj_toMonObj`, `rfl`);
* over any base, the fibre detector `etale_of_smooth_structural_and_etale_fibers` applies to the
  actual residue fibres `fibreGrp A s`, which are smooth and commutative by base change.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace HenselDivision.SmoothCommMulEtale

universe u

section Reconcile

variable {C D : Type*} [Category C] [Category D] [CartesianMonoidalCategory C]
  [CartesianMonoidalCategory D]

open scoped CategoryTheory.Obj in
/-- The monoid structure underlying `Functor.grpObjObj` is `Functor.monObjObj`, definitionally. -/
theorem grpObjObj_toMonObj (F : C ⥤ D) [F.Monoidal] (G : C) [GrpObj G] :
    (Functor.grpObjObj (F := F) (G := G)).toMonObj = Functor.monObjObj (F := F) G := rfl

/-- The base change of a commutative group object along a braided functor is commutative, for the
group structure `Functor.grpObjObj`. -/
theorem isCommMonObj_grpObjObj [BraidedCategory C] [BraidedCategory D] (F : C ⥤ D) [F.Braided]
    (G : C) [GrpObj G] [IsCommMonObj G] :
    letI : GrpObj (F.obj G) := Functor.grpObjObj
    IsCommMonObj (F.obj G) := by
  letI : GrpObj (F.obj G) := Functor.grpObjObj
  constructor
  change (β_ (F.obj G) (F.obj G)).hom ≫ (Functor.LaxMonoidal.μ F G G ≫ F.map μ[G]) =
    Functor.LaxMonoidal.μ F G G ≫ F.map μ[G]
  rw [← Functor.LaxBraided.braided_assoc, ← Functor.map_comp, IsCommMonObj.mul_comm]

end Reconcile

/-! ### Over a field -/

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **Field step for smooth commutative group schemes.** An actual étale open neighbourhood of the
unit for `[m]` makes `[m]` étale. (Proof of `Translation.etale_pow_id_left_of_etale_unit_nbhd`
with properness and geometric integrality replaced by commutativity.) -/
theorem etale_pow_id_left_of_etale_unit_nbhd_comm {k : Type u} [Field k]
    (G : Over (Spec (.of k))) [GrpObj G] [Smooth G.hom] [IsCommMonObj G] (m : ℕ)
    (s : Spec (.of k))
    (H : ∃ V : G.left.Opens, IsAffineOpen V ∧ η[G].left s ∈ V ∧
      Etale (V.ι ≫ (𝟙 G ^ m : G ⟶ G).left)) :
    Etale ((𝟙 G ^ m : G ⟶ G).left) := by
  obtain ⟨V, -, hsV, hV⟩ := H
  let Ω : Type u := AlgebraicClosure k
  let g : Spec (.of Ω) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom <| algebraMap k Ω)
  let G' : Over (Spec (.of Ω)) := (Over.pullback g).obj G
  let : GrpObj G' := Functor.grpObjObj
  have : Smooth G'.hom := by dsimp [G']; infer_instance
  -- commutativity of the actual base-changed group, from the commutativity of `G`
  have : IsCommMonObj G' := isCommMonObj_grpObjObj (Over.pullback g) G
  -- the actual base change of `[m]` is `[m]` of `G'`
  have hpow : (Over.pullback g).map (𝟙 G ^ m) = (𝟙 G' ^ m : G' ⟶ G') := by
    have h : (Over.pullback g).map (𝟙 G ^ m) = ((Over.pullback g).map (𝟙 G)) ^ m :=
      map_pow ((Over.pullback g).homMonoidHom (X := G) (M := G)) (𝟙 G) m
    rw [CategoryTheory.Functor.map_id] at h
    exact h
  have sq := H101DirectFieldRoute.Translation.isPullback_overPullback_map_left g (𝟙 G ^ m)
  -- the unit neighbourhood transported to `G'`
  have hV' : Etale ((pullback.fst G.hom g ⁻¹ᵁ V).ι ≫ (𝟙 G' ^ m : G' ⟶ G').left) := by
    have big := ((isPullback_morphismRestrict (pullback.fst G.hom g) V).flip.paste_horiz
      sq.flip).flip
    rw [← hpow]
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Etale) big hV
  let z : (𝟙_ (Over (Spec (.of Ω)))).left := IsLocalRing.closedPoint Ω
  have he' : η[G'].left z ∈ pullback.fst G.hom g ⁻¹ᵁ V := by
    rw [Scheme.Hom.mem_preimage]
    have hl : ((Over.pullback g).map η[G]).left ≫ pullback.fst G.hom g =
        pullback.fst (𝟙_ (Over (Spec (.of k)))).hom g ≫ η[G].left :=
      pullback.lift_fst _ _ _
    have h1 : η[G'].left ≫ pullback.fst G.hom g =
        (Functor.LaxMonoidal.ε (Over.pullback g)).left ≫
          pullback.fst (𝟙_ (Over (Spec (.of k)))).hom g ≫ η[G].left := by
      change (Functor.LaxMonoidal.ε (Over.pullback g) ≫ (Over.pullback g).map η[G]).left ≫
        pullback.fst G.hom g = _
      rw [Over.comp_left, Category.assoc, hl]
    have h2 : (η[G'].left ≫ pullback.fst G.hom g) z =
        ((Functor.LaxMonoidal.ε (Over.pullback g)).left ≫
          pullback.fst (𝟙_ (Over (Spec (.of k)))).hom g ≫ η[G].left) z := by
      rw [h1]
    simp only [Scheme.Hom.comp_apply] at h2
    have hz : pullback.fst (𝟙_ (Over (Spec (.of k)))).hom g
        ((Functor.LaxMonoidal.ε (Over.pullback g)).left z) = s :=
      Subsingleton.elim (α := Spec (.of k)) _ _
    have h3 : pullback.fst G.hom g (η[G'].left z) = η[G].left s :=
      h2.trans (congrArg (fun p ↦ η[G].left p) hz)
    exact (congrArg (fun y ↦ y ∈ V) h3).mpr hsV
  -- étale over the algebraic closure, by translation
  have hG' : Etale (𝟙 G' ^ m : G' ⟶ G').left :=
    H101DirectFieldRoute.Translation.etale_pow_id_left_of_isAlgClosed G' m z _ he' hV'
  rw [← hpow] at hG'
  -- fpqc descent along the faithfully flat base change
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := @Etale) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) sq.flip
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hG'

/-- **`[m]` is étale on a smooth commutative group scheme over a field** when `m` is a unit. -/
theorem etale_pow_id_left_of_isUnit_comm {k : Type u} [Field k]
    (G : Over (Spec (.of k))) [GrpObj G] [Smooth G.hom] [IsCommMonObj G] (m : ℕ)
    (hm : IsUnit (m : k)) :
    Etale ((𝟙 G ^ m : G ⟶ G).left) :=
  etale_pow_id_left_of_etale_unit_nbhd_comm G m (IsLocalRing.closedPoint k)
    (H101DirectFieldRoute.LocalPromotion.exists_etale_open_mul_at_unit_of_isUnit k G m hm
      (IsLocalRing.closedPoint k))

/-! ### Over an arbitrary base -/

open ZInQ.Contrib.MulEtale.FibreMaps
open H101DirectGlobalDetection.CanonicalFibres

variable {O : Type} [CommRing O]

/-- The actual residue fibres of a smooth commutative group scheme have étale `[m]`. -/
theorem fibre_pow_etale_comm (A : Grp (Over (Spec (.of O)))) [Smooth A.X.hom]
    [IsCommMonObj A.X] (s : Spec (.of O)) (m : ℕ) (hm : IsUnit (m : O)) :
    Etale ((𝟙 (fibreGrp A s).X ^ m : (fibreGrp A s).X ⟶ (fibreGrp A s).X).left) := by
  letI : GrpObj (fibreGrp A s).X := (fibreGrp A s).grp
  have : Smooth (fibreGrp A s).X.hom := by
    change Smooth (pullback.snd A.X.hom ((Spec (.of O)).fromSpecResidueField s))
    infer_instance
  have : IsCommMonObj (fibreGrp A s).X :=
    isCommMonObj_grpObjObj (Over.pullback ((Spec (.of O)).fromSpecResidueField s)) A.X
  exact etale_pow_id_left_of_isUnit_comm (k := (Spec (.of O)).residueField s)
    (fibreGrp A s).X m (isUnit_residue_natCast s m hm)

/-- The detector's actual fibre map is étale. -/
theorem fiberHom_pow_etale_comm (A : Grp (Over (Spec (.of O)))) [Smooth A.X.hom]
    [IsCommMonObj A.X] (s : Spec (.of O)) (m : ℕ) (hm : IsUnit (m : O)) :
    Etale (fiberHom (𝟙 A.X ^ m : A.X ⟶ A.X).left A.X.hom s) := by
  rw [H101DirectFieldRoute.FibreMultiplication.fiberHom_pow_eq]
  letI : Etale ((𝟙 (fibreGrp A s).X ^ m : (fibreGrp A s).X ⟶ (fibreGrp A s).X).left) :=
    fibre_pow_etale_comm A s m hm
  letI : Etale (fibreMulDomainIso A s m).hom := inferInstance
  exact Etale.etale_comp (fibreMulDomainIso A s m).hom
    (𝟙 (fibreGrp A s).X ^ m : (fibreGrp A s).X ⟶ (fibreGrp A s).X).left

/-- **Multiplication by a unit is étale on every smooth commutative group scheme over `Spec O`.** -/
theorem multiplication_etale_of_smooth_comm (A : Grp (Over (Spec (.of O)))) [Smooth A.X.hom]
    [IsCommMonObj A.X] (m : ℕ) (hm : IsUnit (m : O)) :
    Etale ((𝟙 A.X ^ m : A.X ⟶ A.X).left) := by
  letI : Smooth ((𝟙 A.X ^ m : A.X ⟶ A.X).left ≫ A.X.hom) := by
    rw [Over.w]
    infer_instance
  exact H101DirectGlobalDetection.etale_of_smooth_structural_and_etale_fibers
    (𝟙 A.X ^ m : A.X ⟶ A.X).left A.X.hom (fun s => fiberHom_pow_etale_comm A s m hm)

end HenselDivision.SmoothCommMulEtale

#check @HenselDivision.SmoothCommMulEtale.grpObjObj_toMonObj
#check @HenselDivision.SmoothCommMulEtale.etale_pow_id_left_of_isUnit_comm
#check @HenselDivision.SmoothCommMulEtale.multiplication_etale_of_smooth_comm
#print axioms HenselDivision.SmoothCommMulEtale.isCommMonObj_grpObjObj
#print axioms HenselDivision.SmoothCommMulEtale.etale_pow_id_left_of_isUnit_comm
#print axioms HenselDivision.SmoothCommMulEtale.multiplication_etale_of_smooth_comm

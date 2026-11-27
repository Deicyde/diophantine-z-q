import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.Representability
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.ProperSmooth
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.PacketTarget
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV
open scoped CategoryTheory.Obj
set_option autoImplicit false
namespace Y3Buzzard

/-!
# Assembly of the level-3 packet from the leaves (draft)

1. Generic facts: `iota 0` is the zero map, `iota (-1)` is the inverse.
2. The comparison maps `actionTot` preserve the unit and the inverse.
3. The fibre-power map as a base change of `qX` (standalone copies of the statements of the
   descent file), the diagonal action on `A x_X A`, and its kernel-pair square.
4. `descentInputOf`: the descent input of a level-(5,3) datum and a quotient datum.
5. Discharged leaves: geometric fibres exist (by base change), and the quotient map is etale
   (by descent along itself).
6. `y3Packet_of_leaves`.

Compatibility of the diagonal action with multiplication (`ActionMulCompat`) is kept as a
hypothesis: it says that each `actionTot M d` is a homomorphism of group schemes over
`actionMap M d`.
-/

attribute [local instance] FEC.grp

/-! ## 1. Generic facts on false elliptic curves -/

section Generic

variable {S : Scheme.{0}}

theorem toUnit_left_eq (U : Over S) : (toUnit U).left = U.hom := by
  first
    | rfl
    | exact Over.toUnit_left U
    | simpa using Over.w (toUnit U)

theorem oneL_sec' (A : FEC S) : oneL A ≫ A.F.hom = 𝟙 S :=
  Over.w (MonObj.one : 𝟙_ (Over S) ⟶ A.F)

/-- `iota 0` is the zero map: it sends a point to the unit over its image. -/
theorem iota_zero_eq (A : FEC S) {T : Scheme.{0}} (y : T ⟶ A.F.left) :
    y ≫ A.iota 0 = (y ≫ A.F.hom) ≫ oneL A := by
  have h : (Over.homMk (U := Over.mk (y ≫ A.F.hom)) y rfl : Over.mk (y ≫ A.F.hom) ⟶ A.F) ≫
      (Over.homMk (A.iota 0) (A.iota_over 0) : A.F ⟶ A.F) = 1 := by
    rw [iotaHom_zero, MonObj.comp_one]
  have hl := congrArg (fun f : Over.mk (y ≫ A.F.hom) ⟶ A.F => f.left) h
  have e1 : ((Over.homMk (U := Over.mk (y ≫ A.F.hom)) y rfl : Over.mk (y ≫ A.F.hom) ⟶ A.F) ≫
      (Over.homMk (A.iota 0) (A.iota_over 0) : A.F ⟶ A.F)).left = y ≫ A.iota 0 := rfl
  have e2 : (1 : Over.mk (y ≫ A.F.hom) ⟶ A.F).left =
      (toUnit (Over.mk (y ≫ A.F.hom))).left ≫ oneL A := rfl
  have e3 : (toUnit (Over.mk (y ≫ A.F.hom))).left = y ≫ A.F.hom :=
    toUnit_left_eq (Over.mk (y ≫ A.F.hom))
  exact e1.symm.trans (hl.trans (e2.trans (congrArg (fun t => t ≫ oneL A) e3)))

theorem one_mul_inv_eq_one (A : FEC S) : (𝟙 A.F) * (GrpObj.inv : A.F ⟶ A.F) = 1 := by
  first
    | exact GrpObj.right_inv A.F
    | exact GrpObj.right_inv
    | exact GrpObj.right_inv'
    | (show lift (𝟙 A.F) GrpObj.inv ≫ MonObj.mul = toUnit A.F ≫ MonObj.one; simp)

/-- `iota (-1)` is the inverse of the group law. -/
theorem invL_eq_iota (A : FEC S) : invL A = A.iota (-1) := by
  have h := A.iota_add (-1) 1
  have e0 : (-1 : O) + 1 = 0 := by
    first
      | exact neg_add_cancel 1
      | simp
  rw [e0, iotaHom_zero, iotaHom_one] at h
  -- `h : 1 = x * 𝟙 A.F` with `x` the homomorphism `iota (-1)`
  have hx : (Over.homMk (A.iota (-1)) (A.iota_over (-1)) : A.F ⟶ A.F) =
      (GrpObj.inv : A.F ⟶ A.F) :=
    calc (Over.homMk (A.iota (-1)) (A.iota_over (-1)) : A.F ⟶ A.F)
        = (Over.homMk (A.iota (-1)) (A.iota_over (-1)) : A.F ⟶ A.F) * 1 :=
          (_root_.mul_one _).symm
      _ = (Over.homMk (A.iota (-1)) (A.iota_over (-1)) : A.F ⟶ A.F) *
            ((𝟙 A.F) * (GrpObj.inv : A.F ⟶ A.F)) := by rw [one_mul_inv_eq_one]
      _ = ((Over.homMk (A.iota (-1)) (A.iota_over (-1)) : A.F ⟶ A.F) * 𝟙 A.F) *
            (GrpObj.inv : A.F ⟶ A.F) := (_root_.mul_assoc _ _ _).symm
      _ = 1 * (GrpObj.inv : A.F ⟶ A.F) := by rw [← h]
      _ = (GrpObj.inv : A.F ⟶ A.F) := _root_.one_mul _
  have hl := congrArg (fun f : A.F ⟶ A.F => f.left) hx
  have e1 : (Over.homMk (A.iota (-1)) (A.iota_over (-1)) : A.F ⟶ A.F).left = A.iota (-1) := rfl
  exact (e1.symm.trans hl).symm

end Generic

/-! ## 2. The comparison maps preserve the unit and the inverse -/

section Action

variable (M : Moduli35)

theorem actionTot_oneL (d : Y3OrderMod.G 5) :
    (actionMap M d).left ≫ oneL M.A = oneL M.A ≫ actionTot M d := by
  have hsec := oneL_sec' M.A
  have h0 : oneL M.A ≫ M.A.iota 0 = oneL M.A := by
    rw [iota_zero_eq, hsec, Category.id_comp]
  symm
  calc oneL M.A ≫ actionTot M d = (oneL M.A ≫ M.A.iota 0) ≫ actionTot M d := by rw [h0]
    _ = oneL M.A ≫ (M.A.iota 0 ≫ actionTot M d) := Category.assoc _ _ _
    _ = oneL M.A ≫ (actionTot M d ≫ M.A.iota 0) := by rw [actionTot_iota]
    _ = (oneL M.A ≫ actionTot M d) ≫ M.A.iota 0 := (Category.assoc _ _ _).symm
    _ = ((oneL M.A ≫ actionTot M d) ≫ M.A.F.hom) ≫ oneL M.A := iota_zero_eq M.A _
    _ = oneL M.A ≫ actionTot M d ≫ M.A.F.hom ≫ oneL M.A := by simp only [Category.assoc]
    _ = oneL M.A ≫ M.A.F.hom ≫ (actionMap M d).left ≫ oneL M.A := by
        rw [reassoc_of% (actionTot_w M d)]
    _ = (actionMap M d).left ≫ oneL M.A := by rw [reassoc_of% hsec]

theorem actionTot_invL (d : Y3OrderMod.G 5) :
    actionTot M d ≫ invL M.A = invL M.A ≫ actionTot M d := by
  have e := invL_eq_iota M.A
  exact (congrArg (fun t => actionTot M d ≫ t) e).trans
    ((actionTot_iota M d (-1)).symm.trans (congrArg (fun t => t ≫ actionTot M d) e.symm))

end Action

/-! ## 3. The fibre-power map and its kernel pair -/

section FibrePower

variable {X Y B : Scheme.{0}} (A : FEC X) (qX : X ⟶ Y) (qA : A.F.left ⟶ B) (b : B ⟶ Y)
  (hpb : IsPullback qA A.F.hom b qX)

theorem fibrePowerMap_w :
    fibrePowerMap A qX qA b hpb ≫ (Over.mk b ⊗ Over.mk b).hom = (A.F ⊗ A.F).hom ≫ qX :=
  calc fibrePowerMap A qX qA b hpb ≫ (Over.mk b ⊗ Over.mk b).hom
      = (sqTensorIsoOf A qX qA b hpb).inv.left ≫ pullback.fst (Over.mk b ⊗ Over.mk b).hom qX ≫
          (Over.mk b ⊗ Over.mk b).hom := Category.assoc _ _ _
    _ = (sqTensorIsoOf A qX qA b hpb).inv.left ≫
          pullback.snd (Over.mk b ⊗ Over.mk b).hom qX ≫ qX := by
        rw [pullback.condition]
    _ = ((sqTensorIsoOf A qX qA b hpb).inv.left ≫
          pullback.snd (Over.mk b ⊗ Over.mk b).hom qX) ≫ qX := (Category.assoc _ _ _).symm
    _ = (A.F ⊗ A.F).hom ≫ qX :=
        congrArg (fun k => k ≫ qX) (Over.w (sqTensorIsoOf A qX qA b hpb).inv)

/-- The fibre-power map is a base change of `qX`. -/
theorem fibrePowerMap_isPullback :
    IsPullback (fibrePowerMap A qX qA b hpb) (A.F ⊗ A.F).hom (Over.mk b ⊗ Over.mk b).hom qX :=
  IsPullback.of_iso_pullback ⟨fibrePowerMap_w A qX qA b hpb⟩
    ((Over.forget X).mapIso (sqTensorIsoOf A qX qA b hpb).symm) rfl
    (Over.w (sqTensorIsoOf A qX qA b hpb).inv)

end FibrePower

section Diagonal

variable (M : Moduli35) (Q : QuotientData M)

/-- The diagonal action on `A x_X A`: the unique map fixing the fibre-power map and lying over
`ρ d`. -/
def actAA (d : Y3OrderMod.G 5) : (M.A.F ⊗ M.A.F).left ⟶ (M.A.F ⊗ M.A.F).left :=
  (fibrePowerMap_isPullback M.A Q.qX Q.qA Q.b Q.cart).lift
    (fibrePowerMap M.A Q.qX Q.qA Q.b Q.cart) ((M.A.F ⊗ M.A.F).hom ≫ (ρ M d).asIso.hom) (by
      rw [Category.assoc, act_comp_eq (ρ M) Q.kpX d]
      exact fibrePowerMap_w M.A Q.qX Q.qA Q.b Q.cart)

theorem actAA_q (d : Y3OrderMod.G 5) :
    actAA M Q d ≫ fibrePowerMap M.A Q.qX Q.qA Q.b Q.cart =
      fibrePowerMap M.A Q.qX Q.qA Q.b Q.cart :=
  (fibrePowerMap_isPullback M.A Q.qX Q.qA Q.b Q.cart).lift_fst _ _ _

theorem actAA_hom (d : Y3OrderMod.G 5) :
    actAA M Q d ≫ (M.A.F ⊗ M.A.F).hom = (M.A.F ⊗ M.A.F).hom ≫ (ρ M d).asIso.hom :=
  (fibrePowerMap_isPullback M.A Q.qX Q.qA Q.b Q.cart).lift_snd _ _ _

/-- The kernel pair of the fibre-power map is `∐ (_ : G 5), A x_X A`, by pasting with the
kernel-pair square of `qX` and finitary extensivity. -/
theorem kpAA :
    IsPullback (Sigma.desc (actAA M Q))
      (Y3QuotientDescent.actT (M.A.F ⊗ M.A.F).left (Y3OrderMod.G 5))
      (fibrePowerMap M.A Q.qX Q.qA Q.b Q.cart) (fibrePowerMap M.A Q.qX Q.qA Q.b Q.cart) :=
  kp_baseChange (ρ M) Q.kpX (fibrePowerMap_isPullback M.A Q.qX Q.qA Q.b Q.cart) (actAA M Q)
    (actAA_q M Q) (actAA_hom M Q)

end Diagonal

/-- Hypothesis: the diagonal action on `A x_X A` commutes with the group law, that is, each
comparison map `actionTot M d` is a homomorphism of group schemes over `actionMap M d`. -/
def ActionMulCompat : Prop :=
  ∀ (M : Moduli35) (Q : QuotientData M) (d : Y3OrderMod.G 5),
    actAA M Q d ≫ mulL M.A = mulL M.A ≫ actionTot M d

/-- `ActionMulCompat` over a locally noetherian base; the packet uses it only there. -/
def ActionMulCompatLN : Prop :=
  ∀ (M : Moduli35) (Q : QuotientData M), IsLocallyNoetherian M.X.left →
    ∀ d : Y3OrderMod.G 5, actAA M Q d ≫ mulL M.A = mulL M.A ≫ actionTot M d

theorem actionMulCompatLN_of (h : ActionMulCompat) : ActionMulCompatLN :=
  fun M Q _ d => h M Q d

/-! ## 4. The descent input -/

/-- The descent input of a level-(5,3) datum and a quotient datum. -/
def descentInputOf (M : Moduli35) (Q : QuotientData M)
    (hmul : ∀ d : Y3OrderMod.G 5, actAA M Q d ≫ mulL M.A = mulL M.A ≫ actionTot M d) :
    DescentInput M.X.left Q.Y where
  A := M.A
  G := Y3OrderMod.G 5
  actX g := (ρ M g).asIso.hom
  actA g := (ρA M g).asIso.hom
  act_over := ρA_equivariant M
  act_iota g a := (ρA_iota M g a).symm
  act_one g := actionTot_oneL M g
  act_inv g := actionTot_invL M g
  actAA := actAA M Q
  act_mul := hmul
  qX := Q.qX
  finite := Q.finX
  flat := Q.flatX
  surj := Q.surjX
  RX := ∐ fun _ : Y3OrderMod.G 5 => M.X.left
  aX := Y3QuotientDescent.actS (ρ M)
  prX := Y3QuotientDescent.actT M.X.left (Y3OrderMod.G 5)
  hKX := Q.kpX
  incX g := Sigma.ι (fun _ : Y3OrderMod.G 5 => M.X.left) g
  incX_a g := ι_actS (ρ M) g
  incX_pr g := ι_actT M.X.left g
  incX_jointlyEpi u v h := Sigma.hom_ext u v h
  B := Q.B
  qA := Q.qA
  RA := ∐ fun _ : Y3OrderMod.G 5 => M.A.F.left
  aA := Y3QuotientDescent.actS (ρA M)
  prA := Y3QuotientDescent.actT M.A.F.left (Y3OrderMod.G 5)
  hKA := Q.kpA
  incA g := Sigma.ι (fun _ : Y3OrderMod.G 5 => M.A.F.left) g
  incA_a g := ι_actS (ρA M) g
  incA_pr g := ι_actT M.A.F.left g
  incA_jointlyEpi u v h := Sigma.hom_ext u v h
  b := Q.b
  hpb := Q.cart
  RAA := ∐ fun _ : Y3OrderMod.G 5 => (M.A.F ⊗ M.A.F).left
  aAA := Sigma.desc (actAA M Q)
  prAA := Y3QuotientDescent.actT (M.A.F ⊗ M.A.F).left (Y3OrderMod.G 5)
  hKAA := kpAA M Q
  incAA g := Sigma.ι (fun _ : Y3OrderMod.G 5 => (M.A.F ⊗ M.A.F).left) g
  incAA_a g := Sigma.ι_desc _ g
  incAA_pr g := ι_actT (M.A.F ⊗ M.A.F).left g
  incAA_jointlyEpi u v h := Sigma.hom_ext u v h
  P3 := M.P3
  P3_sec := M.sec3
  P3_gen := M.gen3
  P3_inv g := (actionTot_P3 M g).symm

/-! ## 5. Discharged leaves -/

/-- Geometric fibres exist: take the base change. -/
theorem fecGeomFibre : FECGeomFibre :=
  fun _ A _ _ _ s => ⟨A.pullback s, FEC.pullback_fibre A s⟩

/-- The action map `∐ (_ : G), X ⟶ X` is etale: it is a coproduct of isomorphisms. -/
theorem etale_actS {X : Scheme.{0}} {G : Type} [Group G] (ρX : G →* Aut X) :
    AlgebraicGeometry.Etale (Y3QuotientDescent.actS ρX) := by
  haveI : IsZariskiLocalAtSource @AlgebraicGeometry.Etale := by
    first
      | exact inferInstance
      | exact HasRingHomProperty.instIsZariskiLocalAtSource (P := @AlgebraicGeometry.Etale)
  have hcomp : ∀ g : G, AlgebraicGeometry.Etale (ρX g).asIso.hom := fun g => by
    first
      | exact inferInstance
      | exact MorphismProperty.of_isIso (@AlgebraicGeometry.Etale) (ρX g).asIso.hom
  unfold Y3QuotientDescent.actS
  first
    | exact IsZariskiLocalAtSource.sigmaDesc (P := @AlgebraicGeometry.Etale) hcomp
    | exact IsZariskiLocalAtSource.sigmaDesc hcomp

/-- The quotient map is etale, by descent along itself: its base change along `qX` is the
action map from `∐ (_ : G 5), X`. -/
theorem etale_qX (M : Moduli35) (Q : QuotientData M) : AlgebraicGeometry.Etale Q.qX := by
  haveI := Q.finX
  haveI := Q.flatX
  haveI := Q.surjX
  have hq : FpqcQ Q.qX := ⟨⟨Q.surjX, Q.flatX⟩, inferInstance⟩
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := @AlgebraicGeometry.Etale)
    (Q := FpqcQ) Q.kpX hq (etale_actS (ρ M))

/-! ## 6. The packet -/

/-- The level-(5,3) frame scheme is locally noetherian: it is proper over `Z[1/30]`. -/
theorem isLocallyNoetherian_X35 (hB1 : BuzzardThm21Cor23V15') (hB25 : BuzzardFrameRepTorsor 5)
    (hB23 : BuzzardFrameRepNS 3) :
    IsLocallyNoetherian (moduli35 (moduli5 hB1 hB25) hB23).X.left := by
  haveI hZ30 : IsNoetherianRing Y3RouteA.Z30 := by
    first
      | exact inferInstance
      | exact IsLocalization.isNoetherianRing (Submonoid.powers (30 : ℤ)) Y3RouteA.Z30
          inferInstance
  have hZ : IsLocallyNoetherian Z30Base := by
    first
      | exact inferInstance
      | (unfold Z30Base; infer_instance)
  have hP : IsProper (moduli35 (moduli5 hB1 hB25) hB23).X.hom := isProper_X35 hB1 hB25 hB23
  have hL : LocallyOfFiniteType (moduli35 (moduli5 hB1 hB25) hB23).X.hom := by
    haveI := hP
    infer_instance
  first
    | exact @LocallyOfFiniteType.isLocallyNoetherian _ _
        (moduli35 (moduli5 hB1 hB25) hB23).X.hom hL hZ
    | exact @AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian _ _
        (moduli35 (moduli5 hB1 hB25) hB23).X.hom hL hZ
    | (haveI := hL
       haveI : IsLocallyNoetherian ((Functor.fromPUnit Z30Base).obj
          (moduli35 (moduli5 hB1 hB25) hB23).X.right) := hZ
       exact LocallyOfFiniteType.isLocallyNoetherian (moduli35 (moduli5 hB1 hB25) hB23).X.hom)

/-- A scheme proper over `Z[1/30]` is locally noetherian. -/
theorem isLocallyNoetherian_of_proper_Z30 (T : Over Z30Base) (h : IsProper T.hom) :
    IsLocallyNoetherian T.left := by
  haveI hZ30 : IsNoetherianRing Y3RouteA.Z30 := by
    first
      | exact inferInstance
      | exact IsLocalization.isNoetherianRing (Submonoid.powers (30 : ℤ)) Y3RouteA.Z30
          inferInstance
  have hZ : IsLocallyNoetherian Z30Base := by
    first
      | exact inferInstance
      | (unfold Z30Base; infer_instance)
  have hL : LocallyOfFiniteType T.hom := by
    haveI := h
    infer_instance
  first
    | exact @LocallyOfFiniteType.isLocallyNoetherian _ _ T.hom hL hZ
    | exact @AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian _ _ T.hom hL hZ
    | (haveI := hL
       haveI : IsLocallyNoetherian ((Functor.fromPUnit Z30Base).obj T.right) := hZ
       exact LocallyOfFiniteType.isLocallyNoetherian T.hom)

/-- The general descent statement B7(b) implies its finite etale form. -/
theorem descentSmoothRelDimFiniteEtale_of_general (h : DescentSmoothOfRelativeDimension) :
    SourceDescent.DescentSmoothRelDimFiniteEtale :=
  fun n X Y Z f q _ _ het hsurj hfq => h n X Y Z f q het hsurj hfq

/-- Frame representability without the torsor clause. -/
theorem frameRep_of_torsor {M : ℕ} (h : BuzzardFrameRepTorsor M) : BuzzardFrameRep M :=
  fun S A => by
    obtain ⟨Z, i, h1, h2, h3, h4, h5, -⟩ := h S A
    exact ⟨Z, i, h1, h2, h3, h4, h5⟩

/-- The descended structure map `b` is smooth of relative dimension 2. The map `qA` is the
base change of the etale surjection `qX`, so it is etale and surjective, and
`qA ≫ b = A.F.hom ≫ qX` is smooth of relative dimension `2 + 0`. B7(b) in its finite etale form
then applies: `qA` is also finite, as a base change of the finite `qX`. -/
theorem smooth_b_of_B7b (hB7b : SourceDescent.DescentSmoothRelDimFiniteEtale)
    {X Y : Scheme.{0}} (D : DescentInput X Y) (hY : IsLocallyNoetherian Y)
    (het : AlgebraicGeometry.Etale D.qX) :
    SmoothOfRelativeDimension 2 D.b := by
  have hetA : AlgebraicGeometry.Etale D.qA := by
    first
      | exact MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Etale) D.hpb.flip het
      | (haveI := het; infer_instance)
  have hsurA : AlgebraicGeometry.Surjective D.qA := by
    first
      | exact MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Surjective) D.hpb.flip
          D.surj
      | infer_instance
  have h0 : SmoothOfRelativeDimension 0 D.qX := by
    first
      | exact (AlgebraicGeometry.Etale.iff_smoothOfRelativeDimension_zero D.qX).1 het
      | (haveI := het; infer_instance)
  have hcomp : SmoothOfRelativeDimension (2 + 0) (D.A.F.hom ≫ D.qX) :=
    smoothOfRelativeDimension_comp (hf := D.A.smooth) (hg := h0) 2 0 _ _
  have hcomp2 : SmoothOfRelativeDimension 2 (D.A.F.hom ≫ D.qX) := by
    first
      | exact hcomp
      | simpa using hcomp
  have hcomp3 : SmoothOfRelativeDimension 2 (D.qA ≫ D.b) :=
    (congrArg (fun k => SmoothOfRelativeDimension 2 k) D.hpb.w).mpr hcomp2
  have hfinA : AlgebraicGeometry.IsFinite D.qA := by
    first
      | exact MorphismProperty.of_isPullback (P := @AlgebraicGeometry.IsFinite) D.hpb.flip
          D.finite
      | (haveI := D.finite; infer_instance)
  exact hB7b 2 _ _ _ D.qA D.b hY hfinA hetA hsurA hcomp3


/-- Generators of the full level-3 structure descend along finite surjective epimorphisms of
the parameter scheme. This is the case `M = 3` of `isGenDescentFinite`. -/
def IsGenDescentFin3 : Prop :=
  ∀ (S : Scheme.{0}) (A : FEC S) (T T' : Scheme.{0}) (f : T' ⟶ T) (P : T ⟶ A.F.left),
    AlgebraicGeometry.IsFinite f → AlgebraicGeometry.Surjective f → Epi f →
      IsGen 3 A (f ≫ P) → IsGen 3 A P

/-- The packet built from the leaves it uses. This is a construction (the packet is data). -/
def y3Packet_of_parts (hB1 : BuzzardThm21Cor23V15') (hB23 : BuzzardFrameRepNS 3)
    (hB25 : BuzzardFrameRepTorsor 5) (hB3 : SerreRigidityLevel3') (hB6 : ProjectiveFEC)
    (hB7b : SourceDescent.DescentSmoothRelDimFiniteEtale)
    (hCI : DescentClosedImmersion) (hT5 : TorsionRep 5)
    (hPM : ProperMonoIsClosedImmersion) (hP : ProperLocalOnBase)
    (hG : GeomConnLocalOnBase) (hD : IsGenDescentFin3)
    (hmul : ActionMulCompatLN) : Y3Packet := by
  let M : Moduli35 := moduli35 (moduli5 hB1 hB25) hB23
  let Q : QuotientData M := quotientDataOfLeaves hB1 hB25 hB23 hB3 fecGeomFibre hB6
  have hLN : IsLocallyNoetherian M.X.left := isLocallyNoetherian_X35 hB1 hB25 hB23
  let D : DescentInput M.X.left Q.Y := descentInputOf M Q (hmul M Q hLN)
  have hps : IsProper Q.YOver.hom ∧ SmoothOfRelativeDimension 1 Q.YOver.hom :=
    Y_proper_smooth hB1 hB25 hB23 hB3 fecGeomFibre hB6 hT5 hB7b hCI hPM (etale_qX M Q)
  have hYLN : IsLocallyNoetherian Q.Y := isLocallyNoetherian_of_proper_Z30 Q.YOver hps.1
  have hS : SmoothOfRelativeDimension 2 D.b := smooth_b_of_B7b hB7b D hYLN (etale_qX M Q)
  have hrep := rep3 hB25 Q D hP hS hG rfl rfl
    (fun d τ hτ => by
      obtain rfl := eq_of_heq hτ
      exact act_comp_eq (ρA M) Q.kpA d)
    HEq.rfl
  have hsec : D.descP3 ≫ (D.descFEC hP hS hG).F.hom = 𝟙 Q.YOver.left := D.descP3_sec
  have hgen : IsGen 3 (D.descFEC hP hS hG) D.descP3 := by
    have h1 : IsGen 3 (D.descFEC hP hS hG) (D.P3 ≫ D.qA) :=
      (isGen_iff_of_fibre (A := D.descFEC hP hS hG) (A' := D.A) (g := D.qX) (h := D.qA)
        D.hpb (fun a => (D.qA_iotaB a).symm)).1 D.P3_gen
    have h2 : IsGen 3 (D.descFEC hP hS hG) (D.qX ≫ D.descP3) :=
      (congrArg (fun P => IsGen 3 (D.descFEC hP hS hG) P) D.P3_qA).mp h1
    haveI : Epi D.qX := by
      first
        | exact inferInstance
        | exact epi_of_effectiveEpi D.qX
    exact hD _ (D.descFEC hP hS hG) _ _ D.qX D.descP3 D.finite D.surj inferInstance h2
  first
    | exact ⟨Q.YOver, D.descFEC hP hS hG, D.descP3, hsec, hgen, hps.1, hps.2, hrep⟩
    | (unfold Y3Packet; exact ⟨Q.YOver, D.descFEC hP hS hG, D.descP3, hsec, hgen, hps.1, hps.2, hrep⟩)
    | exact ⟨⟨Q.YOver, D.descFEC hP hS hG, D.descP3, hsec, hgen, hps.1, hps.2, hrep⟩⟩

/-- The packet built from the bundle of printed leaves. -/
def y3Packet_of_leaves (hL : Y3PrintedLeaves) (hT5 : TorsionRep 5)
    (hPM : ProperMonoIsClosedImmersion) (hP : ProperLocalOnBase)
    (hG : GeomConnLocalOnBase) (hD : IsGenDescentFin3)
    (hmul : ActionMulCompat) : Y3Packet := by
  obtain ⟨hB1, hB23, hB25, hB3, -, hB6, -, hB7b, -, -, hCI⟩ := hL
  exact y3Packet_of_parts hB1 (frameRepNS_of_rep (frameRep_of_torsor hB23)) hB25 hB3 hB6
    (descentSmoothRelDimFiniteEtale_of_general hB7b) hCI hT5 hPM hP hG hD
    (actionMulCompatLN_of hmul)

/-- The repository target `Y3RouteA.Y3FullThreeRepZ30`, from the leaves. The leaf
`ProperMonoIsClosedImmersion` is discharged by Mathlib (`properMonoIsClosedImmersion`). -/
theorem y3FullThreeRepZ30_of_leaves (hL : Y3PrintedLeaves) (hT5 : TorsionRep 5)
    (hP : ProperLocalOnBase) (hG : GeomConnLocalOnBase)
    (hD : IsGenDescentFin3) (hmul : ActionMulCompat) : Y3RouteA.Y3FullThreeRepZ30 :=
  y3FullThreeRepZ30_of_packet
    (y3Packet_of_leaves hL hT5 properMonoIsClosedImmersion hP hG hD hmul)

/-
Hypotheses of `y3Packet_of_leaves`, with intended citations.

* `hL : Y3PrintedLeaves`: B1', B2' at 3 and 5, B3', B4'', B6, B7(a) to B7(d); sources as
  in each leaf (Buzzard 1997, Thm 2.1, Cor. 2.3, Sec. 1; Milne; EGA II; Stacks tags 03GN,
  02KM, 05B5, 02KL, 02L6). B4'' and B7(a), B7(c) are not used here.
* `hT5 : TorsionRep 5`: Milne, Abelian Varieties (Storrs article), Sec. 20, Prop. 20.7.
* `hPM : ProperMonoIsClosedImmersion`: Stacks, Lemma 41.7.2, tag 04XV.
* `hP : ProperLocalOnBase`: Stacks, Descent, Lemma 35.23.16; Remark 02WH, item 17.
* Smoothness of relative dimension 2 of the descended curve: from B7(b) and etaleness of
  `qX` (`smooth_b_of_B7b`); no separate hypothesis.
* `hG : GeomConnLocalOnBase`: Stacks, Varieties, Section 33.7 (lemma number to be fixed).
* `hD : IsGenDescentFin3`: proved as `isGenDescentFinite` (cancellation of an epimorphism and
  lifting of geometric points through a finite surjective map).
* `hmul : ActionMulCompat`: each `actionTot M d` preserves the unit (`actionTot_oneL`) and is
  `O`-linear, hence is a homomorphism: Milne, Storrs article, Cor. 20.2(a) (this is B4''
  applied after identifying `A` with its base change along `actionMap M d`); the diagonal
  action is characterized by the cartesian square of the fibre-power map.

Discharged here: `FECGeomFibre` (base change), `Etale Q.qX` (descent of etaleness along
`qX`), the three kernel pairs of the descent input, and `act_one`, `act_inv`.
-/

end Y3Buzzard

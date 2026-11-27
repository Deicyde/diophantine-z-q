import ZInQKernel.Contrib.OneProof.BuzzardFrameRepTorsor5
import ZInQKernel.Contrib.OneProof.SerreRigidityZ30.Leaves

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV
open scoped CategoryTheory.Obj
namespace Y3Buzzard

/-!
# The level-three moduli target through rigidity on geometric fibres over `Z[1/30]`

The freeness of the action of `G 5` on the level-(5,3) moduli scheme `X` uses rigidity at level
three only on geometric fibres: for an algebraically closed field `k` and a point
`s : Spec k ⟶ X` fixed by `g_δ`, the restriction of the comparison map `h_δ` to the fibre of `A`
over `s` is an `O`-linear automorphism fixing the restricted level-3 generator, and rigidity says
that it fixes every point of the fibre. Since `X` lies over `Z[1/30]`, the composite
`Spec k ⟶ X ⟶ Z[1/30]` is a geometric point of `Z[1/30]`, so the fibre form
`SerreRigidityFibreZ30` applies there.

Each declaration below, with the suffix `_z30`, repeats the proof of its counterpart along the
chain from this fibre argument to `Y3RouteA.Y3FullThreeRepZ30`, with `SerreRigidityFibreZ30` in
place of `SerreRigidityLevel3'`.
-/

attribute [local instance] FEC.grp

/-! ## 1. Freeness of the action of `G 5` -/

section Free

variable (M : Moduli35)

/-- Rigidity on a fibre: `h_δ` fixes every point over a geometric point fixed by `g_δ`. The
geometric point lies over `Z[1/30]` through the structure map of the moduli scheme; the
hypotheses on the characteristic of `k` are not needed for the fibre form of rigidity. -/
theorem actionTot_fixes_fibre_z30 (hSR : SerreRigidityFibreZ30) (δ : Y3OrderMod.G 5) {k : Type}
    [Field k] [IsAlgClosed k] (_hc2 : ringChar k ≠ 2) (_hc3 : ringChar k ≠ 3)
    (s : Spec (CommRingCat.of k) ⟶ M.X.left) (hzs : s ≫ (actionMap M δ).left = s)
    (As : FEC (Spec (CommRingCat.of k))) (hs : As.F.left ⟶ M.A.F.left)
    (hpb : IsPullback hs As.F.hom M.A.F.hom s) (hι : ∀ a, As.iota a ≫ hs = hs ≫ M.A.iota a)
    (y : Spec (CommRingCat.of k) ⟶ M.A.F.left) (hy : y ≫ M.A.F.hom = s) :
    y ≫ actionTot M δ = y := by
  have hzs' := fix_inv M hzs
  obtain ⟨E, hE1, hE2⟩ := exists_fibreEndo hpb (actionTot M δ) _ (actionTot_w M δ) hzs
  obtain ⟨E', hE1', hE2'⟩ := exists_fibreEndo hpb (actionTot M δ⁻¹) _ (actionTot_w M δ⁻¹) hzs'
  have hEE' : E ≫ E' = 𝟙 _ := fibreEndo_comp_eq_id hpb
    (by rw [← actionTot_mul, inv_mul_cancel, actionTot_one]) hE1 hE2 hE1' hE2'
  have hE'E : E' ≫ E = 𝟙 _ := fibreEndo_comp_eq_id hpb
    (by rw [← actionTot_mul, mul_inv_cancel, actionTot_one]) hE1' hE2' hE1 hE2
  -- the restriction of `P3`
  have e3 : s ≫ M.P3 ≫ M.A.F.hom = s := by rw [M.sec3, Category.comp_id]
  have h3 : (s ≫ M.P3) ≫ M.A.F.hom = s := by rw [Category.assoc, e3]
  obtain ⟨P3s, hP1, hP2⟩ : ∃ P3s, P3s ≫ hs = s ≫ M.P3 ∧ P3s ≫ As.F.hom = 𝟙 _ :=
    ⟨hpb.lift (s ≫ M.P3) (𝟙 _) (by rw [h3, Category.id_comp]),
      hpb.lift_fst _ _ _, hpb.lift_snd _ _ _⟩
  let P3pt : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ As.F :=
    Over.homMk (U := Over.mk (𝟙 (Spec (CommRingCat.of k)))) P3s hP2
  have hG : IsGenAt 3 M.A s (Over.homMk (U := Over.mk s) (s ≫ M.P3) h3) :=
    (isGenAt_congr M.A e3 (s ≫ M.P3) (Category.assoc _ _ _) h3).1 (M.gen3.2 k s)
  have hPQ : (Over.homMk (U := Over.mk s) (s ≫ M.P3) h3 : Over.mk s ⟶ M.A.F) =
      fibreMap hpb (Category.id_comp s) P3pt :=
    Over.OverMorphism.ext hP1.symm
  have hgen3 : IsGenAt 3 As (𝟙 _) P3pt :=
    isGenAt_of_fibre_rev hpb hι (Category.id_comp s) (IsGenAt.of_eq hPQ hG)
  have hP3fix : (s ≫ M.P3) ≫ actionTot M δ = s ≫ M.P3 := by
    rw [Category.assoc, actionTot_P3, ← Category.assoc, hzs]
  have hP3s : P3s ≫ E = P3s := fibre_point_fixed hpb hE1 hE2 hP3fix hP1
  -- rigidity on the geometric fibre over `Z[1/30]`
  let θ : As.F ≅ As.F := isoOfInv E E' hE2 hE2' hEE' hE'E
  have hθι : ∀ a : O, As.iota a ≫ θ.hom.left = θ.hom.left ≫ As.iota a := fun a =>
    fibreEndo_iota hpb hι (actionTot_iota M δ) hE1 hE2 a
  have hfix3 : P3pt ≫ θ.hom = P3pt := Over.OverMorphism.ext hP3s
  have hθ := hSR k (s ≫ M.X.hom) As θ hθι P3pt hgen3 hfix3
  have hall : ∀ x : Spec (CommRingCat.of k) ⟶ As.F.left, x ≫ As.F.hom = 𝟙 _ → x ≫ E = x := by
    intro x hx
    have hl := congrArg (fun f => f.left)
      (hθ (Over.homMk (U := Over.mk (𝟙 (Spec (CommRingCat.of k)))) x hx))
    exact hl
  exact point_fixed_of_fibre hpb hE1 hall y hy

/-- No geometric point is fixed by `ρ δ` for `δ ≠ 1`. -/
theorem fixedPointFree_geom_z30 (hSR : SerreRigidityFibreZ30) (hBC : FECGeomFibre)
    {δ : Y3OrderMod.G 5} (hδ : δ ≠ 1) {T : Scheme.{0}} (z : T ⟶ M.X.left)
    (hz : z ≫ (ρ M δ).asIso.hom = z) (k : Type) [Field k] [IsAlgClosed k]
    (t : Spec (CommRingCat.of k) ⟶ T) : False := by
  apply hδ
  have hz' : z ≫ (actionMap M δ).left = z := hz
  have hzs : (t ≫ z) ≫ (actionMap M δ).left = t ≫ z := by rw [Category.assoc, hz']
  let φ := (ringHomOfSpec (t ≫ z ≫ M.X.hom)).hom
  have hc2 : ringChar k ≠ 2 := ringChar_ne_of_Z30 φ (by norm_num)
  have hc3 : ringChar k ≠ 3 := ringChar_ne_of_Z30 φ (by norm_num)
  obtain ⟨As, hAs⟩ := hBC M.X.left M.A k (t ≫ z)
  have hAs' : ∃ h, IsPullback h As.F.hom M.A.F.hom (t ≫ z) ∧
      ∀ a : O, As.iota a ≫ h = h ≫ M.A.iota a := hAs
  obtain ⟨hs, hpb, hι⟩ := hAs'
  have hy : ((t ≫ z) ≫ M.P5 ≫ M.A.iota (Y3OrderMod.σ δ)) ≫ M.A.F.hom = t ≫ z := by
    simp only [Category.assoc, M.A.iota_over, M.sec5, Category.comp_id]
  have hfixy := actionTot_fixes_fibre_z30 M hSR δ hc2 hc3 (t ≫ z) hzs As hs hpb hι _ hy
  have hP5 : (t ≫ z) ≫ M.P5 ≫ M.A.iota (Y3OrderMod.σ δ) = (t ≫ z) ≫ M.P5 := by
    calc (t ≫ z) ≫ M.P5 ≫ M.A.iota (Y3OrderMod.σ δ)
        = ((t ≫ z) ≫ M.P5 ≫ M.A.iota (Y3OrderMod.σ δ)) ≫ actionTot M δ := hfixy.symm
      _ = (t ≫ z) ≫ ((M.P5 ≫ M.A.iota (Y3OrderMod.σ δ)) ≫ actionTot M δ) :=
          Category.assoc _ _ _
      _ = (t ≫ z) ≫ ((actionMap M δ).left ≫ M.P5) := by rw [actionTot_P5]
      _ = ((t ≫ z) ≫ (actionMap M δ).left) ≫ M.P5 := (Category.assoc _ _ _).symm
      _ = (t ≫ z) ≫ M.P5 := by rw [hzs]
  exact eq_one_of_rel (rel_of_fixed_P5 M (t ≫ z) _ hP5)

/-- No nonempty scheme maps to a fixed locus of `ρ δ` for `δ ≠ 1`. -/
theorem fixedPointFree_z30 (hSR : SerreRigidityFibreZ30) (hBC : FECGeomFibre)
    {δ : Y3OrderMod.G 5} (hδ : δ ≠ 1) (T : Scheme.{0}) (z : T ⟶ M.X.left)
    (hz : z ≫ (ρ M δ).asIso.hom = z) : IsEmpty T := by
  by_contra hne
  obtain ⟨x⟩ := not_isEmpty_iff.mp hne
  exact fixedPointFree_geom_z30 M hSR hBC hδ z hz (AlgebraicClosure (T.residueField x))
    (Spec.map (CommRingCat.ofHom
        (algebraMap (T.residueField x) (AlgebraicClosure (T.residueField x)))) ≫
      T.fromSpecResidueField x)

/-- The freeness hypothesis in the shape used by the quotient step. -/
theorem hfix_z30 (hSR : SerreRigidityFibreZ30) (hBC : FECGeomFibre) :
    ∀ δ : Y3OrderMod.G 5, δ ≠ 1 → ∀ (T : Scheme.{0}) (z : T ⟶ M.X.left),
      z ≫ (ρ M δ).asIso.hom = z → IsEmpty T :=
  fun _ hδ T z hz => fixedPointFree_z30 M hSR hBC hδ T z hz

end Free

/-! ## 2. The quotient by `G 5` and its properness and smoothness -/

/-- The quotient data of the level-(5,3) datum built from the leaves. -/
def quotientDataOfLeaves_z30 (hB1 : BuzzardThm21Cor23V15') (hB25 : BuzzardFrameRepTorsor 5)
    (hB23 : BuzzardFrameRepNS 3) (hSR : SerreRigidityFibreZ30) (hBC : FECGeomFibre)
    (hB6 : ProjectiveFEC) : QuotientData (moduli35 (moduli5 hB1 hB25) hB23) :=
  quotientData _ (hfix_z30 _ hSR hBC) (fsa_X35 hB1 hB25 hB23) (fsa_A35 hB1 hB25 hB23 hB6)

/-- The quotient `Y` of the level-(5,3) moduli scheme by `G 5`, for the quotient datum built from
the leaves, is proper and smooth of relative dimension 1 over `Z[1/30]`. -/
theorem Y_proper_smooth_z30 (hB1 : BuzzardThm21Cor23V15') (hB25 : BuzzardFrameRepTorsor 5)
    (hB23 : BuzzardFrameRepNS 3) (hSR : SerreRigidityFibreZ30) (hBC : FECGeomFibre)
    (hB6 : ProjectiveFEC) (hT5 : TorsionRep 5)
    (hB7b : SourceDescent.DescentSmoothRelDimFiniteEtale)
    (hCI : DescentClosedImmersion) (hPM : ProperMonoIsClosedImmersion)
    (hEt : AlgebraicGeometry.Etale (quotientDataOfLeaves_z30 hB1 hB25 hB23 hSR hBC hB6).qX) :
    IsProper (quotientDataOfLeaves_z30 hB1 hB25 hB23 hSR hBC hB6).YOver.hom ∧
      SmoothOfRelativeDimension 1
        (quotientDataOfLeaves_z30 hB1 hB25 hB23 hSR hBC hB6).YOver.hom :=
  Y_proper_smooth_of hB1 hB25 hB23 hT5 hB7b hCI hPM _ hEt

/-! ## 3. The packet -/

/-- The packet built from the leaves it uses. This is a construction (the packet is data). -/
def y3Packet_of_parts_z30 (hB1 : BuzzardThm21Cor23V15') (hB23 : BuzzardFrameRepNS 3)
    (hB25 : BuzzardFrameRepTorsor 5) (hSR : SerreRigidityFibreZ30) (hB6 : ProjectiveFEC)
    (hB7b : SourceDescent.DescentSmoothRelDimFiniteEtale)
    (hCI : DescentClosedImmersion) (hT5 : TorsionRep 5)
    (hPM : ProperMonoIsClosedImmersion) (hP : ProperLocalOnBase)
    (hG : GeomConnLocalOnBase) (hD : IsGenDescentFin3)
    (hmul : ActionMulCompatLN) : Y3Packet := by
  let M : Moduli35 := moduli35 (moduli5 hB1 hB25) hB23
  let Q : QuotientData M := quotientDataOfLeaves_z30 hB1 hB25 hB23 hSR fecGeomFibre hB6
  have hLN : IsLocallyNoetherian M.X.left := isLocallyNoetherian_X35 hB1 hB25 hB23
  let D : DescentInput M.X.left Q.Y := descentInputOf M Q (hmul M Q hLN)
  have hps : IsProper Q.YOver.hom ∧ SmoothOfRelativeDimension 1 Q.YOver.hom :=
    Y_proper_smooth_z30 hB1 hB25 hB23 hSR fecGeomFibre hB6 hT5 hB7b hCI hPM (etale_qX M Q)
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
    have : Epi D.qX := inferInstance
    exact hD _ (D.descFEC hP hS hG) _ _ D.qX D.descP3 D.finite D.surj inferInstance h2
  exact ⟨Q.YOver, D.descFEC hP hS hG, D.descP3, hsec, hgen, hps.1, hps.2, hrep⟩

/-! ## 4. The level-three moduli target -/

/-- `Y3RouteA.Y3FullThreeRepZ30` from the printed leaves it uses. -/
theorem y3FullThreeRepZ30_of_printed_z30 (hB1 : BuzzardThm21Cor23V15')
    (hB23 : BuzzardFrameRepNS 3) (hB25 : BuzzardFrameRepTorsor 5)
    (hSR : SerreRigidityFibreZ30) (hB4 : ZeroPreservingIsHomLN) (hB6 : ProjectiveFEC)
    (hB7b : SourceDescent.DescentSmoothRelDimFiniteEtale)
    (hCI : DescentClosedImmersion) (hM : MilneProp207 5) (hP : ProperLocalOnBase) :
    Y3RouteA.Y3FullThreeRepZ30 :=
  y3FullThreeRepZ30_of_packet
    (y3Packet_of_parts_z30 hB1 hB23 hB25 hSR hB6 hB7b hCI (torsionRep5_of_milne hM)
      properMonoIsClosedImmersion hP geomConnLocalOnBase isGenDescentFin3
      (actionMulCompatLN_of_B4 hB4))

/-- `Y3RouteA.Y3FullThreeRepZ30` from the remaining printed leaves, with properness descent and
descent of closed immersions proved from flat descent. -/
theorem y3FullThreeRepZ30_of_printed_min_z30 (hB1 : BuzzardThm21Cor23V15')
    (hB23 : BuzzardFrameRepNS 3) (hB25 : BuzzardFrameRepTorsor 5)
    (hSR : SerreRigidityFibreZ30) (hB4 : ZeroPreservingIsHomLN) (hB6 : ProjectiveFEC)
    (hB7b : SourceDescent.DescentSmoothRelDimFiniteEtale) (hM : MilneProp207 5) :
    Y3RouteA.Y3FullThreeRepZ30 :=
  y3FullThreeRepZ30_of_printed_z30 hB1 hB23 hB25 hSR hB4 hB6 hB7b descentClosedImmersion hM
    properLocalOnBase

/-- `Y3RouteA.Y3FullThreeRepZ30` from eight printed inputs, with level-3 frames from Milne's
count of the 3-torsion (`GeomCard3`) and Milne, Prop. 20.7 at `n = 3`. -/
theorem y3FullThreeRepZ30_of_printed_min5_z30 (hB1 : BuzzardThm21Cor23V15')
    (hM3 : MilneProp207 3) (hC3 : GeomCard3) (hB25 : BuzzardFrameRepTorsor 5)
    (hSR : SerreRigidityFibreZ30) (hB4 : ZeroPreservingIsHomLN) (hB6 : ProjectiveFEC)
    (hM5 : MilneProp207 5) :
    Y3RouteA.Y3FullThreeRepZ30 :=
  y3FullThreeRepZ30_of_printed_min_z30 hB1 (frameRepNS3_of hM3 hC3 Y3OrderMod.card_OMod3) hB25
    hSR hB4 hB6 SourceDescent.h1StdEt_descentSmoothRelDimFiniteEtale hM5

/-- `Y3RouteA.Y3FullThreeRepZ30` from eight printed inputs, with Milne's count of the 5-torsion
(`GeomCard5`) in place of `BuzzardFrameRepTorsor 5`. -/
theorem y3FullThreeRepZ30_of_printed_milne5_z30 (hB1 : BuzzardThm21Cor23V15')
    (hM3 : MilneProp207 3) (hC3 : GeomCard3) (hC5 : GeomCard5)
    (hSR : SerreRigidityFibreZ30) (hB4 : ZeroPreservingIsHomLN) (hB6 : ProjectiveFEC)
    (hM5 : MilneProp207 5) :
    Y3RouteA.Y3FullThreeRepZ30 :=
  y3FullThreeRepZ30_of_printed_min5_z30 hB1 hM3 hC3 (buzzardFrameRepTorsor5_of_milne hM5 hC5) hSR
    hB4 hB6 hM5

/-- `Y3RouteA.Y3FullThreeRepZ30` from seven printed inputs: Milne's Remark 8.4 for every order
prime to the characteristic (`MilneRem84`) gives both counts `GeomCard3` and `GeomCard5`, and
rigidity at level three enters only on geometric fibres over `Z[1/30]`. -/
theorem y3FullThreeRepZ30_of_printed_rem84_z30 (hB1 : BuzzardThm21Cor23V15')
    (hM3 : MilneProp207 3) (hR : MilneRem84) (hSR : SerreRigidityFibreZ30)
    (hB4 : ZeroPreservingIsHomLN) (hB6 : ProjectiveFEC) (hM5 : MilneProp207 5) :
    Y3RouteA.Y3FullThreeRepZ30 :=
  y3FullThreeRepZ30_of_printed_milne5_z30 hB1 hM3 (geomCard3_of_rem84 hR) (geomCard5_of_rem84 hR)
    hSR hB4 hB6 hM5

end Y3Buzzard

import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.FrameModuli
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.FrameAction
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.Quotients
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.DescendedFamily
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.BuzzardLeaves2
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.FECPullback
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.QuotientDescent
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV
open scoped CategoryTheory.Obj
namespace Y3Buzzard

/-!
# The quotient `Y` represents level-3 structures (draft)

Data: the level-(5,3) moduli datum `M`, its quotient base `Y` by the free action `ρ M` of
`G 5`, and a false elliptic curve `E` over `Y` whose base change along `qX` is `M.A`
(through `qA`), together with a section `P3` of `E` descending `M.P3`.
For `E := descFEC` all of this is provided by `DescentInput` and `QuotientData`.

Existence (complete below): frame the given curve by the level-5 torsor of B2', classify
over the torsor, descend the classifying map and the comparison map along the torsor, and
descend the isomorphism property of the comparison with the pullback
(`MorphismProperty.of_isPullback_of_descendsAlong`, fpqc descent of isomorphisms).

Uniqueness: on `V = Z' ×_Y X` the frame of `M.A` is carried to `A'` through the two
cartesian squares; its torsor point and the projection give a map into the action relation;
on each piece of the resulting splitting (finitary extensivity) the two classifying maps
agree after `ρ δ`, by uniqueness in `Moduli35.rep`; `qX` is invariant, the pieces glue, and
`pT` and `q'` are cancelled as effective epimorphisms.
-/

attribute [local instance] FEC.grp

/-! ## 0. Generic helpers -/

@[reassoc]
theorem fec_iota_over {T : Scheme.{0}} (A : FEC T) (a : O) : A.iota a ≫ A.F.hom = A.F.hom :=
  A.iota_over a

@[reassoc]
theorem fec_pb_iota_fst {T T' : Scheme.{0}} (A : FEC T) (g : T' ⟶ T) (a : O) :
    (A.pullback g).iota a ≫ A.pullbackFst g = A.pullbackFst g ≫ A.iota a :=
  A.pullback_iota_fst g a

/-- A comparison map between two pullbacks of the same cospan is an isomorphism. -/
theorem isIso_of_isPullback_isPullback {C : Type*} [Category C] {P P' X Y Z : C}
    {f₁ : P ⟶ X} {s₁ : P ⟶ Y} {f₂ : P' ⟶ X} {s₂ : P' ⟶ Y} {b : X ⟶ Z} {g : Y ⟶ Z}
    (h₁ : IsPullback f₁ s₁ b g) (h₂ : IsPullback f₂ s₂ b g) (j : P ⟶ P')
    (hj₁ : j ≫ f₂ = f₁) (hj₂ : j ≫ s₂ = s₁) : IsIso j := by
  refine ⟨⟨h₁.lift f₂ s₂ h₂.w, ?_, ?_⟩⟩
  · apply h₁.hom_ext
    · rw [Category.assoc, h₁.lift_fst, hj₁, Category.id_comp]
    · rw [Category.assoc, h₁.lift_snd, hj₂, Category.id_comp]
  · apply h₂.hom_ext
    · rw [Category.assoc, hj₁, h₁.lift_fst, Category.id_comp]
    · rw [Category.assoc, hj₂, h₁.lift_snd, Category.id_comp]

/-- The fpqc class used for descent of isomorphisms. -/
abbrev FpqcQ : MorphismProperty Scheme.{0} :=
  @AlgebraicGeometry.Surjective ⊓ @AlgebraicGeometry.Flat ⊓ @AlgebraicGeometry.QuasiCompact

/-- A base change of a finite, flat, surjective map lies in `FpqcQ`. -/
theorem fpqcQ_of_isPullback {P B X Y : Scheme.{0}} {fst : P ⟶ B} {snd : P ⟶ X} {f : B ⟶ Y}
    {q : X ⟶ Y} [AlgebraicGeometry.IsFinite q] [AlgebraicGeometry.Flat q]
    [AlgebraicGeometry.Surjective q] (h : IsPullback fst snd f q) : FpqcQ fst := by
  haveI : AlgebraicGeometry.Flat fst :=
    MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Flat) h.flip inferInstance
  haveI : AlgebraicGeometry.Surjective fst :=
    MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Surjective) h.flip inferInstance
  haveI : AlgebraicGeometry.IsFinite fst :=
    MorphismProperty.of_isPullback (P := @AlgebraicGeometry.IsFinite) h.flip inferInstance
  haveI : AlgebraicGeometry.QuasiCompact fst := inferInstance
  exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩

/-- Descent of the isomorphism property along a base change of a finite, flat, surjective
map: if `j` is a base change of `c` along such a map and `j` is an isomorphism, so is `c`. -/
theorem isIso_of_descent {A X Y Z : Scheme.{0}} {j : A ⟶ X} {s : A ⟶ Y} {π : X ⟶ Z}
    {c : Y ⟶ Z} (sq : IsPullback j s π c) (hπ : FpqcQ π) (hj : IsIso j) : IsIso c := by
  have h : MorphismProperty.isomorphisms Scheme.{0} c :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := MorphismProperty.isomorphisms Scheme.{0})
      (Q := FpqcQ) sq hπ hj
  exact h

/-- The kernel pair of a base change of a torsor quotient map. -/
theorem kp_baseChange {Z S W V : Scheme.{0}} {G : Type} [Group G] [Finite G]
    (ρZ : G →* Aut Z) {q : Z ⟶ S}
    (hK : IsPullback (Y3QuotientDescent.actS ρZ) (Y3QuotientDescent.actT Z G) q q)
    {f₁ : W ⟶ V} {p₁ : W ⟶ Z} {k : V ⟶ S} (hpb : IsPullback f₁ p₁ k q) (τ : G → (W ⟶ W))
    (hτf : ∀ g, τ g ≫ f₁ = f₁) (hτp : ∀ g, τ g ≫ p₁ = p₁ ≫ (ρZ g).asIso.hom) :
    IsPullback (Sigma.desc τ) (Y3QuotientDescent.actT W G) f₁ f₁ := by
  have e1 : (Sigma.desc fun g : G => p₁ ≫ Sigma.ι (fun _ : G => Z) g) ≫
      Y3QuotientDescent.actS ρZ = Sigma.desc τ ≫ p₁ := by
    apply Sigma.hom_ext
    intro g
    simp only [Sigma.ι_desc_assoc, Category.assoc, ι_actS, hτp]
  have o2 : IsPullback (Sigma.desc τ ≫ p₁) (Y3QuotientDescent.actT W G) q (f₁ ≫ k) := by
    rw [← e1, hpb.w]
    exact (isPullback_sigmaDesc_actT (G := G) p₁).paste_horiz hK
  have hp : Sigma.desc τ ≫ f₁ = Y3QuotientDescent.actT W G ≫ f₁ := by
    apply Sigma.hom_ext
    intro g
    rw [Sigma.ι_desc_assoc, hτf, ← Category.assoc, ι_actT, Category.id_comp]
  exact IsPullback.of_right o2 hp hpb.flip

/-- A map out of a base change of a torsor quotient map descends once it is invariant. -/
def descBC {Z S W V T : Scheme.{0}} {G : Type} [Group G] [Finite G]
    (ρZ : G →* Aut Z) {q : Z ⟶ S} [AlgebraicGeometry.IsFinite q] [AlgebraicGeometry.Flat q]
    [AlgebraicGeometry.Surjective q]
    (hK : IsPullback (Y3QuotientDescent.actS ρZ) (Y3QuotientDescent.actT Z G) q q)
    {f₁ : W ⟶ V} {p₁ : W ⟶ Z} {k : V ⟶ S} (hpb : IsPullback f₁ p₁ k q) (τ : G → (W ⟶ W))
    (hτf : ∀ g, τ g ≫ f₁ = f₁) (hτp : ∀ g, τ g ≫ p₁ = p₁ ≫ (ρZ g).asIso.hom)
    (e : W ⟶ T) (he : ∀ g, τ g ≫ e = e) : V ⟶ T :=
  haveI : EffectiveEpi f₁ := effectiveEpi_of_isPullback hpb
  Y3QuotientDescent.descend (kp_baseChange ρZ hK hpb τ hτf hτp) e (by
    apply Sigma.hom_ext
    intro g
    rw [Sigma.ι_desc_assoc, he, ← Category.assoc, ι_actT, Category.id_comp])

theorem descBC_fac {Z S W V T : Scheme.{0}} {G : Type} [Group G] [Finite G]
    (ρZ : G →* Aut Z) {q : Z ⟶ S} [AlgebraicGeometry.IsFinite q] [AlgebraicGeometry.Flat q]
    [AlgebraicGeometry.Surjective q]
    (hK : IsPullback (Y3QuotientDescent.actS ρZ) (Y3QuotientDescent.actT Z G) q q)
    {f₁ : W ⟶ V} {p₁ : W ⟶ Z} {k : V ⟶ S} (hpb : IsPullback f₁ p₁ k q) (τ : G → (W ⟶ W))
    (hτf : ∀ g, τ g ≫ f₁ = f₁) (hτp : ∀ g, τ g ≫ p₁ = p₁ ≫ (ρZ g).asIso.hom)
    (e : W ⟶ T) (he : ∀ g, τ g ≫ e = e) :
    f₁ ≫ descBC ρZ hK hpb τ hτf hτp e he = e := by
  haveI : EffectiveEpi f₁ := effectiveEpi_of_isPullback hpb
  exact Y3QuotientDescent.descend_fac _ _ _

/-! ## 1. The input data -/

/-- A quotient of the level-(5,3) base with a descended curve and section. -/
structure RepData (M : Moduli35) where
  Y : Scheme.{0}
  sY : Y ⟶ Z30Base
  qX : M.X.left ⟶ Y
  hsY : qX ≫ sY = M.X.hom
  kpX : IsPullback (Y3QuotientDescent.actS (ρ M))
    (Y3QuotientDescent.actT M.X.left (Y3OrderMod.G 5)) qX qX
  finX : AlgebraicGeometry.IsFinite qX
  flatX : AlgebraicGeometry.Flat qX
  surjX : AlgebraicGeometry.Surjective qX
  E : FEC Y
  qA : M.A.F.left ⟶ E.F.left
  cart : IsPullback qA M.A.F.hom E.F.hom qX
  iota_qA : ∀ a : O, qA ≫ E.iota a = M.A.iota a ≫ qA
  inv_qA : ∀ δ : Y3OrderMod.G 5, actionTot M δ ≫ qA = qA
  P3 : Y ⟶ E.F.left
  P3_qA : M.P3 ≫ qA = qX ≫ P3

attribute [instance] RepData.finX RepData.flatX RepData.surjX

/-- The quotient base over `Z[1/30]`. -/
abbrev RepData.YOver {M : Moduli35} (R : RepData M) : Over Z30Base := Over.mk R.sY

/-- The data of B2' at `M = 5` for one curve. -/
structure Torsor5 {S : Scheme.{0}} (A' : FEC S) where
  Z : Scheme.{0}
  i : Z ⟶ A'.F.left
  fin : AlgebraicGeometry.IsFinite (i ≫ A'.F.hom)
  etale : AlgebraicGeometry.Etale (i ≫ A'.F.hom)
  surj : AlgebraicGeometry.Surjective (i ≫ A'.F.hom)
  char : FrameChar 5 A' i
  rho : Y3OrderMod.G 5 →* Aut Z
  hrho : ∀ δ : Y3OrderMod.G 5, (rho δ).asIso.hom ≫ i = i ≫ A'.iota (Y3OrderMod.σ δ)
  kp : IsPullback (Y3QuotientDescent.actS rho) (Y3QuotientDescent.actT Z (Y3OrderMod.G 5))
    (i ≫ A'.F.hom) (i ≫ A'.F.hom)

/-- Choice of the data of B2' at `M = 5`. -/
def Torsor5.ofLeaf (hB : BuzzardFrameRepTorsor 5) (S : Over Z30Base) (A' : FEC S.left) :
    Torsor5 A' := by
  choose Z i _ hfin het hsurj hchar rho hrho hkp using hB S A'
  exact ⟨Z, i, hfin, het, hsurj, hchar, rho, hrho, hkp⟩

theorem Torsor5.flat {S : Scheme.{0}} {A' : FEC S} (T : Torsor5 A') :
    AlgebraicGeometry.Flat (T.i ≫ A'.F.hom) := by
  haveI := T.etale
  first
    | infer_instance
    | exact (AlgebraicGeometry.Etale.iff_flat_and_formallyUnramified.1 T.etale).1

/-! ## 2. The context of the existence proof -/

/-- A level-3 structure on a curve over `S`, with a chosen level-5 torsor. -/
structure Ctx (S : Over Z30Base) (A' : FEC S.left) where
  T : Torsor5 A'
  P3' : S.left ⟶ A'.F.left
  hP3' : P3' ≫ A'.F.hom = 𝟙 S.left
  hg3 : IsGen 3 A' P3'

namespace Ctx

variable {S : Over Z30Base} {A' : FEC S.left} (C : Ctx S A')

/-- The torsor map `q' = i' ≫ A'.F.hom`. A plain definition, so that `simp` and `rw` do not
unfold it. -/
def q : C.T.Z ⟶ S.left := C.T.i ≫ A'.F.hom

instance finq : AlgebraicGeometry.IsFinite C.q := C.T.fin
instance flatq : AlgebraicGeometry.Flat C.q := C.T.flat
instance surjq : AlgebraicGeometry.Surjective C.q := C.T.surj

instance effEpi_q : EffectiveEpi C.q := effectiveEpi_of_isPullback (IsPullback.id_vert C.q)

/-! The same instances for the unfolded form, which is the one in `C.T.kp`. -/

instance finq' : AlgebraicGeometry.IsFinite (C.T.i ≫ A'.F.hom) := C.T.fin
instance flatq' : AlgebraicGeometry.Flat (C.T.i ≫ A'.F.hom) := C.T.flat
instance surjq' : AlgebraicGeometry.Surjective (C.T.i ≫ A'.F.hom) := C.T.surj

instance effEpi_q' : EffectiveEpi (C.T.i ≫ A'.F.hom) :=
  effectiveEpi_of_isPullback (IsPullback.id_vert (C.T.i ≫ A'.F.hom))

instance effEpi_fst : EffectiveEpi (A'.pullbackFst C.q) :=
  effectiveEpi_of_isPullback (A'.pullback_isPullback C.q)

/-- The torsor as an object over `Z[1/30]`. -/
abbrev ZO : Over Z30Base := Over.mk (C.q ≫ S.hom)

/-- The tautological 5-frame over the torsor. -/
def P5Z : C.T.Z ⟶ (A'.pullback C.q).F.left := A'.pointSection C.q C.T.i rfl

/-- The 3-frame pulled back to the torsor. -/
def P3Z : C.T.Z ⟶ (A'.pullback C.q).F.left := A'.pullbackSection C.q C.P3' C.hP3'

@[reassoc]
theorem P5Z_fst : C.P5Z ≫ A'.pullbackFst C.q = C.T.i := FEC.pointSection_fst _ _ _ _

@[reassoc]
theorem P5Z_sec : C.P5Z ≫ (A'.pullback C.q).F.hom = 𝟙 C.T.Z := FEC.pointSection_sec _ _ _ _

@[reassoc]
theorem P3Z_fst : C.P3Z ≫ A'.pullbackFst C.q = C.q ≫ C.P3' :=
  A'.pullbackSection_fst C.q C.P3' C.hP3'

@[reassoc]
theorem P3Z_sec : C.P3Z ≫ (A'.pullback C.q).F.hom = 𝟙 C.T.Z :=
  A'.pullbackSection_sec C.q C.P3' C.hP3'

theorem P5Z_gen : IsGen 5 (A'.pullback C.q) C.P5Z := by
  refine (isGen_iff_of_fibre (A'.pullback_isPullback C.q) (A'.pullback_iota_fst C.q)).2 ?_
  rw [C.P5Z_fst]
  exact (C.T.char C.T.Z C.T.i).1 ⟨𝟙 C.T.Z, Category.id_comp C.T.i⟩

theorem P3Z_gen : IsGen 3 (A'.pullback C.q) C.P3Z :=
  A'.isGen_pullbackSection C.q C.P3' C.hP3' C.hg3

theorem P5Zσ_sec (δ : Y3OrderMod.G 5) :
    (C.P5Z ≫ (A'.pullback C.q).iota (Y3OrderMod.σ δ)) ≫ (A'.pullback C.q).F.hom =
      𝟙 C.ZO.left := by
  rw [Category.assoc, fec_iota_over, C.P5Z_sec]
  all_goals rfl

theorem P5Zσ_gen (δ : Y3OrderMod.G 5) :
    IsGen 5 (A'.pullback C.q) (C.P5Z ≫ (A'.pullback C.q).iota (Y3OrderMod.σ δ)) := by
  obtain ⟨d, hd⟩ := Y3OrderMod.σ_inv_mul δ
  obtain ⟨d', hd'⟩ := Y3OrderMod.σ_mul_inv δ
  exact isGen_mul_unit C.P5Z_gen hd hd'

/-! ### Step 3: classification over the torsor -/

theorem cls (M : Moduli35) :
    ∃! g : C.ZO ⟶ M.X, ∃ h, FrameSq M (S := C.ZO) (A'.pullback C.q) C.P5Z C.P3Z g h :=
  rep' M (S := C.ZO) (A'.pullback C.q) C.P5Z C.P3Z C.P5Z_sec C.P3Z_sec C.P5Z_gen C.P3Z_gen

/-- The classifying map `g₁ : Z' ⟶ X₃₅`. -/
def g₁ (M : Moduli35) : C.ZO ⟶ M.X := Classical.choose (C.cls M).exists

/-- The comparison map `h₁` over `g₁`. -/
def h₁ (M : Moduli35) : (A'.pullback C.q).F.left ⟶ M.A.F.left :=
  Classical.choose (Classical.choose_spec (C.cls M).exists)

theorem sq₁ (M : Moduli35) :
    FrameSq M (S := C.ZO) (A'.pullback C.q) C.P5Z C.P3Z (C.g₁ M) (C.h₁ M) :=
  Classical.choose_spec (Classical.choose_spec (C.cls M).exists)

theorem sq₁_pb (M : Moduli35) :
    IsPullback (C.h₁ M) (A'.pullback C.q).F.hom M.A.F.hom (C.g₁ M).left := (C.sq₁ M).1

@[reassoc]
theorem sq₁_iota (M : Moduli35) (a : O) :
    (A'.pullback C.q).iota a ≫ C.h₁ M = C.h₁ M ≫ M.A.iota a := (C.sq₁ M).2.1 a

@[reassoc]
theorem sq₁_P5 (M : Moduli35) : C.P5Z ≫ C.h₁ M = (C.g₁ M).left ≫ M.P5 := (C.sq₁ M).2.2.1

@[reassoc]
theorem sq₁_P3 (M : Moduli35) : C.P3Z ≫ C.h₁ M = (C.g₁ M).left ≫ M.P3 := (C.sq₁ M).2.2.2

@[reassoc]
theorem h₁_w (M : Moduli35) :
    C.h₁ M ≫ M.A.F.hom = (A'.pullback C.q).F.hom ≫ (C.g₁ M).left := (C.sq₁_pb M).w

/-! ### Step 4: equivariance -/

@[reassoc]
theorem rr_q (δ : Y3OrderMod.G 5) : (C.T.rho δ).asIso.hom ≫ C.q = C.q := by
  show (C.T.rho δ).asIso.hom ≫ C.T.i ≫ A'.F.hom = C.T.i ≫ A'.F.hom
  rw [← Category.assoc, C.T.hrho δ, Category.assoc, fec_iota_over]

/-- The action of `δ` on the pulled-back curve, over `ρ' δ`. -/
def tau (δ : Y3OrderMod.G 5) : (A'.pullback C.q).F.left ⟶ (A'.pullback C.q).F.left :=
  (A'.pullback_isPullback C.q).lift (A'.pullbackFst C.q)
    ((A'.pullback C.q).F.hom ≫ (C.T.rho δ).asIso.hom)
    (by rw [Category.assoc, C.rr_q δ]; exact (A'.pullback_isPullback C.q).w)

@[reassoc]
theorem tau_fst (δ : Y3OrderMod.G 5) : C.tau δ ≫ A'.pullbackFst C.q = A'.pullbackFst C.q :=
  (A'.pullback_isPullback C.q).lift_fst _ _ _

@[reassoc]
theorem tau_snd (δ : Y3OrderMod.G 5) :
    C.tau δ ≫ (A'.pullback C.q).F.hom = (A'.pullback C.q).F.hom ≫ (C.T.rho δ).asIso.hom :=
  (A'.pullback_isPullback C.q).lift_snd _ _ _

theorem tau_pb (δ : Y3OrderMod.G 5) :
    IsPullback (C.tau δ) (A'.pullback C.q).F.hom (A'.pullback C.q).F.hom
      (C.T.rho δ).asIso.hom := by
  refine IsPullback.of_right ?_ (C.tau_snd δ) (A'.pullback_isPullback C.q)
  rw [C.tau_fst, C.rr_q]
  exact A'.pullback_isPullback C.q

@[reassoc]
theorem tau_iota (δ : Y3OrderMod.G 5) (a : O) :
    (A'.pullback C.q).iota a ≫ C.tau δ = C.tau δ ≫ (A'.pullback C.q).iota a := by
  apply (A'.pullback_isPullback C.q).hom_ext
  · simp only [Category.assoc, C.tau_fst, fec_pb_iota_fst, C.tau_fst_assoc]
  · simp only [Category.assoc, C.tau_snd, fec_iota_over_assoc, fec_iota_over, C.tau_snd]

theorem tau_P5 (δ : Y3OrderMod.G 5) :
    (C.P5Z ≫ (A'.pullback C.q).iota (Y3OrderMod.σ δ)) ≫ C.tau δ =
      (C.T.rho δ).asIso.hom ≫ C.P5Z := by
  apply (A'.pullback_isPullback C.q).hom_ext
  · simp only [Category.assoc, C.tau_fst, fec_pb_iota_fst, C.P5Z_fst_assoc, C.P5Z_fst]
    rw [C.T.hrho δ]
  · simp only [Category.assoc, C.tau_snd, fec_iota_over_assoc, C.P5Z_sec_assoc, C.P5Z_sec,
      Category.id_comp, Category.comp_id]

theorem tau_P3 (δ : Y3OrderMod.G 5) : C.P3Z ≫ C.tau δ = (C.T.rho δ).asIso.hom ≫ C.P3Z := by
  apply (A'.pullback_isPullback C.q).hom_ext
  · simp only [Category.assoc, C.tau_fst, C.P3Z_fst, C.rr_q_assoc]
  · simp only [Category.assoc, C.tau_snd, C.P3Z_sec_assoc, C.P3Z_sec, Category.id_comp,
      Category.comp_id]

/-- `ρ' δ` as an endomorphism over `Z[1/30]`. -/
def rrO (δ : Y3OrderMod.G 5) : C.ZO ⟶ C.ZO :=
  Over.homMk (U := C.ZO) (V := C.ZO) (C.T.rho δ).asIso.hom (by
    show (C.T.rho δ).asIso.hom ≫ C.q ≫ S.hom = C.q ≫ S.hom
    rw [C.rr_q_assoc])

theorem sqA (M : Moduli35) (δ : Y3OrderMod.G 5) :
    FrameSq M (S := C.ZO) (A'.pullback C.q)
      (C.P5Z ≫ (A'.pullback C.q).iota (Y3OrderMod.σ δ)) C.P3Z (C.rrO δ ≫ C.g₁ M)
      (C.tau δ ≫ C.h₁ M) := by
  refine ⟨(C.tau_pb δ).paste_horiz (C.sq₁_pb M), fun a => ?_, ?_, ?_⟩
  · rw [C.tau_iota_assoc, C.sq₁_iota, Category.assoc]
  · rw [← Category.assoc, C.tau_P5, Category.assoc, C.sq₁_P5]
    rfl
  · rw [← Category.assoc, C.tau_P3, Category.assoc, C.sq₁_P3]
    rfl

theorem sqB_P5 (M : Moduli35) (δ : Y3OrderMod.G 5) :
    (C.P5Z ≫ (A'.pullback C.q).iota (Y3OrderMod.σ δ)) ≫ C.h₁ M ≫ actionTot M δ =
      (C.g₁ M).left ≫ (actionMap M δ).left ≫ M.P5 := by
  calc (C.P5Z ≫ (A'.pullback C.q).iota (Y3OrderMod.σ δ)) ≫ C.h₁ M ≫ actionTot M δ
      = C.P5Z ≫ ((A'.pullback C.q).iota (Y3OrderMod.σ δ) ≫ C.h₁ M) ≫ actionTot M δ := by
        simp only [Category.assoc]
    _ = C.P5Z ≫ (C.h₁ M ≫ M.A.iota (Y3OrderMod.σ δ)) ≫ actionTot M δ := by rw [C.sq₁_iota]
    _ = (C.P5Z ≫ C.h₁ M) ≫ M.A.iota (Y3OrderMod.σ δ) ≫ actionTot M δ := by
        simp only [Category.assoc]
    _ = (C.g₁ M).left ≫ (M.P5 ≫ M.A.iota (Y3OrderMod.σ δ)) ≫ actionTot M δ := by
        rw [C.sq₁_P5]; simp only [Category.assoc]
    _ = (C.g₁ M).left ≫ (actionMap M δ).left ≫ M.P5 := by rw [actionTot_P5]

theorem sqB_P3 (M : Moduli35) (δ : Y3OrderMod.G 5) :
    C.P3Z ≫ C.h₁ M ≫ actionTot M δ = (C.g₁ M).left ≫ (actionMap M δ).left ≫ M.P3 := by
  rw [C.sq₁_P3_assoc, actionTot_P3]

theorem sqB (M : Moduli35) (δ : Y3OrderMod.G 5) :
    FrameSq M (S := C.ZO) (A'.pullback C.q)
      (C.P5Z ≫ (A'.pullback C.q).iota (Y3OrderMod.σ δ)) C.P3Z (C.g₁ M ≫ actionMap M δ)
      (C.h₁ M ≫ actionTot M δ) := by
  refine ⟨(C.sq₁_pb M).paste_horiz (actionSq_pb M δ), fun a => ?_, ?_, ?_⟩
  · rw [C.sq₁_iota_assoc, actionTot_iota, Category.assoc]
  · rw [C.sqB_P5, Over.comp_left, Category.assoc]
  · rw [C.sqB_P3, Over.comp_left, Category.assoc]

theorem equivar (M : Moduli35) (δ : Y3OrderMod.G 5) :
    C.rrO δ ≫ C.g₁ M = C.g₁ M ≫ actionMap M δ :=
  (rep' M (S := C.ZO) (A'.pullback C.q) _ C.P3Z (C.P5Zσ_sec δ) C.P3Z_sec (C.P5Zσ_gen δ)
    C.P3Z_gen).unique ⟨_, C.sqA M δ⟩ ⟨_, C.sqB M δ⟩

theorem equivar_left (M : Moduli35) (δ : Y3OrderMod.G 5) :
    (C.T.rho δ).asIso.hom ≫ (C.g₁ M).left = (C.g₁ M).left ≫ (actionMap M δ).left := by
  exact congrArg (fun f => f.left) (C.equivar M δ)

theorem tau_h₁ (M : Moduli35) (δ : Y3OrderMod.G 5) :
    C.tau δ ≫ C.h₁ M = C.h₁ M ≫ actionTot M δ := by
  have sA : FrameSq M (S := C.ZO) (A'.pullback C.q)
      (C.P5Z ≫ (A'.pullback C.q).iota (Y3OrderMod.σ δ)) C.P3Z (C.g₁ M ≫ actionMap M δ)
      (C.tau δ ≫ C.h₁ M) := by
    rw [← C.equivar M δ]
    exact C.sqA M δ
  exact huniq' M (S := C.ZO) (A'.pullback C.q) _ C.P3Z (C.P5Zσ_sec δ) C.P3Z_sec
    (C.P5Zσ_gen δ) C.P3Z_gen sA (C.sqB M δ)

/-! ### Step 5: the classifying map `g₀` -/

variable {M : Moduli35} (R : RepData M)

theorem g₁qX_inv (δ : Y3OrderMod.G 5) :
    (C.T.rho δ).asIso.hom ≫ (C.g₁ M).left ≫ R.qX = (C.g₁ M).left ≫ R.qX := by
  rw [← Category.assoc, C.equivar_left, Category.assoc, ← ρ_hom M δ, act_comp_eq (ρ M) R.kpX δ]

/-- The descended classifying map `S ⟶ Y`. -/
def g₀ : S.left ⟶ R.Y :=
  Y3QuotientDescent.descend C.T.kp ((C.g₁ M).left ≫ R.qX)
    (compat_of_invariant C.T.rho _ (C.g₁qX_inv R))

@[reassoc]
theorem g₀_fac : C.q ≫ C.g₀ R = (C.g₁ M).left ≫ R.qX :=
  Y3QuotientDescent.descend_fac _ _ _

theorem g₁_over : (C.g₁ M).left ≫ M.X.hom = C.q ≫ S.hom := Over.w (C.g₁ M)

theorem g₀_over : C.g₀ R ≫ R.sY = S.hom := by
  apply Y3QuotientDescent.eq_of_effectiveEpi C.q
  rw [C.g₀_fac_assoc, R.hsY, C.g₁_over]

/-- `g₀` as a map over `Z[1/30]`. -/
def g₀O : S ⟶ R.YOver := Over.homMk (V := R.YOver) (C.g₀ R) (C.g₀_over R)

/-! ### Step 6: the comparison map `h` -/

theorem e_inv (δ : Y3OrderMod.G 5) : C.tau δ ≫ C.h₁ M ≫ R.qA = C.h₁ M ≫ R.qA := by
  rw [← Category.assoc, C.tau_h₁, Category.assoc, R.inv_qA]

/-- The comparison map `A' ⟶ E`, descended from `h₁ ≫ qA`. -/
def hD : A'.F.left ⟶ R.E.F.left :=
  descBC C.T.rho C.T.kp (A'.pullback_isPullback C.q) C.tau C.tau_fst C.tau_snd
    (C.h₁ M ≫ R.qA) (C.e_inv R)

@[reassoc]
theorem hD_fac : A'.pullbackFst C.q ≫ C.hD R = C.h₁ M ≫ R.qA :=
  descBC_fac _ _ _ _ _ _ _ _

theorem hD_w : C.hD R ≫ R.E.F.hom = A'.F.hom ≫ C.g₀ R := by
  apply Y3QuotientDescent.eq_of_effectiveEpi (A'.pullbackFst C.q)
  calc A'.pullbackFst C.q ≫ C.hD R ≫ R.E.F.hom = C.h₁ M ≫ R.qA ≫ R.E.F.hom := by
        rw [C.hD_fac_assoc]
    _ = C.h₁ M ≫ M.A.F.hom ≫ R.qX := by rw [R.cart.w]
    _ = (A'.pullback C.q).F.hom ≫ (C.g₁ M).left ≫ R.qX := by rw [C.h₁_w_assoc]
    _ = (A'.pullback C.q).F.hom ≫ C.q ≫ C.g₀ R := by rw [C.g₀_fac]
    _ = A'.pullbackFst C.q ≫ A'.F.hom ≫ C.g₀ R := by
        rw [← Category.assoc (A'.pullback C.q).F.hom, ← (A'.pullback_isPullback C.q).w,
          Category.assoc]

/-! ### Step 7: cartesianness, by descent of an isomorphism -/

/-- The comparison map `A' ⟶ pullback b g₀`. -/
def cmp : A'.F.left ⟶ pullback R.E.F.hom (C.g₀ R) :=
  pullback.lift (C.hD R) A'.F.hom (C.hD_w R)

/-- The base change of the comparison along the pulled-back torsor map. -/
def jmp : (A'.pullback C.q).F.left ⟶ pullback (pullback.snd R.E.F.hom (C.g₀ R)) C.q :=
  pullback.lift (A'.pullbackFst C.q ≫ C.cmp R) (A'.pullback C.q).F.hom (by
    rw [Category.assoc, cmp, pullback.lift_snd]
    exact (A'.pullback_isPullback C.q).w)

theorem jmp_fst : C.jmp R ≫ pullback.fst _ _ = A'.pullbackFst C.q ≫ C.cmp R :=
  pullback.lift_fst _ _ _

theorem jmp_snd : C.jmp R ≫ pullback.snd _ _ = (A'.pullback C.q).F.hom :=
  pullback.lift_snd _ _ _

theorem sq_jmp :
    IsPullback (C.jmp R) (A'.pullbackFst C.q) (pullback.fst _ _) (C.cmp R) := by
  have s : IsPullback (A'.pullbackFst C.q) (C.jmp R ≫ pullback.snd _ _)
      (C.cmp R ≫ pullback.snd R.E.F.hom (C.g₀ R)) C.q := by
    rw [C.jmp_snd, cmp, pullback.lift_snd]
    exact A'.pullback_isPullback C.q
  exact (IsPullback.of_bot s (C.jmp_fst R).symm
    (IsPullback.of_hasPullback (pullback.snd R.E.F.hom (C.g₀ R)) C.q)).flip

theorem isIso_jmp : IsIso (C.jmp R) := by
  have h₁ : IsPullback (C.h₁ M ≫ R.qA) (A'.pullback C.q).F.hom R.E.F.hom (C.q ≫ C.g₀ R) := by
    rw [C.g₀_fac]
    exact (C.sq₁_pb M).paste_horiz R.cart
  have h₂ := (IsPullback.of_hasPullback (pullback.snd R.E.F.hom (C.g₀ R)) C.q).paste_horiz
    (IsPullback.of_hasPullback R.E.F.hom (C.g₀ R))
  refine isIso_of_isPullback_isPullback h₁ h₂ (C.jmp R) ?_ (C.jmp_snd R)
  rw [← Category.assoc, C.jmp_fst, Category.assoc, cmp, pullback.lift_fst, C.hD_fac]

theorem isIso_cmp : IsIso (C.cmp R) :=
  isIso_of_descent (C.sq_jmp R)
    (fpqcQ_of_isPullback (IsPullback.of_hasPullback (pullback.snd R.E.F.hom (C.g₀ R)) C.q))
    (C.isIso_jmp R)

theorem hD_pb : IsPullback (C.hD R) A'.F.hom R.E.F.hom (C.g₀ R) := by
  haveI := C.isIso_cmp R
  exact IsPullback.of_iso_pullback ⟨C.hD_w R⟩ (asIso (C.cmp R)) (pullback.lift_fst _ _ _)
    (pullback.lift_snd _ _ _)

/-! ### Step 8: `O`-compatibility and the section -/

theorem hD_iota (a : O) : A'.iota a ≫ C.hD R = C.hD R ≫ R.E.iota a := by
  apply Y3QuotientDescent.eq_of_effectiveEpi (A'.pullbackFst C.q)
  calc A'.pullbackFst C.q ≫ A'.iota a ≫ C.hD R
      = (A'.pullback C.q).iota a ≫ A'.pullbackFst C.q ≫ C.hD R := by
        rw [fec_pb_iota_fst_assoc]
    _ = ((A'.pullback C.q).iota a ≫ C.h₁ M) ≫ R.qA := by rw [C.hD_fac, Category.assoc]
    _ = C.h₁ M ≫ M.A.iota a ≫ R.qA := by rw [C.sq₁_iota, Category.assoc]
    _ = C.h₁ M ≫ R.qA ≫ R.E.iota a := by rw [R.iota_qA]
    _ = A'.pullbackFst C.q ≫ C.hD R ≫ R.E.iota a := by rw [C.hD_fac_assoc]

theorem hD_P3 : C.P3' ≫ C.hD R = C.g₀ R ≫ R.P3 := by
  apply Y3QuotientDescent.eq_of_effectiveEpi C.q
  calc C.q ≫ C.P3' ≫ C.hD R = C.P3Z ≫ A'.pullbackFst C.q ≫ C.hD R := by
        rw [C.P3Z_fst_assoc]
    _ = C.P3Z ≫ C.h₁ M ≫ R.qA := by rw [C.hD_fac]
    _ = (C.g₁ M).left ≫ M.P3 ≫ R.qA := by rw [C.sq₁_P3_assoc]
    _ = (C.g₁ M).left ≫ R.qX ≫ R.P3 := by rw [R.P3_qA]
    _ = C.q ≫ C.g₀ R ≫ R.P3 := by rw [C.g₀_fac_assoc]

/-- The existence half for one level-3 structure. -/
theorem exists_rep :
    ∃ h : A'.F.left ⟶ R.E.F.left, IsPullback h A'.F.hom R.E.F.hom (C.g₀O R).left ∧
      (∀ a : O, A'.iota a ≫ h = h ≫ R.E.iota a) ∧ C.P3' ≫ h = (C.g₀O R).left ≫ R.P3 :=
  ⟨C.hD R, C.hD_pb R, C.hD_iota R, C.hD_P3 R⟩

/-- Uniqueness reduces to the identity `g₁ ≫ qX = q' ≫ g.left`. -/
theorem eq_g₀O_of {g : S ⟶ R.YOver} (hg : (C.g₁ M).left ≫ R.qX = C.q ≫ g.left) :
    g = C.g₀O R := by
  apply Over.OverMorphism.ext
  show g.left = C.g₀ R
  apply Y3QuotientDescent.eq_of_effectiveEpi C.q
  rw [C.g₀_fac, hg]

end Ctx

/-- Existence half of `rep3`. -/
theorem rep3_exists (hB25 : BuzzardFrameRepTorsor 5) {M : Moduli35} (R : RepData M)
    (S : Over Z30Base) (A' : FEC S.left) (P3' : S.left ⟶ A'.F.left)
    (hP3' : P3' ≫ A'.F.hom = 𝟙 S.left) (hg3 : IsGen 3 A' P3') :
    ∃ g : S ⟶ R.YOver, ∃ h : A'.F.left ⟶ R.E.F.left,
      IsPullback h A'.F.hom R.E.F.hom g.left ∧ (∀ a : O, A'.iota a ≫ h = h ≫ R.E.iota a) ∧
      P3' ≫ h = g.left ≫ R.P3 :=
  let C : Ctx S A' := ⟨Torsor5.ofLeaf hB25 S A', P3', hP3', hg3⟩
  ⟨C.g₀O R, C.exists_rep R⟩

/-! ## 3. Uniqueness: generic ingredients -/

/-- Transfer of an `O`-compatible cartesian square through the quotient curve: a curve
`C` over `T` that is a base change of `M.A` along `x`, and a map `t` with `t ≫ g = x ≫ qX`,
give an `O`-compatible cartesian square from `C` to `A'` over `t`. -/
theorem transfer {M : Moduli35} (R : RepData M) {S T : Scheme.{0}} {A' : FEC S}
    {g : S ⟶ R.Y} {h : A'.F.left ⟶ R.E.F.left} (hh : IsPullback h A'.F.hom R.E.F.hom g)
    (hhι : ∀ a : O, A'.iota a ≫ h = h ≫ R.E.iota a) {C : FEC T} {x : T ⟶ M.X.left}
    {k : C.F.left ⟶ M.A.F.left} (hk : IsPullback k C.F.hom M.A.F.hom x)
    (hkι : ∀ a : O, C.iota a ≫ k = k ≫ M.A.iota a) (t : T ⟶ S) (ht : t ≫ g = x ≫ R.qX) :
    ∃ φ : C.F.left ⟶ A'.F.left, φ ≫ h = k ≫ R.qA ∧ φ ≫ A'.F.hom = C.F.hom ≫ t ∧
      IsPullback φ C.F.hom A'.F.hom t ∧ ∀ a : O, C.iota a ≫ φ = φ ≫ A'.iota a := by
  have hw : (k ≫ R.qA) ≫ R.E.F.hom = (C.F.hom ≫ t) ≫ g :=
    calc (k ≫ R.qA) ≫ R.E.F.hom = k ≫ (R.qA ≫ R.E.F.hom) := Category.assoc _ _ _
      _ = k ≫ (M.A.F.hom ≫ R.qX) := by rw [R.cart.w]
      _ = (k ≫ M.A.F.hom) ≫ R.qX := (Category.assoc _ _ _).symm
      _ = (C.F.hom ≫ x) ≫ R.qX := by rw [hk.w]
      _ = C.F.hom ≫ (x ≫ R.qX) := Category.assoc _ _ _
      _ = C.F.hom ≫ (t ≫ g) := by rw [ht]
      _ = (C.F.hom ≫ t) ≫ g := (Category.assoc _ _ _).symm
  obtain ⟨φ, hφ1, hφ2⟩ : ∃ φ : C.F.left ⟶ A'.F.left,
      φ ≫ h = k ≫ R.qA ∧ φ ≫ A'.F.hom = C.F.hom ≫ t :=
    ⟨hh.lift _ _ hw, hh.lift_fst _ _ _, hh.lift_snd _ _ _⟩
  refine ⟨φ, hφ1, hφ2, ?_, fun a => ?_⟩
  · refine IsPullback.of_right ?_ hφ2 hh
    rw [hφ1, ht]
    exact hk.paste_horiz R.cart
  · apply hh.hom_ext
    · calc (C.iota a ≫ φ) ≫ h = C.iota a ≫ (φ ≫ h) := Category.assoc _ _ _
        _ = C.iota a ≫ (k ≫ R.qA) := by rw [hφ1]
        _ = (C.iota a ≫ k) ≫ R.qA := (Category.assoc _ _ _).symm
        _ = (k ≫ M.A.iota a) ≫ R.qA := by rw [hkι]
        _ = k ≫ (M.A.iota a ≫ R.qA) := Category.assoc _ _ _
        _ = k ≫ (R.qA ≫ R.E.iota a) := by rw [R.iota_qA]
        _ = (k ≫ R.qA) ≫ R.E.iota a := (Category.assoc _ _ _).symm
        _ = (φ ≫ h) ≫ R.E.iota a := by rw [hφ1]
        _ = φ ≫ (h ≫ R.E.iota a) := Category.assoc _ _ _
        _ = φ ≫ (A'.iota a ≫ h) := by rw [hhι]
        _ = (φ ≫ A'.iota a) ≫ h := (Category.assoc _ _ _).symm
    · calc (C.iota a ≫ φ) ≫ A'.F.hom = C.iota a ≫ (φ ≫ A'.F.hom) := Category.assoc _ _ _
        _ = C.iota a ≫ (C.F.hom ≫ t) := by rw [hφ2]
        _ = (C.iota a ≫ C.F.hom) ≫ t := (Category.assoc _ _ _).symm
        _ = C.F.hom ≫ t := by rw [fec_iota_over]
        _ = φ ≫ A'.F.hom := hφ2.symm
        _ = φ ≫ (A'.iota a ≫ A'.F.hom) := by rw [fec_iota_over]
        _ = (φ ≫ A'.iota a) ≫ A'.F.hom := (Category.assoc _ _ _).symm

/-- Splitting a scheme mapping to the action relation: the pieces over the coproduct
injections are jointly epimorphic (finitary extensivity). -/
theorem jointEpi_pieces {G : Type} [Finite G] {Z V W : Scheme.{0}}
    (ℓ : V ⟶ ∐ fun _ : G => Z) (m₁ m₂ : V ⟶ W)
    (H : ∀ δ : G, pullback.fst ℓ (Sigma.ι (fun _ : G => Z) δ) ≫ m₁ =
      pullback.fst ℓ (Sigma.ι (fun _ : G => Z) δ) ≫ m₂) : m₁ = m₂ := by
  have e : (Sigma.desc fun δ : G => Sigma.ι (fun _ : G => Z) δ) = 𝟙 _ :=
    Sigma.hom_ext _ _ (fun δ => by rw [Sigma.ι_desc, Category.comp_id])
  have hπ : IsIso (Sigma.desc fun δ : G => Sigma.ι (fun _ : G => Z) δ) := by
    rw [e]
    infer_instance
  haveI := FinitaryPreExtensive.isIso_sigmaDesc_fst
    (fun δ : G => Sigma.ι (fun _ : G => Z) δ) ℓ hπ
  refine (cancel_epi (Sigma.desc fun δ : G => pullback.fst ℓ (Sigma.ι (fun _ : G => Z) δ))).1 ?_
  apply Sigma.hom_ext
  intro δ
  rw [Sigma.ι_desc_assoc, Sigma.ι_desc_assoc]
  exact H δ

/-- On a piece of the action relation, the second coordinate is the first moved by `δ`. -/
theorem piece_coords {G : Type} [Group G] {Z V W : Scheme.{0}} (ρZ : G →* Aut Z)
    (ℓ : V ⟶ ∐ fun _ : G => Z) (u : W ⟶ V) (f : W ⟶ Z) (δ : G)
    (c : u ≫ ℓ = f ≫ Sigma.ι (fun _ : G => Z) δ) :
    u ≫ ℓ ≫ Y3QuotientDescent.actT Z G = f ∧
      u ≫ ℓ ≫ Y3QuotientDescent.actS ρZ = f ≫ (ρZ δ).asIso.hom := by
  constructor
  · rw [← Category.assoc, c, Category.assoc, ι_actT, Category.comp_id]
  · rw [← Category.assoc, c, Category.assoc, ι_actS]

/-! ## 4. Uniqueness -/

/-- A second level-3 representation of the same structure. -/
structure Cand {M : Moduli35} (R : RepData M) {S : Over Z30Base} {A' : FEC S.left}
    (C : Ctx S A') where
  g : S ⟶ R.YOver
  h : A'.F.left ⟶ R.E.F.left
  pb : IsPullback h A'.F.hom R.E.F.hom g.left
  iota : ∀ a : O, A'.iota a ≫ h = h ≫ R.E.iota a
  sec : C.P3' ≫ h = g.left ≫ R.P3

namespace Cand

variable {M : Moduli35} {R : RepData M} {S : Over Z30Base} {A' : FEC S.left} {C : Ctx S A'}
  (K : Cand R C)

/-- The comparison scheme `V = Z' ×_Y X`. -/
abbrev V : Scheme.{0} := pullback (C.q ≫ K.g.left) R.qX

abbrev pT : K.V ⟶ C.T.Z := pullback.fst (C.q ≫ K.g.left) R.qX

abbrev pX : K.V ⟶ M.X.left := pullback.snd (C.q ≫ K.g.left) R.qX

theorem hV : IsPullback K.pT K.pX (C.q ≫ K.g.left) R.qX := IsPullback.of_hasPullback _ _

@[reassoc]
theorem hV_w : K.pT ≫ C.q ≫ K.g.left = K.pX ≫ R.qX := pullback.condition

/-- The 5-frame of `M.A` over `V`, carried to `A'` through the two cartesian squares. -/
def x₂ : K.V ⟶ A'.F.left :=
  K.pb.lift (K.pX ≫ M.P5 ≫ R.qA) (K.pT ≫ C.q) (by
    calc (K.pX ≫ M.P5 ≫ R.qA) ≫ R.E.F.hom = K.pX ≫ M.P5 ≫ (R.qA ≫ R.E.F.hom) := by
          simp only [Category.assoc]
      _ = K.pX ≫ (M.P5 ≫ M.A.F.hom) ≫ R.qX := by rw [R.cart.w]; simp only [Category.assoc]
      _ = K.pX ≫ R.qX := by rw [M.sec5, Category.id_comp]
      _ = K.pT ≫ C.q ≫ K.g.left := K.hV_w.symm
      _ = (K.pT ≫ C.q) ≫ K.g.left := (Category.assoc _ _ _).symm)

theorem x₂_h : K.x₂ ≫ K.h = K.pX ≫ M.P5 ≫ R.qA := K.pb.lift_fst _ _ _

theorem x₂_s : K.x₂ ≫ A'.F.hom = K.pT ≫ C.q := K.pb.lift_snd _ _ _

theorem x₂_gen : IsGen 5 A' K.x₂ := by
  refine (isGen_iff_of_fibre K.pb K.iota).2 ?_
  rw [K.x₂_h]
  exact isGen_comp K.pX (isGen_of_fibre R.cart (fun a => (R.iota_qA a).symm) M.gen5)

/-- The torsor point of the carried frame. -/
def z₂ : K.V ⟶ C.T.Z := Classical.choose ((C.T.char K.V K.x₂).2 K.x₂_gen)

theorem z₂_i : K.z₂ ≫ C.T.i = K.x₂ := Classical.choose_spec ((C.T.char K.V K.x₂).2 K.x₂_gen)

theorem z₂_q : K.z₂ ≫ C.q = K.pT ≫ C.q := by
  show K.z₂ ≫ C.T.i ≫ A'.F.hom = K.pT ≫ C.q
  rw [← Category.assoc, K.z₂_i, K.x₂_s]

/-- Gluing step: on one piece, `qX` kills the action. -/
theorem glue_piece {W : Scheme.{0}} (u : W ⟶ K.V) (δ : Y3OrderMod.G 5)
    (e : u ≫ K.pX = u ≫ K.pT ≫ (C.g₁ M).left ≫ (actionMap M δ).left) :
    u ≫ K.pT ≫ (C.g₁ M).left ≫ R.qX = u ≫ K.pX ≫ R.qX := by
  have hq : (actionMap M δ).left ≫ R.qX = R.qX := act_comp_eq (ρ M) R.kpX δ
  calc u ≫ K.pT ≫ (C.g₁ M).left ≫ R.qX
      = u ≫ K.pT ≫ (C.g₁ M).left ≫ ((actionMap M δ).left ≫ R.qX) := by rw [hq]
    _ = (u ≫ K.pT ≫ (C.g₁ M).left ≫ (actionMap M δ).left) ≫ R.qX := by
        simp only [Category.assoc]
    _ = (u ≫ K.pX) ≫ R.qX := by rw [← e]
    _ = u ≫ K.pX ≫ R.qX := Category.assoc _ _ _

/-- The per-piece classification: where the carried frame is the tautological frame moved
by `δ`, the map `pX` is `pT ≫ g₁ ≫ ρ δ`. -/
theorem piece_eq_of {W : Scheme.{0}} (u : W ⟶ K.V) (f : W ⟶ C.T.Z) (δ : Y3OrderMod.G 5)
    (hu1 : u ≫ K.pT = f) (hu2 : u ≫ K.z₂ = f ≫ (C.T.rho δ).asIso.hom) :
    u ≫ K.pX = u ≫ K.pT ≫ (C.g₁ M).left ≫ (actionMap M δ).left := by
  have hgw : K.g.left ≫ R.sY = S.hom := Over.w K.g
  have haw : (actionMap M δ).left ≫ M.X.hom = M.X.hom := Over.w (actionMap M δ)
  have wb : (u ≫ K.pT ≫ (C.g₁ M).left ≫ (actionMap M δ).left) ≫ M.X.hom =
      (u ≫ K.pX) ≫ M.X.hom :=
    calc (u ≫ K.pT ≫ (C.g₁ M).left ≫ (actionMap M δ).left) ≫ M.X.hom
        = u ≫ K.pT ≫ (C.g₁ M).left ≫ ((actionMap M δ).left ≫ M.X.hom) := by
          simp only [Category.assoc]
      _ = u ≫ K.pT ≫ ((C.g₁ M).left ≫ M.X.hom) := by rw [haw]
      _ = u ≫ K.pT ≫ C.q ≫ S.hom := by rw [C.g₁_over]
      _ = u ≫ (K.pT ≫ C.q ≫ K.g.left) ≫ R.sY := by rw [← hgw]; simp only [Category.assoc]
      _ = u ≫ (K.pX ≫ R.qX) ≫ R.sY := by rw [K.hV_w]
      _ = (u ≫ K.pX) ≫ (R.qX ≫ R.sY) := by simp only [Category.assoc]
      _ = (u ≫ K.pX) ≫ M.X.hom := by rw [R.hsY]
  -- transfer `M.A` pulled back along `u ≫ pX` to `A'`, then to the torsor curve
  have ht : ((u ≫ K.pT) ≫ C.q) ≫ K.g.left = (u ≫ K.pX) ≫ R.qX :=
    calc ((u ≫ K.pT) ≫ C.q) ≫ K.g.left = u ≫ (K.pT ≫ C.q ≫ K.g.left) := by
          simp only [Category.assoc]
      _ = u ≫ (K.pX ≫ R.qX) := by rw [K.hV_w]
      _ = (u ≫ K.pX) ≫ R.qX := (Category.assoc _ _ _).symm
  obtain ⟨φ, hφh, hφs, hφpb, hφι⟩ := transfer R K.pb K.iota
    (M.A.pullback_isPullback (u ≫ K.pX)) (M.A.pullback_iota_fst (u ≫ K.pX))
    ((u ≫ K.pT) ≫ C.q) ht
  obtain ⟨ψ, hψ1, hψ2, hψpb, hψι⟩ := up_fibre C.q hφpb hφι
  -- the two frames, pushed to the torsor curve
  have hP5φ : M.A.pullbackSection (u ≫ K.pX) M.P5 M.sec5 ≫ φ = u ≫ K.x₂ := by
    apply K.pb.hom_ext
    · calc (M.A.pullbackSection (u ≫ K.pX) M.P5 M.sec5 ≫ φ) ≫ K.h
          = M.A.pullbackSection (u ≫ K.pX) M.P5 M.sec5 ≫ (φ ≫ K.h) := Category.assoc _ _ _
        _ = M.A.pullbackSection (u ≫ K.pX) M.P5 M.sec5 ≫
              (M.A.pullbackFst (u ≫ K.pX) ≫ R.qA) := by rw [hφh]
        _ = (M.A.pullbackSection (u ≫ K.pX) M.P5 M.sec5 ≫ M.A.pullbackFst (u ≫ K.pX)) ≫
              R.qA := (Category.assoc _ _ _).symm
        _ = ((u ≫ K.pX) ≫ M.P5) ≫ R.qA := by rw [M.A.pullbackSection_fst]
        _ = u ≫ (K.x₂ ≫ K.h) := by rw [K.x₂_h]; simp only [Category.assoc]
        _ = (u ≫ K.x₂) ≫ K.h := (Category.assoc _ _ _).symm
    · calc (M.A.pullbackSection (u ≫ K.pX) M.P5 M.sec5 ≫ φ) ≫ A'.F.hom
          = M.A.pullbackSection (u ≫ K.pX) M.P5 M.sec5 ≫ (φ ≫ A'.F.hom) :=
            Category.assoc _ _ _
        _ = M.A.pullbackSection (u ≫ K.pX) M.P5 M.sec5 ≫
              ((M.A.pullback (u ≫ K.pX)).F.hom ≫ ((u ≫ K.pT) ≫ C.q)) := by rw [hφs]
        _ = (M.A.pullbackSection (u ≫ K.pX) M.P5 M.sec5 ≫ (M.A.pullback (u ≫ K.pX)).F.hom) ≫
              ((u ≫ K.pT) ≫ C.q) := (Category.assoc _ _ _).symm
        _ = (u ≫ K.pT) ≫ C.q := by rw [M.A.pullbackSection_sec, Category.id_comp]
        _ = u ≫ (K.x₂ ≫ A'.F.hom) := by rw [K.x₂_s]; simp only [Category.assoc]
        _ = (u ≫ K.x₂) ≫ A'.F.hom := (Category.assoc _ _ _).symm
  have hP3φ : M.A.pullbackSection (u ≫ K.pX) M.P3 M.sec3 ≫ φ = (u ≫ K.pT) ≫ C.q ≫ C.P3' := by
    apply K.pb.hom_ext
    · calc (M.A.pullbackSection (u ≫ K.pX) M.P3 M.sec3 ≫ φ) ≫ K.h
          = M.A.pullbackSection (u ≫ K.pX) M.P3 M.sec3 ≫ (φ ≫ K.h) := Category.assoc _ _ _
        _ = M.A.pullbackSection (u ≫ K.pX) M.P3 M.sec3 ≫
              (M.A.pullbackFst (u ≫ K.pX) ≫ R.qA) := by rw [hφh]
        _ = (M.A.pullbackSection (u ≫ K.pX) M.P3 M.sec3 ≫ M.A.pullbackFst (u ≫ K.pX)) ≫
              R.qA := (Category.assoc _ _ _).symm
        _ = ((u ≫ K.pX) ≫ M.P3) ≫ R.qA := by rw [M.A.pullbackSection_fst]
        _ = (u ≫ K.pX) ≫ (M.P3 ≫ R.qA) := Category.assoc _ _ _
        _ = (u ≫ K.pX) ≫ (R.qX ≫ R.P3) := by rw [R.P3_qA]
        _ = u ≫ (K.pX ≫ R.qX) ≫ R.P3 := by simp only [Category.assoc]
        _ = u ≫ (K.pT ≫ C.q ≫ K.g.left) ≫ R.P3 := by rw [K.hV_w]
        _ = (u ≫ K.pT) ≫ C.q ≫ (K.g.left ≫ R.P3) := by simp only [Category.assoc]
        _ = (u ≫ K.pT) ≫ C.q ≫ (C.P3' ≫ K.h) := by rw [K.sec]
        _ = ((u ≫ K.pT) ≫ C.q ≫ C.P3') ≫ K.h := by simp only [Category.assoc]
    · calc (M.A.pullbackSection (u ≫ K.pX) M.P3 M.sec3 ≫ φ) ≫ A'.F.hom
          = M.A.pullbackSection (u ≫ K.pX) M.P3 M.sec3 ≫ (φ ≫ A'.F.hom) :=
            Category.assoc _ _ _
        _ = M.A.pullbackSection (u ≫ K.pX) M.P3 M.sec3 ≫
              ((M.A.pullback (u ≫ K.pX)).F.hom ≫ ((u ≫ K.pT) ≫ C.q)) := by rw [hφs]
        _ = (M.A.pullbackSection (u ≫ K.pX) M.P3 M.sec3 ≫ (M.A.pullback (u ≫ K.pX)).F.hom) ≫
              ((u ≫ K.pT) ≫ C.q) := (Category.assoc _ _ _).symm
        _ = (u ≫ K.pT) ≫ C.q := by rw [M.A.pullbackSection_sec, Category.id_comp]
        _ = ((u ≫ K.pT) ≫ C.q) ≫ (C.P3' ≫ A'.F.hom) := by rw [C.hP3', Category.comp_id]
        _ = ((u ≫ K.pT) ≫ C.q ≫ C.P3') ≫ A'.F.hom := by simp only [Category.assoc]
  have hψP5 : M.A.pullbackSection (u ≫ K.pX) M.P5 M.sec5 ≫ ψ =
      f ≫ C.P5Z ≫ (A'.pullback C.q).iota (Y3OrderMod.σ δ) := by
    apply (A'.pullback_isPullback C.q).hom_ext
    · calc (M.A.pullbackSection (u ≫ K.pX) M.P5 M.sec5 ≫ ψ) ≫ A'.pullbackFst C.q
          = M.A.pullbackSection (u ≫ K.pX) M.P5 M.sec5 ≫ φ := by rw [Category.assoc, hψ1]
        _ = u ≫ K.x₂ := hP5φ
        _ = u ≫ K.z₂ ≫ C.T.i := by rw [K.z₂_i]
        _ = (u ≫ K.z₂) ≫ C.T.i := (Category.assoc _ _ _).symm
        _ = (f ≫ (C.T.rho δ).asIso.hom) ≫ C.T.i := by rw [hu2]
        _ = f ≫ C.T.i ≫ A'.iota (Y3OrderMod.σ δ) := by rw [Category.assoc, C.T.hrho δ]
        _ = f ≫ (C.P5Z ≫ A'.pullbackFst C.q) ≫ A'.iota (Y3OrderMod.σ δ) := by rw [C.P5Z_fst]
        _ = f ≫ C.P5Z ≫ (A'.pullbackFst C.q ≫ A'.iota (Y3OrderMod.σ δ)) := by
            simp only [Category.assoc]
        _ = f ≫ C.P5Z ≫ ((A'.pullback C.q).iota (Y3OrderMod.σ δ) ≫ A'.pullbackFst C.q) := by
            rw [fec_pb_iota_fst]
        _ = (f ≫ C.P5Z ≫ (A'.pullback C.q).iota (Y3OrderMod.σ δ)) ≫ A'.pullbackFst C.q := by
            simp only [Category.assoc]
    · calc (M.A.pullbackSection (u ≫ K.pX) M.P5 M.sec5 ≫ ψ) ≫ (A'.pullback C.q).F.hom
          = M.A.pullbackSection (u ≫ K.pX) M.P5 M.sec5 ≫
              ((M.A.pullback (u ≫ K.pX)).F.hom ≫ (u ≫ K.pT)) := by rw [Category.assoc, hψ2]
        _ = (M.A.pullbackSection (u ≫ K.pX) M.P5 M.sec5 ≫ (M.A.pullback (u ≫ K.pX)).F.hom) ≫
              (u ≫ K.pT) := (Category.assoc _ _ _).symm
        _ = f := by rw [M.A.pullbackSection_sec, Category.id_comp, hu1]
        _ = f ≫ C.P5Z ≫ (A'.pullback C.q).F.hom := by rw [C.P5Z_sec, Category.comp_id]
        _ = f ≫ C.P5Z ≫ ((A'.pullback C.q).iota (Y3OrderMod.σ δ) ≫
              (A'.pullback C.q).F.hom) := by rw [fec_iota_over]
        _ = (f ≫ C.P5Z ≫ (A'.pullback C.q).iota (Y3OrderMod.σ δ)) ≫
              (A'.pullback C.q).F.hom := by simp only [Category.assoc]
  have hψP3 : M.A.pullbackSection (u ≫ K.pX) M.P3 M.sec3 ≫ ψ = f ≫ C.P3Z := by
    apply (A'.pullback_isPullback C.q).hom_ext
    · calc (M.A.pullbackSection (u ≫ K.pX) M.P3 M.sec3 ≫ ψ) ≫ A'.pullbackFst C.q
          = M.A.pullbackSection (u ≫ K.pX) M.P3 M.sec3 ≫ φ := by rw [Category.assoc, hψ1]
        _ = (u ≫ K.pT) ≫ C.q ≫ C.P3' := hP3φ
        _ = f ≫ (C.P3Z ≫ A'.pullbackFst C.q) := by rw [hu1, C.P3Z_fst]
        _ = (f ≫ C.P3Z) ≫ A'.pullbackFst C.q := (Category.assoc _ _ _).symm
    · calc (M.A.pullbackSection (u ≫ K.pX) M.P3 M.sec3 ≫ ψ) ≫ (A'.pullback C.q).F.hom
          = M.A.pullbackSection (u ≫ K.pX) M.P3 M.sec3 ≫
              ((M.A.pullback (u ≫ K.pX)).F.hom ≫ (u ≫ K.pT)) := by rw [Category.assoc, hψ2]
        _ = (M.A.pullbackSection (u ≫ K.pX) M.P3 M.sec3 ≫ (M.A.pullback (u ≫ K.pX)).F.hom) ≫
              (u ≫ K.pT) := (Category.assoc _ _ _).symm
        _ = f := by rw [M.A.pullbackSection_sec, Category.id_comp, hu1]
        _ = (f ≫ C.P3Z) ≫ (A'.pullback C.q).F.hom := by
            rw [Category.assoc, C.P3Z_sec, Category.comp_id]
  -- the two frame squares over the piece
  have sqa : FrameSq M (S := Over.mk ((u ≫ K.pX) ≫ M.X.hom)) (M.A.pullback (u ≫ K.pX))
      (M.A.pullbackSection (u ≫ K.pX) M.P5 M.sec5) (M.A.pullbackSection (u ≫ K.pX) M.P3 M.sec3)
      (Over.homMk (U := Over.mk ((u ≫ K.pX) ≫ M.X.hom)) (V := M.X) (u ≫ K.pX) rfl)
      (M.A.pullbackFst (u ≫ K.pX)) :=
    ⟨M.A.pullback_isPullback (u ≫ K.pX), M.A.pullback_iota_fst (u ≫ K.pX),
      M.A.pullbackSection_fst (u ≫ K.pX) M.P5 M.sec5,
      M.A.pullbackSection_fst (u ≫ K.pX) M.P3 M.sec3⟩
  have hpbb : IsPullback (ψ ≫ C.h₁ M ≫ actionTot M δ) (M.A.pullback (u ≫ K.pX)).F.hom
      M.A.F.hom (u ≫ K.pT ≫ (C.g₁ M).left ≫ (actionMap M δ).left) := by
    have H := (hψpb.paste_horiz (C.sq₁_pb M)).paste_horiz (actionSq_pb M δ)
    have e1 : (ψ ≫ C.h₁ M) ≫ actionTot M δ = ψ ≫ C.h₁ M ≫ actionTot M δ :=
      Category.assoc _ _ _
    have e2 : ((u ≫ K.pT) ≫ (C.g₁ M).left) ≫ (actionMap M δ).left =
        u ≫ K.pT ≫ (C.g₁ M).left ≫ (actionMap M δ).left := by simp only [Category.assoc]
    rw [e1, e2] at H
    exact H
  have sqb : FrameSq M (S := Over.mk ((u ≫ K.pX) ≫ M.X.hom)) (M.A.pullback (u ≫ K.pX))
      (M.A.pullbackSection (u ≫ K.pX) M.P5 M.sec5) (M.A.pullbackSection (u ≫ K.pX) M.P3 M.sec3)
      (Over.homMk (U := Over.mk ((u ≫ K.pX) ≫ M.X.hom)) (V := M.X)
        (u ≫ K.pT ≫ (C.g₁ M).left ≫ (actionMap M δ).left) wb)
      (ψ ≫ C.h₁ M ≫ actionTot M δ) := by
    refine ⟨hpbb, fun a => ?_, ?_, ?_⟩
    · calc (M.A.pullback (u ≫ K.pX)).iota a ≫ ψ ≫ C.h₁ M ≫ actionTot M δ
          = ((M.A.pullback (u ≫ K.pX)).iota a ≫ ψ) ≫ C.h₁ M ≫ actionTot M δ :=
            (Category.assoc _ _ _).symm
        _ = (ψ ≫ (A'.pullback C.q).iota a) ≫ C.h₁ M ≫ actionTot M δ := by rw [hψι a]
        _ = ψ ≫ ((A'.pullback C.q).iota a ≫ C.h₁ M) ≫ actionTot M δ := by
            simp only [Category.assoc]
        _ = ψ ≫ (C.h₁ M ≫ M.A.iota a) ≫ actionTot M δ := by rw [C.sq₁_iota]
        _ = ψ ≫ C.h₁ M ≫ (M.A.iota a ≫ actionTot M δ) := by simp only [Category.assoc]
        _ = ψ ≫ C.h₁ M ≫ (actionTot M δ ≫ M.A.iota a) := by rw [actionTot_iota]
        _ = (ψ ≫ C.h₁ M ≫ actionTot M δ) ≫ M.A.iota a := by simp only [Category.assoc]
    · calc M.A.pullbackSection (u ≫ K.pX) M.P5 M.sec5 ≫ ψ ≫ C.h₁ M ≫ actionTot M δ
          = (M.A.pullbackSection (u ≫ K.pX) M.P5 M.sec5 ≫ ψ) ≫ C.h₁ M ≫ actionTot M δ :=
            (Category.assoc _ _ _).symm
        _ = (f ≫ C.P5Z ≫ (A'.pullback C.q).iota (Y3OrderMod.σ δ)) ≫ C.h₁ M ≫
              actionTot M δ := by rw [hψP5]
        _ = f ≫ ((C.P5Z ≫ (A'.pullback C.q).iota (Y3OrderMod.σ δ)) ≫ C.h₁ M ≫
              actionTot M δ) := by simp only [Category.assoc]
        _ = f ≫ ((C.g₁ M).left ≫ (actionMap M δ).left ≫ M.P5) := by rw [C.sqB_P5]
        _ = (u ≫ K.pT ≫ (C.g₁ M).left ≫ (actionMap M δ).left) ≫ M.P5 := by
            rw [← hu1]; simp only [Category.assoc]
    · calc M.A.pullbackSection (u ≫ K.pX) M.P3 M.sec3 ≫ ψ ≫ C.h₁ M ≫ actionTot M δ
          = (M.A.pullbackSection (u ≫ K.pX) M.P3 M.sec3 ≫ ψ) ≫ C.h₁ M ≫ actionTot M δ :=
            (Category.assoc _ _ _).symm
        _ = (f ≫ C.P3Z) ≫ C.h₁ M ≫ actionTot M δ := by rw [hψP3]
        _ = f ≫ (C.P3Z ≫ C.h₁ M ≫ actionTot M δ) := Category.assoc _ _ _
        _ = f ≫ ((C.g₁ M).left ≫ (actionMap M δ).left ≫ M.P3) := by rw [C.sqB_P3]
        _ = (u ≫ K.pT ≫ (C.g₁ M).left ≫ (actionMap M δ).left) ≫ M.P3 := by
            rw [← hu1]; simp only [Category.assoc]
  have hab := (rep' M (S := Over.mk ((u ≫ K.pX) ≫ M.X.hom)) (M.A.pullback (u ≫ K.pX))
    (M.A.pullbackSection (u ≫ K.pX) M.P5 M.sec5) (M.A.pullbackSection (u ≫ K.pX) M.P3 M.sec3)
    (M.A.pullbackSection_sec (u ≫ K.pX) M.P5 M.sec5)
    (M.A.pullbackSection_sec (u ≫ K.pX) M.P3 M.sec3)
    (M.A.isGen_pullbackSection (u ≫ K.pX) M.P5 M.sec5 M.gen5)
    (M.A.isGen_pullbackSection (u ≫ K.pX) M.P3 M.sec3 M.gen3)).unique ⟨_, sqa⟩ ⟨_, sqb⟩
  exact congrArg (fun f => f.left) hab

/-- The key identity `g₁ ≫ qX = q' ≫ g`. -/
theorem key : (C.g₁ M).left ≫ R.qX = C.q ≫ K.g.left := by
  have hglue : K.pT ≫ (C.g₁ M).left ≫ R.qX = K.pX ≫ R.qX := by
    apply jointEpi_pieces (C.T.kp.lift K.z₂ K.pT K.z₂_q)
    intro δ
    obtain ⟨h1, h2⟩ := piece_coords C.T.rho (C.T.kp.lift K.z₂ K.pT K.z₂_q)
      (pullback.fst (C.T.kp.lift K.z₂ K.pT K.z₂_q) (Sigma.ι (fun _ : Y3OrderMod.G 5 => C.T.Z) δ))
      (pullback.snd (C.T.kp.lift K.z₂ K.pT K.z₂_q) (Sigma.ι (fun _ : Y3OrderMod.G 5 => C.T.Z) δ)) δ pullback.condition
    have hu1 : pullback.fst (C.T.kp.lift K.z₂ K.pT K.z₂_q) (Sigma.ι (fun _ : Y3OrderMod.G 5 => C.T.Z) δ) ≫ K.pT =
        pullback.snd (C.T.kp.lift K.z₂ K.pT K.z₂_q) (Sigma.ι (fun _ : Y3OrderMod.G 5 => C.T.Z) δ) := by
      exact (congrArg (fun k => pullback.fst (C.T.kp.lift K.z₂ K.pT K.z₂_q) (Sigma.ι (fun _ : Y3OrderMod.G 5 => C.T.Z) δ) ≫ k)
        (C.T.kp.lift_snd K.z₂ K.pT K.z₂_q)).symm.trans h1
    have hu2 : pullback.fst (C.T.kp.lift K.z₂ K.pT K.z₂_q) (Sigma.ι (fun _ : Y3OrderMod.G 5 => C.T.Z) δ) ≫ K.z₂ =
        pullback.snd (C.T.kp.lift K.z₂ K.pT K.z₂_q) (Sigma.ι (fun _ : Y3OrderMod.G 5 => C.T.Z) δ) ≫
          (C.T.rho δ).asIso.hom := by
      exact (congrArg (fun k => pullback.fst (C.T.kp.lift K.z₂ K.pT K.z₂_q) (Sigma.ι (fun _ : Y3OrderMod.G 5 => C.T.Z) δ) ≫ k)
        (C.T.kp.lift_fst K.z₂ K.pT K.z₂_q)).symm.trans h2
    exact K.glue_piece _ δ (K.piece_eq_of _ _ δ hu1 hu2)
  haveI : EffectiveEpi K.pT := effectiveEpi_of_isPullback K.hV
  apply Y3QuotientDescent.eq_of_effectiveEpi K.pT
  rw [hglue, K.hV_w]

end Cand

theorem Ctx.unique_rep {M : Moduli35} (R : RepData M) {S : Over Z30Base} {A' : FEC S.left}
    (C : Ctx S A') (g : S ⟶ R.YOver) (h : A'.F.left ⟶ R.E.F.left)
    (hh : IsPullback h A'.F.hom R.E.F.hom g.left)
    (hhι : ∀ a : O, A'.iota a ≫ h = h ≫ R.E.iota a) (hhP : C.P3' ≫ h = g.left ≫ R.P3) :
    g = C.g₀O R :=
  C.eq_g₀O_of R (Cand.key (⟨g, h, hh, hhι, hhP⟩ : Cand R C))

/-! ## 5. Representability -/

/-- `Y` represents level-3 structures, for any `RepData`. -/
theorem rep3_of (hB25 : BuzzardFrameRepTorsor 5) {M : Moduli35} (R : RepData M) :
    ∀ (S : Over Z30Base) (A' : FEC S.left) (P3' : S.left ⟶ A'.F.left),
      P3' ≫ A'.F.hom = 𝟙 S.left → IsGen 3 A' P3' →
        ∃! g : S ⟶ R.YOver, ∃ h : A'.F.left ⟶ R.E.F.left,
          IsPullback h A'.F.hom R.E.F.hom g.left ∧
          (∀ a : O, A'.iota a ≫ h = h ≫ R.E.iota a) ∧ P3' ≫ h = g.left ≫ R.P3 := by
  intro S A' P3' hP3' hg3
  let C : Ctx S A' := ⟨Torsor5.ofLeaf hB25 S A', P3', hP3', hg3⟩
  refine ⟨C.g₀O R, C.exists_rep R, ?_⟩
  rintro g ⟨h, hh, hhι, hhP⟩
  exact C.unique_rep R g h hh hhι hhP

/-- `rep3_of` with the curve over `X₃₅` given up to an equality with `M.A`. -/
theorem rep3_gen (hB25 : BuzzardFrameRepTorsor 5) {M : Moduli35} (Y : Scheme.{0})
    (sY : Y ⟶ Z30Base) (qX : M.X.left ⟶ Y) (hsY : qX ≫ sY = M.X.hom)
    (kpX : IsPullback (Y3QuotientDescent.actS (ρ M))
      (Y3QuotientDescent.actT M.X.left (Y3OrderMod.G 5)) qX qX)
    [AlgebraicGeometry.IsFinite qX] [AlgebraicGeometry.Flat qX]
    [AlgebraicGeometry.Surjective qX] (E : FEC Y) (A : FEC M.X.left) (hA : A = M.A)
    (qA : A.F.left ⟶ E.F.left) (cart : IsPullback qA A.F.hom E.F.hom qX)
    (hι : ∀ a : O, qA ≫ E.iota a = A.iota a ≫ qA)
    (hinv : ∀ (δ : Y3OrderMod.G 5) (τ : A.F.left ⟶ A.F.left), HEq τ (actionTot M δ) →
      τ ≫ qA = qA)
    (P3A : M.X.left ⟶ A.F.left) (hP3 : HEq P3A M.P3) (P3d : Y ⟶ E.F.left)
    (hsec : P3A ≫ qA = qX ≫ P3d) :
    ∀ (S : Over Z30Base) (A' : FEC S.left) (P3' : S.left ⟶ A'.F.left),
      P3' ≫ A'.F.hom = 𝟙 S.left → IsGen 3 A' P3' →
        ∃! g : S ⟶ Over.mk sY, ∃ h : A'.F.left ⟶ E.F.left,
          IsPullback h A'.F.hom E.F.hom g.left ∧
          (∀ a : O, A'.iota a ≫ h = h ≫ E.iota a) ∧ P3' ≫ h = g.left ≫ P3d := by
  subst hA
  obtain rfl := eq_of_heq hP3
  exact rep3_of hB25 ⟨Y, sY, qX, hsY, kpX, inferInstance, inferInstance, inferInstance, E, qA,
    cart, hι, fun δ => hinv δ _ HEq.rfl, P3d, hsec⟩

/-- **G7.** The quotient `Y` represents level-3 structures, with universal curve the
descended curve `descFEC` and universal section `descP3`. -/
theorem rep3 (hB25 : BuzzardFrameRepTorsor 5) {M : Moduli35} (Q : QuotientData M)
    (D : DescentInput M.X.left Q.Y) (hP : ProperLocalOnBase)
    (hS : SmoothOfRelativeDimension 2 D.b)
    (hG : GeomConnLocalOnBase) (hDA : D.A = M.A) (hqX : D.qX = Q.qX)
    (hinv : ∀ (δ : Y3OrderMod.G 5) (τ : D.A.F.left ⟶ D.A.F.left), HEq τ (actionTot M δ) →
      τ ≫ D.qA = D.qA)
    (hP3 : HEq D.P3 M.P3) :
    ∀ (S : Over Z30Base) (A' : FEC S.left) (P3' : S.left ⟶ A'.F.left),
      P3' ≫ A'.F.hom = 𝟙 S.left → IsGen 3 A' P3' →
        ∃! g : S ⟶ Q.YOver, ∃ h : A'.F.left ⟶ (D.descFEC hP hS hG).F.left,
          IsPullback h A'.F.hom (D.descFEC hP hS hG).F.hom g.left ∧
          (∀ a : O, A'.iota a ≫ h = h ≫ (D.descFEC hP hS hG).iota a) ∧
          P3' ≫ h = g.left ≫ D.descP3 := by
  haveI := Q.finX
  haveI := Q.flatX
  haveI := Q.surjX
  have hcart : IsPullback D.qA D.A.F.hom (D.descFEC hP hS hG).F.hom Q.qX := by
    rw [← hqX]
    exact D.hpb
  have hsec : D.P3 ≫ D.qA = Q.qX ≫ D.descP3 := by
    rw [← hqX]
    exact D.P3_qA
  exact rep3_gen hB25 Q.Y Q.sY Q.qX Q.hsY Q.kpX (D.descFEC hP hS hG) D.A hDA D.qA hcart
    D.qA_iotaB hinv D.P3 hP3 D.descP3 hsec

end Y3Buzzard

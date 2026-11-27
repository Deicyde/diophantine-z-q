import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.BuzzardLeaves
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.BuzzardLeaves2
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.OrderMod
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.FrameRep3
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.FrameModuli
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.FrameAction
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.ActionRelation
import Mathlib

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV
open scoped CategoryTheory.Obj

namespace Y3Buzzard

/-!
# The frame scheme is a torsor under the units modulo `M`

From frame representability `BuzzardFrameRep M` (a closed subscheme `i : Z ⟶ A`, finite, étale
and surjective over the base `S`, whose points are exactly the generators of full level-`M`
structures) we prove the torsor clause `BuzzardFrameRepTorsor M`. No further hypothesis is used.

Write `q = i ≫ π : Z ⟶ S` and `G = (O / M O)ˣ`.

1. The action. For `g : G`, `P ↦ P ≫ ι(σ g)` preserves generators, because `σ g` is invertible
   modulo `M`. So `i ≫ ι(σ g)` lifts through `i`, uniquely because `i` is a monomorphism. On points
   killed by `M`, `ι(a)` only depends on `a` modulo `M`; with `σ g * σ h ≡ σ (g * h)` this makes
   the lifts an action.
2. Freeness. If `g` and `h` act in the same way on a family of frames over a nonempty scheme, then
   at a geometric point the generator `P` satisfies `P ≫ ι(σ g - σ h) = 0`, so `σ g ≡ σ h` modulo
   `M` by the first clause of `IsGenAt`.
3. Transitivity at geometric points. Two generators `P, P'` over the same geometric point satisfy
   `P = P' ≫ ι(a)` and `P' = P ≫ ι(b)` by the second clause of `IsGenAt`; the first clause gives
   `a b ≡ b a ≡ 1` modulo `M`, so `a` is a unit modulo `M` and `P = P' ≫ ι(σ [a])`.
4. The comparison map `c : ∐_g Z ⟶ Z ×_S Z`, `(g, z) ↦ (g z, z)`. Its `g`-component is the
   diagonal of `q` followed by the automorphism `g × 1` of `Z ×_S Z`. The diagonal of an étale
   map is an open immersion, so every component is an open immersion; the components have disjoint
   images by freeness, so `c` is an open immersion. By transitivity at geometric points `c` is
   surjective. A surjective open immersion is an isomorphism, and this is the kernel-pair square.
-/

namespace FrameTorsor

attribute [local instance] FEC.grp

/-! ## 1. Algebra of the `O`-action on torsion points -/

section Alg

variable {B : Scheme.{0}} (A : FEC B)

/-- On a point killed by `M`, `ι(a)` only depends on `a` modulo `M`. -/
theorem comp_iota_congr {M : ℕ} {U : Over B} (x : U ⟶ A.F)
    (hx : x ≫ (Over.homMk (A.iota (M : O)) (A.iota_over _) : A.F ⟶ A.F) = 1) {a b : O}
    (hab : (a : Y3OrderMod.OMod M) = (b : Y3OrderMod.OMod M)) :
    x ≫ (Over.homMk (A.iota a) (A.iota_over a) : A.F ⟶ A.F) =
      x ≫ (Over.homMk (A.iota b) (A.iota_over b) : A.F ⟶ A.F) := by
  obtain ⟨c, hc⟩ := Y3OrderMod.coe_eq_coe_iff.1 hab
  have ha : a = b + (M : O) * c := by rw [← hc]; abel
  subst ha
  rw [comp_iota_add, comp_iota_natCast_mul_eq_one A M x hx, _root_.mul_one]

/-- If `ι(a)` and `ι(b)` agree on a point, then `ι(a - b)` kills it. -/
theorem comp_iota_sub_eq_one {U : Over B} (x : U ⟶ A.F) {a b : O}
    (h : x ≫ (Over.homMk (A.iota a) (A.iota_over a) : A.F ⟶ A.F) =
      x ≫ (Over.homMk (A.iota b) (A.iota_over b) : A.F ⟶ A.F)) :
    x ≫ (Over.homMk (A.iota (a - b)) (A.iota_over _) : A.F ⟶ A.F) = 1 := by
  have e1 := comp_iota_add A x a (-b)
  have e2 := comp_iota_add A x b (-b)
  rw [h, ← e2, add_neg_cancel, iotaHom_zero, MonObj.comp_one] at e1
  rw [sub_eq_add_neg]
  exact e1

/-- On an `M`-torsion point of `A`, `ι(a)` only depends on `a` modulo `M`. -/
theorem tors_iota_congr {M : ℕ} {T : Scheme.{0}} (P : T ⟶ A.F.left)
    (hP : (Over.homMk (U := Over.mk (P ≫ A.F.hom)) P rfl : Over.mk (P ≫ A.F.hom) ⟶ A.F) ^ M = 1)
    {a b : O} (hab : (a : Y3OrderMod.OMod M) = (b : Y3OrderMod.OMod M)) :
    P ≫ A.iota a = P ≫ A.iota b :=
  congrArg (fun f : Over.mk (P ≫ A.F.hom) ⟶ A.F => f.left)
    (comp_iota_congr A _ ((comp_iotaHom_natCast A _ M).trans hP) hab)

end Alg

/-! ## 2. The action of the units modulo `M` on the frame scheme -/

section Action

variable {M : ℕ} {B : Scheme.{0}} {A : FEC B} {Z : Scheme.{0}} {i : Z ⟶ A.F.left}

/-- The inclusion of the frame scheme is a generator. -/
theorem isGen_i (hchar : FrameChar M A i) : IsGen M A i :=
  (hchar Z i).1 ⟨𝟙 Z, Category.id_comp i⟩

/-- `i ≫ ι(σ g)` is a generator, as `σ g` is invertible modulo `M`. -/
theorem isGen_i_σ (hchar : FrameChar M A i) (g : Y3OrderMod.G M) :
    IsGen M A (i ≫ A.iota (Y3OrderMod.σ g)) := by
  obtain ⟨d, hd⟩ := Y3OrderMod.σ_inv_mul g
  obtain ⟨d', hd'⟩ := Y3OrderMod.σ_mul_inv g
  exact isGen_mul_unit (isGen_i hchar) hd hd'

/-- The action of a unit `g` on the frame scheme: a lift of `i ≫ ι(σ g)` through `i`. -/
def frameActHom (hchar : FrameChar M A i) (g : Y3OrderMod.G M) : Z ⟶ Z :=
  Classical.choose ((hchar Z _).2 (isGen_i_σ hchar g))

theorem frameActHom_spec (hchar : FrameChar M A i) (g : Y3OrderMod.G M) :
    frameActHom hchar g ≫ i = i ≫ A.iota (Y3OrderMod.σ g) :=
  Classical.choose_spec ((hchar Z _).2 (isGen_i_σ hchar g))

/-- On the frame scheme, `ι(a)` only depends on `a` modulo `M`. -/
theorem i_iota_congr (hchar : FrameChar M A i) {a b : O}
    (hab : (a : Y3OrderMod.OMod M) = (b : Y3OrderMod.OMod M)) :
    i ≫ A.iota a = i ≫ A.iota b :=
  tors_iota_congr A i (isGen_i hchar).1 hab

theorem frameActHom_one [Mono i] (hchar : FrameChar M A i) : frameActHom hchar 1 = 𝟙 Z := by
  apply (cancel_mono i).1
  rw [frameActHom_spec, Category.id_comp]
  obtain ⟨c, hc⟩ := Y3OrderMod.σ_one (M := M)
  rw [i_iota_congr hchar (b := 1) (Y3OrderMod.coe_eq_coe_iff.2 ⟨c, hc⟩), A.iota_one,
    Category.comp_id]

/-- The action law, in the composition order of `Aut`. -/
theorem frameActHom_mul [Mono i] (hchar : FrameChar M A i) (g h : Y3OrderMod.G M) :
    frameActHom hchar (g * h) = frameActHom hchar h ≫ frameActHom hchar g := by
  apply (cancel_mono i).1
  calc frameActHom hchar (g * h) ≫ i = i ≫ A.iota (Y3OrderMod.σ (g * h)) :=
        frameActHom_spec hchar _
    _ = i ≫ A.iota (Y3OrderMod.σ g * Y3OrderMod.σ h) :=
        i_iota_congr hchar (Y3OrderMod.coe_eq_coe_iff.2 (Y3OrderMod.σ_mul g h)).symm
    _ = (i ≫ A.iota (Y3OrderMod.σ h)) ≫ A.iota (Y3OrderMod.σ g) := by
        rw [A.iota_mul, Category.assoc]
    _ = frameActHom hchar h ≫ (i ≫ A.iota (Y3OrderMod.σ g)) := by
        rw [← frameActHom_spec hchar h]; exact Category.assoc _ _ _
    _ = (frameActHom hchar h ≫ frameActHom hchar g) ≫ i := by
        rw [← frameActHom_spec hchar g]; exact (Category.assoc _ _ _).symm

/-- The action `ρ : G M →* Aut Z`. -/
def frameAct [Mono i] (hchar : FrameChar M A i) : Y3OrderMod.G M →* Aut Z :=
  autOfAntiHom (frameActHom hchar) (frameActHom_one hchar) (frameActHom_mul hchar)

theorem frameAct_hom [Mono i] (hchar : FrameChar M A i) (g : Y3OrderMod.G M) :
    (frameAct hchar g).asIso.hom = frameActHom hchar g := rfl

theorem frameActHom_isIso [Mono i] (hchar : FrameChar M A i) (g : Y3OrderMod.G M) :
    IsIso (frameActHom hchar g) :=
  ⟨⟨frameActHom hchar g⁻¹,
    by rw [← frameActHom_mul, inv_mul_cancel, frameActHom_one],
    by rw [← frameActHom_mul, mul_inv_cancel, frameActHom_one]⟩⟩

/-- The action is over the base. -/
theorem frameActHom_q (hchar : FrameChar M A i) (g : Y3OrderMod.G M) :
    frameActHom hchar g ≫ i ≫ A.F.hom = i ≫ A.F.hom := by
  rw [← Category.assoc, frameActHom_spec, Category.assoc, A.iota_over]

end Action

/-! ## 3. Freeness and transitivity at geometric points, and the comparison map -/

section Geom

variable {M : ℕ} {B : Scheme.{0}} {A : FEC B} {Z : Scheme.{0}} {i : Z ⟶ A.F.left}

/-- Freeness: if `g` and `h` act in the same way on a family of frames over a scheme with a
point, then `g = h`. -/
theorem eq_of_frameActHom_eq (hchar : FrameChar M A i) {T : Scheme.{0}} (z : T ⟶ Z) (t : T)
    {g h : Y3OrderMod.G M} (hz : z ≫ frameActHom hchar g = z ≫ frameActHom hchar h) :
    g = h := by
  have hgen := (isGen_i hchar).2 (geomK t) (geomPt t ≫ z)
  set x : Over.mk ((geomPt t ≫ z) ≫ i ≫ A.F.hom) ⟶ A.F :=
    Over.homMk (U := Over.mk ((geomPt t ≫ z) ≫ i ≫ A.F.hom)) ((geomPt t ≫ z) ≫ i)
      (Category.assoc _ _ _)
  have hxy : x ≫ (Over.homMk (A.iota (Y3OrderMod.σ g)) (A.iota_over _) : A.F ⟶ A.F) =
      x ≫ (Over.homMk (A.iota (Y3OrderMod.σ h)) (A.iota_over _) : A.F ⟶ A.F) := by
    apply Over.OverMorphism.ext
    show ((geomPt t ≫ z) ≫ i) ≫ A.iota (Y3OrderMod.σ g) =
      ((geomPt t ≫ z) ≫ i) ≫ A.iota (Y3OrderMod.σ h)
    simp only [Category.assoc]
    rw [← frameActHom_spec hchar g, ← frameActHom_spec hchar h, reassoc_of% hz]
  obtain ⟨b, hb⟩ := (hgen.1 _).1 (comp_iota_sub_eq_one A x hxy)
  have e := (Y3OrderMod.coe_eq_coe_iff (M := M)).2 ⟨b, hb⟩
  rw [Y3OrderMod.σ_spec, Y3OrderMod.σ_spec] at e
  exact Units.ext e

/-- Transitivity at geometric points: two frames over the same geometric point of the base
differ by a unit modulo `M`. -/
theorem exists_frameActHom [Mono i] (hchar : FrameChar M A i) {k : Type} [Field k]
    [IsAlgClosed k] (u v : Spec (CommRingCat.of k) ⟶ Z)
    (huv : u ≫ i ≫ A.F.hom = v ≫ i ≫ A.F.hom) :
    ∃ g : Y3OrderMod.G M, u = v ≫ frameActHom hchar g := by
  have hu := (isGen_i hchar).2 k u
  have hv := (isGen_i hchar).2 k v
  have h₂ : (u ≫ i) ≫ A.F.hom = v ≫ i ≫ A.F.hom := (Category.assoc _ _ _).trans huv
  have hu' := (isGenAt_congr (M := M) A huv (u ≫ i) (Category.assoc _ _ _) h₂).1 hu
  set X : Over.mk (v ≫ i ≫ A.F.hom) ⟶ A.F :=
    Over.homMk (U := Over.mk (v ≫ i ≫ A.F.hom)) (u ≫ i) h₂
  set Y : Over.mk (v ≫ i ≫ A.F.hom) ⟶ A.F :=
    Over.homMk (U := Over.mk (v ≫ i ≫ A.F.hom)) (v ≫ i) (Category.assoc _ _ _)
  have hXM : X ≫ (Over.homMk (A.iota (M : O)) (A.iota_over _) : A.F ⟶ A.F) = 1 :=
    (hu'.1 _).2 ⟨1, (_root_.mul_one _).symm⟩
  have hYM : Y ≫ (Over.homMk (A.iota (M : O)) (A.iota_over _) : A.F ⟶ A.F) = 1 :=
    (hv.1 _).2 ⟨1, (_root_.mul_one _).symm⟩
  obtain ⟨a, ha⟩ := hv.2 X ((comp_iotaHom_natCast A X M).symm.trans hXM)
  obtain ⟨b, hb⟩ := hu'.2 Y ((comp_iotaHom_natCast A Y M).symm.trans hYM)
  have hba : Y ≫ (Over.homMk (A.iota (b * a)) (A.iota_over _) : A.F ⟶ A.F) =
      Y ≫ (Over.homMk (A.iota 1) (A.iota_over _) : A.F ⟶ A.F) := by
    rw [iotaHom_one, Category.comp_id, ← comp_iota_comp_iota, ← ha, ← hb]
  have hab : X ≫ (Over.homMk (A.iota (a * b)) (A.iota_over _) : A.F ⟶ A.F) =
      X ≫ (Over.homMk (A.iota 1) (A.iota_over _) : A.F ⟶ A.F) := by
    rw [iotaHom_one, Category.comp_id, ← comp_iota_comp_iota, ← hb, ← ha]
  obtain ⟨d, hd⟩ := (hv.1 _).1 (comp_iota_sub_eq_one A Y hba)
  obtain ⟨d', hd'⟩ := (hu'.1 _).1 (comp_iota_sub_eq_one A X hab)
  have e1 := (Y3OrderMod.coe_eq_coe_iff (M := M) (x := a * b) (y := 1)).2 ⟨d', hd'⟩
  have e2 := (Y3OrderMod.coe_eq_coe_iff (M := M) (x := b * a) (y := 1)).2 ⟨d, hd⟩
  rw [RingCon.coe_mul, RingCon.coe_one] at e1 e2
  let g : Y3OrderMod.G M := ⟨(a : Y3OrderMod.OMod M), (b : Y3OrderMod.OMod M), e1, e2⟩
  refine ⟨g, ?_⟩
  have hag : ((a : O) : Y3OrderMod.OMod M) = ((Y3OrderMod.σ g : O) : Y3OrderMod.OMod M) :=
    (Y3OrderMod.σ_spec g).symm
  have hX' : X = Y ≫ (Over.homMk (A.iota (Y3OrderMod.σ g)) (A.iota_over _) : A.F ⟶ A.F) :=
    ha.trans (comp_iota_congr A Y hYM hag)
  have hl : u ≫ i = (v ≫ i) ≫ A.iota (Y3OrderMod.σ g) :=
    congrArg (fun f : Over.mk (v ≫ i ≫ A.F.hom) ⟶ A.F => f.left) hX'
  apply (cancel_mono i).1
  rw [hl]
  simp only [Category.assoc, frameActHom_spec]

/-- The `g`-component `z ↦ (g z, z)` of the comparison map to the kernel pair of `q`. -/
def cmpComp (hchar : FrameChar M A i) (g : Y3OrderMod.G M) :
    Z ⟶ pullback (i ≫ A.F.hom) (i ≫ A.F.hom) :=
  pullback.lift (frameActHom hchar g) (𝟙 Z) (by rw [frameActHom_q, Category.id_comp])

theorem cmpComp_fst (hchar : FrameChar M A i) (g : Y3OrderMod.G M) :
    cmpComp hchar g ≫ pullback.fst _ _ = frameActHom hchar g :=
  pullback.lift_fst _ _ _

theorem cmpComp_snd (hchar : FrameChar M A i) (g : Y3OrderMod.G M) :
    cmpComp hchar g ≫ pullback.snd _ _ = 𝟙 Z :=
  pullback.lift_snd _ _ _

/-- The `g`-component is the diagonal of `q` followed by the automorphism `g × 1`. -/
theorem cmpComp_eq (hchar : FrameChar M A i) (g : Y3OrderMod.G M) :
    cmpComp hchar g = pullback.diagonal (i ≫ A.F.hom) ≫
      pullback.map (i ≫ A.F.hom) (i ≫ A.F.hom) (i ≫ A.F.hom) (i ≫ A.F.hom)
        (frameActHom hchar g) (𝟙 Z) (𝟙 B)
        (by rw [Category.comp_id, frameActHom_q]) (by rw [Category.comp_id, Category.id_comp]) := by
  apply pullback.hom_ext
  · rw [cmpComp_fst, Category.assoc, pullback.lift_fst, ← Category.assoc,
      pullback.diagonal_fst, Category.id_comp]
  · rw [cmpComp_snd, Category.assoc, pullback.lift_snd, ← Category.assoc,
      pullback.diagonal_snd, Category.id_comp]

/-- Each component is an open immersion: the diagonal of the étale map `q` is one. -/
theorem cmpComp_isOpenImmersion [Mono i] (hchar : FrameChar M A i)
    (het : AlgebraicGeometry.Etale (i ≫ A.F.hom)) (g : Y3OrderMod.G M) :
    IsOpenImmersion (cmpComp hchar g) := by
  have := het
  have := frameActHom_isIso hchar g
  have : IsOpenImmersion (pullback.diagonal (i ≫ A.F.hom)) :=
    FormallyUnramified.isOpenImmersion_diagonal _
  rw [cmpComp_eq]
  infer_instance

/-- The components have pairwise disjoint images, by freeness. -/
theorem cmpComp_disjoint (hchar : FrameChar M A i) :
    _root_.Pairwise (Function.onFun Disjoint
      fun g : Y3OrderMod.G M => Set.range ⇑(cmpComp hchar g)) := by
  intro g h hgh
  rw [Function.onFun, Set.disjoint_left]
  rintro _ ⟨z₁, rfl⟩ ⟨z₂, hz₂⟩
  obtain ⟨w, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := cmpComp hchar g)
    (g := cmpComp hchar h) z₁ z₂ hz₂.symm
  apply hgh
  have hc := pullback.condition (f := cmpComp hchar g) (g := cmpComp hchar h)
  have h2 : pullback.fst (cmpComp hchar g) (cmpComp hchar h) =
      pullback.snd (cmpComp hchar g) (cmpComp hchar h) := by
    have e := congrArg (fun f => f ≫ pullback.snd (i ≫ A.F.hom) (i ≫ A.F.hom)) hc
    simp only [Category.assoc, cmpComp_snd, Category.comp_id] at e
    exact e
  have h1 := congrArg (fun f => f ≫ pullback.fst (i ≫ A.F.hom) (i ≫ A.F.hom)) hc
  simp only [Category.assoc, cmpComp_fst] at h1
  rw [← h2] at h1
  exact eq_of_frameActHom_eq hchar _ w h1

/-- The comparison map is surjective, by transitivity at geometric points. -/
theorem cmpMap_surjective [Mono i] (hchar : FrameChar M A i) :
    Function.Surjective ⇑(Sigma.desc (cmpComp hchar)) := by
  intro y
  have hcond : (geomPt y ≫ pullback.fst (i ≫ A.F.hom) (i ≫ A.F.hom)) ≫ i ≫ A.F.hom =
      (geomPt y ≫ pullback.snd (i ≫ A.F.hom) (i ≫ A.F.hom)) ≫ i ≫ A.F.hom := by
    rw [Category.assoc, Category.assoc, pullback.condition]
  obtain ⟨g, hg⟩ := exists_frameActHom hchar _ _ hcond
  obtain ⟨p⟩ := spec_field_nonempty (geomK y)
  refine ⟨(geomPt y ≫ pullback.snd (i ≫ A.F.hom) (i ≫ A.F.hom) ≫
    Sigma.ι (fun _ : Y3OrderMod.G M => Z) g) p, ?_⟩
  have hφ : (geomPt y ≫ pullback.snd (i ≫ A.F.hom) (i ≫ A.F.hom) ≫
      Sigma.ι (fun _ : Y3OrderMod.G M => Z) g) ≫ Sigma.desc (cmpComp hchar) = geomPt y := by
    apply pullback.hom_ext
    · simp only [Category.assoc, Sigma.ι_comp_desc_assoc, cmpComp_fst]
      rw [hg, Category.assoc]
    · simp only [Category.assoc, Sigma.ι_comp_desc_assoc, cmpComp_snd, Category.comp_id]
  rw [← Scheme.Hom.comp_apply, hφ, geomPt_apply]

/-- The comparison map is an isomorphism: a surjective open immersion. -/
theorem cmpMap_isIso [Mono i] (hchar : FrameChar M A i)
    (het : AlgebraicGeometry.Etale (i ≫ A.F.hom)) :
    IsIso (Sigma.desc (cmpComp hchar)) := by
  have := fun g => cmpComp_isOpenImmersion hchar het g
  have : IsOpenImmersion (Sigma.desc (cmpComp hchar)) :=
    isOpenImmersion_sigmaDesc (fun _ : Y3OrderMod.G M => Z) (cmpComp hchar)
      (cmpComp_disjoint hchar)
  have : AlgebraicGeometry.Surjective (Sigma.desc (cmpComp hchar)) :=
    ⟨cmpMap_surjective hchar⟩
  exact (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨inferInstance, inferInstance⟩

/-- The action relation is the kernel pair of `q`. -/
theorem isPullback_act [Mono i] (hchar : FrameChar M A i)
    (het : AlgebraicGeometry.Etale (i ≫ A.F.hom)) :
    IsPullback (Y3QuotientDescent.actS (frameAct hchar))
      (Y3QuotientDescent.actT Z (Y3OrderMod.G M)) (i ≫ A.F.hom) (i ≫ A.F.hom) := by
  have := cmpMap_isIso hchar het
  have h1 : Sigma.desc (cmpComp hchar) ≫ pullback.fst (i ≫ A.F.hom) (i ≫ A.F.hom) =
      Y3QuotientDescent.actS (frameAct hchar) := by
    apply Sigma.hom_ext
    intro g
    rw [Sigma.ι_comp_desc_assoc, cmpComp_fst, Y3QuotientDescent.actS, Sigma.ι_comp_desc,
      frameAct_hom]
  have h2 : Sigma.desc (cmpComp hchar) ≫ pullback.snd (i ≫ A.F.hom) (i ≫ A.F.hom) =
      Y3QuotientDescent.actT Z (Y3OrderMod.G M) := by
    apply Sigma.hom_ext
    intro g
    rw [Sigma.ι_comp_desc_assoc, cmpComp_snd, Y3QuotientDescent.actT, Sigma.ι_comp_desc]
  refine IsPullback.of_iso_pullback ⟨?_⟩ (asIso (Sigma.desc (cmpComp hchar))) h1 h2
  rw [← h1, ← h2, Category.assoc, Category.assoc, pullback.condition]

end Geom

end FrameTorsor

/-- B2' from B2: frame representability gives the torsor clause. The action of `g` on the
representing scheme `Z` lifts `ι(σ g)`, and the action relation is the kernel pair of
`Z ⟶ S`, because the comparison map `(g, z) ↦ (g z, z)` is a surjective open immersion. -/
theorem frameRepTorsor_of_rep (M : ℕ) [NeZero M] (h : BuzzardFrameRep M) :
    BuzzardFrameRepTorsor M := by
  intro S A
  obtain ⟨Z, i, hci, hfin, het, hsurj, hchar⟩ := h S A
  have := hci
  have : Mono i := inferInstance
  exact ⟨Z, i, hci, hfin, het, hsurj, hchar, FrameTorsor.frameAct hchar,
    fun g => FrameTorsor.frameActHom_spec hchar g, FrameTorsor.isPullback_act hchar het⟩

end Y3Buzzard

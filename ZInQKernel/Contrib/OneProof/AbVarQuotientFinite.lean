import ZInQKernel.Contrib.CloudR2Poincare.L4.QuotientExists
import ZInQKernel.Contrib.OneProof.MilneQuasiInverse.Descent

/-! A quotient by an arbitrary finite subgroup scheme over ℚ. The scheme quotient
and the descent of group axioms use the same suppliers as the stabilizer quotient. -/

noncomputable section

namespace ShimuraSteps.Quotient

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3 PkgI3.AbVar
open ZInQ.Contrib.CloudR2Poincare.L4
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000

local notation "OverQ" => Over (Spec (CommRingCat.of ℚ))

/-- The isogeny quotient by a finite subgroup, with its scheme kernel and
its universal property in abelian varieties. -/
structure IsFiniteSubgroupQuotient {B Q : AbVar ℚ} {G : OverQ}
    (j : G ⟶ B.X) (q : AbVar.Hom B Q) : Prop where
  isogeny : IsIsogenyMor q.hom
  kernel : IsPullback j (toUnit G) q.hom η[Q.X]
  lift_unique : ∀ (D : AbVar ℚ) (v : AbVar.Hom B D), j ≫ v.hom = 1 →
    ∃! w : AbVar.Hom Q D, q.hom ≫ w.hom = v.hom

section Translation

variable {X G : OverQ} [GrpObj X] [GrpObj G]
    (j : G ⟶ X) [IsMonHom j]

private abbrev target : G ⊗ X ⟶ X := (fst G X ≫ j) * snd G X

private theorem target_pair_mono [Mono j] : JointlyMono₂ (target j) (snd G X) := by
  constructor
  intro T f g ht hs
  apply CartesianMonoidalCategory.hom_ext
  · apply (cancel_mono j).mp
    simp only [target, MonObj.comp_mul] at ht
    rw [hs] at ht
    exact mul_right_cancel ht
  · exact hs

private def translationRelation [Mono j] : EquivalenceRelation (target j) (snd G X) where
  toJointlyMono₂ := target_pair_mono j
  r := lift (1 : X ⟶ G) (𝟙 X)
  reflexivity₁ := by simp [target, MonObj.comp_mul, MonObj.one_comp]
  reflexivity₂ := by simp
  s := lift (fst G X)⁻¹ (target j)
  symmetry₁ := by simp [target, MonObj.comp_mul, GrpObj.inv_comp]
  symmetry₂ := by simp
  c := PullbackCone.mk (pullback.fst _ _) (pullback.snd _ _) pullback.condition
  isLimit := (IsPullback.of_hasPullback (snd G X) (target j)).isLimit
  t := lift ((pullback.fst _ _ ≫ fst G X) * (pullback.snd _ _ ≫ fst G X))
    (pullback.snd _ _ ≫ snd G X)
  transitivity₁ := by
    have hc := pullback.condition (f := snd G X) (g := target j)
    simp only [target, MonObj.comp_mul] at hc
    simp only [target, MonObj.comp_mul, lift_fst_assoc, lift_snd, MonObj.mul_comp, Category.assoc]
    rw [_root_.mul_assoc, ← hc]
    rfl
  transitivity₂ := by simp

private def shear : G ⊗ X ≅ G ⊗ X where
  hom := lift (fst G X) (target j)
  inv := lift (fst G X) ((fst G X ≫ j)⁻¹ * snd G X)
  hom_inv_id := by
    ext <;> simp [target, MonObj.comp_mul, GrpObj.comp_inv]
  inv_hom_id := by
    ext <;> simp [target, MonObj.comp_mul]

private theorem target_properties [IsFinite G.hom] [Flat G.hom] :
    IsFinite (target j).left ∧ Flat (target j).left ∧
      LocallyOfFinitePresentation (target j).left := by
  have : IsFinite (snd G X).left :=
    inferInstanceAs (IsFinite (pullback.snd G.hom X.hom))
  have : Flat (snd G X).left :=
    inferInstanceAs (Flat (pullback.snd G.hom X.hom))
  have : LocallyOfFinitePresentation (snd G X).left := by
    change LocallyOfFinitePresentation (pullback.snd G.hom X.hom)
    infer_instance
  have he : (target j).left = (shear j).hom.left ≫ (snd G X).left := by
    change _ = ((shear j).hom ≫ snd G X).left
    simp [shear]
  rw [he]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end Translation

section SchemeQuotient

variable (B : AbVar ℚ) {G : OverQ} [GrpObj G] (j : G ⟶ B.X) [IsMonHom j]

private theorem finiteSchemeQuotient [IsClosedImmersion j.left] [IsFinite G.hom] [Flat G.hom] :
    ∃ (Y : OverQ) (p : B.X ⟶ Y),
      IsFinite p.left ∧ Flat p.left ∧ Surjective p.left ∧
      IsPullback (target j) (snd G B.X) p p := by
  let s : (G ⊗ B.X).left ⟶ B.X.left := (snd G B.X).left
  let t : (G ⊗ B.X).left ⟶ B.X.left := (target j).left
  have : IsFinite s := inferInstanceAs (IsFinite (pullback.snd G.hom B.X.hom))
  have : Flat s := inferInstanceAs (Flat (pullback.snd G.hom B.X.hom))
  have : LocallyOfFinitePresentation s := by
    change LocallyOfFinitePresentation (pullback.snd G.hom B.X.hom)
    infer_instance
  obtain ⟨htfin, htflat, htfp⟩ := target_properties j
  have : IsFinite t := htfin
  have : Flat t := htflat
  have : LocallyOfFinitePresentation t := htfp
  have : Mono j := Over.mono_of_mono_left j
  let es : EquivalenceRelation t s := schemeRelationOfOver (translationRelation j)
  have haff (x : B.X.left) : ∃ U : B.X.left.Opens, IsAffineOpen U ∧
      ∀ r : (G ⊗ B.X).left, s r = x → t r ∈ U := by
    obtain ⟨U, hU, hEU⟩ := abVar_finiteSet_affineOpen B
      (t '' (s ⁻¹' {x})) ((s.finite_preimage_singleton x).image t)
    exact ⟨U, hU, fun r hr => hEU ⟨r, hr, rfl⟩⟩
  obtain ⟨Y, p, w, hpfin, hpflat, _, hpsurj, hpb, ⟨hcol⟩⟩ :=
    ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.exists_quotient_of_finiteLocallyFree_equivalenceRelation
      s t (fun a b hs ht => es.right_cancellation a b ht hs)
      (homRelation_equivalence_swap es) haff
  have hb : s ≫ B.X.hom = t ≫ B.X.hom := by
    change (snd G B.X).left ≫ B.X.hom = (target j).left ≫ B.X.hom
    rw [Over.w, Over.w]
  let Y₀ := Over.mk (Cofork.IsColimit.desc hcol B.X.hom hb)
  let q : B.X ⟶ Y₀ := Over.homMk p (Cofork.IsColimit.π_desc' hcol B.X.hom hb)
  exact ⟨Y₀, q, hpfin, hpflat, hpsurj, over_kernelPair_of_scheme _ _ q hpb.flip⟩

variable {B} {Y : OverQ} (p : B.X ⟶ Y)
    [IsFinite p.left] [Flat p.left] [Surjective p.left]
    (hp : IsPullback (target j) (snd G B.X) p p)

include hp in
private theorem exists_operations :
    (∃ m : Y ⊗ Y ⟶ Y, (p ⊗ₘ p) ≫ m = μ[B.X] ≫ p) ∧
    (∃ v : Y ⟶ Y, p ≫ v = ι[B.X] ≫ p) := by
  constructor
  · obtain ⟨hf, hflat, hs⟩ := tensor_fpqc p p
    haveI := hf
    haveI := hflat
    haveI := hs
    refine exists_desc_over_of_kernelPair (p ⊗ₘ p)
      (target j ⊗ₘ target j) (snd G B.X ⊗ₘ snd G B.X)
      (tensor_kernelPair _ _ _ hp) (μ[B.X] ≫ p) ?_
    let u : (G ⊗ B.X) ⊗ (G ⊗ B.X) ⟶ G ⊗ B.X :=
      lift ((fst _ _ ≫ fst _ _) * (snd _ _ ≫ fst _ _))
        ((fst _ _ ≫ snd _ _) * (snd _ _ ≫ snd _ _))
    have ht : u ≫ target j = (target j ⊗ₘ target j) ≫ μ[B.X] := by
      rw [tensor_comp_mul_eq]
      simp only [u, target, MonObj.comp_mul, lift_fst_assoc, lift_snd,
        MonObj.mul_comp, Category.assoc]
      ac_rfl
    have hs' : u ≫ snd G B.X = (snd G B.X ⊗ₘ snd G B.X) ≫ μ[B.X] := by
      dsimp only [u]
      rw [lift_snd, tensor_comp_mul_eq]
    rw [← Category.assoc, ← Category.assoc, ← ht, ← hs', Category.assoc, Category.assoc, hp.w]
  · let u : G ⊗ B.X ⟶ G ⊗ B.X := lift (fst G B.X)⁻¹ (snd G B.X)⁻¹
    have ht : u ≫ target j = (target j)⁻¹ := by
      simp [u, target, MonObj.comp_mul, GrpObj.inv_comp, mul_inv_rev, mul_comm]
    have hs : u ≫ snd G B.X = (snd G B.X)⁻¹ := by simp [u]
    refine exists_desc_over_of_kernelPair p (target j) (snd G B.X) hp (ι[B.X] ≫ p) ?_
    change (target j)⁻¹ ≫ p = (snd G B.X)⁻¹ ≫ p
    rw [← ht, ← hs, Category.assoc, Category.assoc, hp.w]

include hp in
private theorem separated_quotient [IsClosedImmersion j.left] [IsFinite G.hom] :
    IsSeparated Y.hom := by
  let r : G ⊗ B.X ⟶ B.X ⊗ B.X := lift (target j) (snd G B.X)
  let δ : Y ⟶ Y ⊗ Y := lift (𝟙 Y) (𝟙 Y)
  have : Mono j := Over.mono_of_mono_left j
  have hm := target_pair_mono j
  haveI : Mono r := ⟨fun {T} u v h => hm.right_cancellation u v
    (by simpa [r, Category.assoc] using congrArg (· ≫ fst B.X B.X) h)
    (by simpa [r, Category.assoc] using congrArg (· ≫ snd B.X B.X) h)⟩
  haveI : IsProper (G ⊗ B.X).hom := by rw [Over.tensorObj_hom]; infer_instance
  haveI : IsSeparated (B.X ⊗ B.X).hom := by rw [Over.tensorObj_hom]; infer_instance
  haveI : IsProper r.left := isProper_over_hom _
  haveI : IsClosedImmersion r.left :=
    (IsClosedImmersion.iff_isProper_and_mono _).mpr ⟨inferInstance, inferInstance⟩
  have hpb : IsPullback r (target j ≫ p) (p ⊗ₘ p) δ := by
    refine IsPullback.mk' (by ext <;> simp [r, δ, hp.w])
      (fun {T} {u v} hu _ => (cancel_mono r).mp hu) ?_
    intro T c d hc
    have h₁ : c ≫ fst B.X B.X ≫ p = d := by
      simpa [δ] using congrArg (· ≫ fst Y Y) hc
    have h₂ : c ≫ snd B.X B.X ≫ p = d := by
      simpa [δ] using congrArg (· ≫ snd Y Y) hc
    let v := hp.lift (c ≫ fst B.X B.X) (c ≫ snd B.X B.X) (h₁.trans h₂.symm)
    refine ⟨v, ?_, ?_⟩
    · ext <;> simp [r, v]
    · rw [← Category.assoc, hp.lift_fst]
      exact h₁
  obtain ⟨hf, hflat, hs⟩ := tensor_fpqc p p
  haveI := hf
  have hpb' := (Over.forget (Spec (CommRingCat.of ℚ))).map_isPullback hpb
  change IsPullback r.left (target j ≫ p).left (p ⊗ₘ p).left δ.left at hpb'
  haveI : UniversallyClosed δ.left :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @UniversallyClosed)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      hpb' ⟨⟨hs, hflat⟩, inferInstance⟩ inferInstance
  haveI : Mono δ := by dsimp [δ]; infer_instance
  haveI : LocallyOfFiniteType (δ.left ≫ (fst Y Y).left) := by
    change LocallyOfFiniteType ((δ ≫ fst Y Y).left)
    simp [δ]
    infer_instance
  haveI : LocallyOfFiniteType δ.left := locallyOfFiniteType_of_comp δ.left (fst Y Y).left
  haveI : IsProper δ.left := {}
  have hc : IsClosedImmersion δ.left :=
    (IsClosedImmersion.iff_isProper_and_mono _).mpr ⟨inferInstance, inferInstance⟩
  exact ⟨hc⟩

end SchemeQuotient


private theorem translation_kernel {B : AbVar ℚ} {G : OverQ} [GrpObj G]
    (j : G ⟶ B.X) [IsMonHom j] [Mono j] {Q : AbVar ℚ} (q : AbVar.Hom B Q)
    (h : IsPullback (target j) (snd G B.X) q.hom q.hom) :
    IsPullback j (toUnit G) q.hom η[Q.X] := by
  have hz := congrArg (fun f => lift (𝟙 G) (1 : G ⟶ B.X) ≫ f) h.w
  have hj : j ≫ q.hom = 1 := by
    simpa only [← Category.assoc, target, MonObj.comp_mul, lift_fst, lift_snd,
      Category.id_comp, _root_.mul_one, MonObj.one_comp] using hz
  refine IsPullback.mk' hj (fun {T} {a b} ha _ => (cancel_mono j).mp ha) ?_
  intro T x u hx
  have he : x ≫ q.hom = (1 : T ⟶ B.X) ≫ q.hom := by
    rw [MonObj.one_comp, hx]
    exact congrArg (· ≫ η[Q.X]) (toUnit_unique u _)
  let l := h.lift x (1 : T ⟶ B.X) he
  refine ⟨l ≫ fst G B.X, ?_, toUnit_unique _ _⟩
  have h₁ : l ≫ target j = x := h.lift_fst _ _ _
  have h₂ : l ≫ snd G B.X = 1 := h.lift_snd _ _ _
  simpa only [target, MonObj.comp_mul, ← Category.assoc, h₂, _root_.mul_one] using h₁

/-- An arbitrary finite closed subgroup scheme of an abelian variety over ℚ
has an isogeny quotient with the indicated kernel and universal property. -/
theorem finiteSubgroupQuotient_exists (B : AbVar ℚ) {G : OverQ} [GrpObj G]
    (j : G ⟶ B.X) [IsMonHom j] [IsClosedImmersion j.left] [IsFinite G.hom] :
    ∃ (Q : AbVar ℚ) (q : AbVar.Hom B Q), IsFiniteSubgroupQuotient j q := by
  haveI : Smooth G.hom := ZInQ.Contrib.CloudR2Poincare.L3.cartierSmooth_proof ℚ G inferInstance
  haveI : Flat G.hom := inferInstance
  obtain ⟨Y, p, hf, hflat, hs, hp⟩ := finiteSchemeQuotient B j
  haveI := hf
  haveI := hflat
  haveI := hs
  haveI : Epi p := epi_over_of_flat_surjective p
  obtain ⟨m, hm⟩ := (exists_operations j p hp).1
  obtain ⟨v, hv⟩ := (exists_operations j p hp).2
  let U := 𝟙_ OverQ
  have h₁ := tensor_fpqc (𝟙 U) p
  have h₂ := tensor_fpqc p (𝟙 U)
  haveI : Epi (𝟙 U ⊗ₘ p) :=
    letI := h₁.2.1
    letI := h₁.2.2
    epi_over_of_flat_surjective _
  haveI : Epi (p ⊗ₘ 𝟙 U) :=
    letI := h₂.2.1
    letI := h₂.2.2
    epi_over_of_flat_surjective _
  obtain ⟨hpf, hpfl, hps⟩ := tensor_fpqc p p
  haveI := hpf
  haveI := hpfl
  haveI := hps
  haveI : Epi (p ⊗ₘ p) := epi_over_of_flat_surjective _
  haveI : Epi ((p ⊗ₘ p) ⊗ₘ p) :=
    let h := tensor_fpqc (p ⊗ₘ p) p
    letI := h.2.1
    letI := h.2.2
    epi_over_of_flat_surjective _
  letI : GrpObj Y := grpObjOfEpi p m hm v hv
  haveI : IsMonHom p := isMonHom_grpObjOfEpi p m hm v hv
  haveI : IsSeparated Y.hom := separated_quotient j p hp
  haveI : LocallyOfFiniteType Y.hom := locallyFiniteType_of_finite_flat_surjective p
  haveI : UniversallyClosed (p.left ≫ Y.hom) := by rw [Over.w]; infer_instance
  haveI : UniversallyClosed Y.hom := UniversallyClosed.of_comp_surjective p.left Y.hom
  let Q : AbVar ℚ :=
    { X := Y
      proper := {}
      smooth := ZInQ.Contrib.CloudR2Poincare.L3.cartierSmooth_proof ℚ Y inferInstance
      geomInt := geometricallyIntegral_of_finite_flat_surjective p }
  let q : AbVar.Hom B Q := Hom.mk' p
  haveI : Mono j := Over.mono_of_mono_left j
  refine ⟨Q, q, ⟨⟨hf, hs⟩, translation_kernel j q hp, ?_⟩⟩
  intro D f hkill
  haveI : EffectiveEpi p.left := inferInstance
  obtain ⟨w, hw, hwf⟩ :=
    ZInQ.Contrib.MilneQuasiInverse.Descent.GroupKernelPowerDescent.Construction.groupHom_descends_of_kernel
      p f.hom (fun T x hx => by
        have hker := translation_kernel j q hp
        let u := hker.lift x (toUnit T) hx
        have hu : u ≫ j = x := hker.lift_fst _ _ _
        rw [← hu, Category.assoc, hkill, MonObj.comp_one])
  haveI := hw
  refine ⟨Hom.mk' w, hwf, fun z hz => Hom.ext' ((cancel_epi p).mp (hz.trans hwf.symm))⟩

end ShimuraSteps.Quotient

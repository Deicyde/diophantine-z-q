import ZInQKernel.Contrib.OneProof.TateFiniteSubgroup
import ZInQKernel.Contrib.CloudR2Poincare.L4.QuotientExists

/-!
# Quotients by arbitrary finite closed subgroup schemes in characteristic zero

The action, descent and separatedness arguments specialize the constructions of
CloudR2Poincare.L4 to the subgroup inclusion. They apply without any line bundle
realizing the subgroup as a stabilizer. The quotient itself is the project’s
finite locally free equivalence-relation quotient.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ.Contrib.CloudR2Poincare
open ZInQ.Contrib.CloudR2Poincare.L4 (tensor_comp_mul_eq tensor_fpqc exists_desc_over_of_kernelPair
  tensor_kernelPair epi_over_of_flat_surjective grpObjOfEpi isProper_over_hom
  geometricallyIntegral_of_finite_flat_surjective locallyFiniteType_of_finite_flat_surjective
  over_kernelPair_of_scheme schemeRelationOfOver homRelation_equivalence_swap abVar_finiteSet_affineOpen)

namespace ZInQ.Contrib.TateFiniteApproximation.SubgroupQuotient

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

variable {k : Type} [Field k] (A : PkgI3.AbVar k) (H : FiniteSubgroupScheme A)

/-- The coequalizer of the two arrows of the subgroup action on A. -/
structure Presentation where
  Q : Over (Spec (.of k))
  q : A.X ⟶ Q
  [flat : Flat q.left]
  [finite : IsFinite q.left]
  [surjective : Surjective q.left]
  [finitePresentation : LocallyOfFinitePresentation q.left]
  kernelPair : IsPullback ((fst H.obj A.X ≫ H.incl) * snd H.obj A.X) (snd H.obj A.X) q q

attribute [instance] Presentation.flat Presentation.finite Presentation.surjective Presentation.finitePresentation

variable (Q : Presentation A H)

/-- The exact stabilizer action in the supplied quotient relation. -/
abbrev quotientTarget : H.obj ⊗ A.X ⟶ A.X := fst H.obj A.X ≫ H.incl * snd H.obj A.X

/-- A product of two quotient arrows in `H.obj × A` is again a quotient arrow. -/
def quotientRelationMul : (H.obj ⊗ A.X) ⊗ (H.obj ⊗ A.X) ⟶ H.obj ⊗ A.X :=
  lift ((fst _ _ ≫ fst _ _) * (snd _ _ ≫ fst _ _))
    ((fst _ _ ≫ snd _ _) * (snd _ _ ≫ snd _ _))

lemma quotientRelationMul_target : quotientRelationMul A H ≫ quotientTarget A H =
    (quotientTarget A H ⊗ₘ quotientTarget A H) ≫ μ[A.X] := by
  rw [tensor_comp_mul_eq]
  simp only [quotientRelationMul, quotientTarget, MonObj.comp_mul, lift_fst_assoc,
    lift_snd, MonObj.mul_comp, Category.assoc]
  ac_rfl

lemma quotientRelationMul_source : quotientRelationMul A H ≫ snd H.obj A.X =
    (snd H.obj A.X ⊗ₘ snd H.obj A.X) ≫ μ[A.X] := by
  rw [quotientRelationMul, lift_snd, tensor_comp_mul_eq]

/-- Multiplication descends from the actual group scheme to its quotient scheme. -/
theorem exists_quotientMul : ∃ m : Q.Q ⊗ Q.Q ⟶ Q.Q,
    (Q.q ⊗ₘ Q.q) ≫ m = μ[A.X] ≫ Q.q := by
  obtain ⟨hf, hflat, hs⟩ := tensor_fpqc Q.q Q.q
  haveI := hf
  haveI := hflat
  haveI := hs
  refine exists_desc_over_of_kernelPair (Q.q ⊗ₘ Q.q)
    (quotientTarget A H ⊗ₘ quotientTarget A H)
    (snd H.obj A.X ⊗ₘ snd H.obj A.X) (tensor_kernelPair _ _ _ Q.kernelPair) (μ[A.X] ≫ Q.q) ?_
  calc
    (quotientTarget A H ⊗ₘ quotientTarget A H) ≫ μ[A.X] ≫ Q.q =
        quotientRelationMul A H ≫ quotientTarget A H ≫ Q.q := by
          simpa only [Category.assoc] using
            congrArg (· ≫ Q.q) (quotientRelationMul_target A H).symm
    _ = quotientRelationMul A H ≫ snd H.obj A.X ≫ Q.q := by rw [Q.kernelPair.w]
    _ = (snd H.obj A.X ⊗ₘ snd H.obj A.X) ≫ μ[A.X] ≫ Q.q := by
      rw [← Category.assoc, quotientRelationMul_source, Category.assoc]

/-- Inversion descends along the same exact kernel-pair relation. -/
theorem exists_quotientInv : ∃ v : Q.Q ⟶ Q.Q, Q.q ≫ v = ι[A.X] ≫ Q.q := by
  let u : H.obj ⊗ A.X ⟶ H.obj ⊗ A.X :=
    lift (fst H.obj A.X)⁻¹ (snd H.obj A.X)⁻¹
  have ht : u ≫ quotientTarget A H = (quotientTarget A H)⁻¹ := by
    simp [u, quotientTarget, MonObj.comp_mul, GrpObj.inv_comp, mul_inv_rev, mul_comm]
  have hs : u ≫ snd H.obj A.X = (snd H.obj A.X)⁻¹ := by simp [u]
  refine exists_desc_over_of_kernelPair Q.q (quotientTarget A H) (snd H.obj A.X)
    Q.kernelPair (ι[A.X] ≫ Q.q) ?_
  change (quotientTarget A H)⁻¹ ≫ Q.q = (snd H.obj A.X)⁻¹ ≫ Q.q
  rw [← ht, ← hs, Category.assoc, Category.assoc, Q.kernelPair.w]

/-- The actual quotient scheme receives a proved group-object structure. -/
@[reducible] def quotientGrp : GrpObj Q.Q :=
  let q := Q.q
  haveI : Epi q := epi_over_of_flat_surjective q
  have h₁ := tensor_fpqc (𝟙 (𝟙_ (Over (Spec (.of k))))) q
  haveI : Epi (𝟙 (𝟙_ (Over (Spec (.of k)))) ⊗ₘ q) :=
    letI := h₁.2.1
    letI := h₁.2.2
    epi_over_of_flat_surjective _
  have h₂ := tensor_fpqc q (𝟙 (𝟙_ (Over (Spec (.of k)))))
  haveI : Epi (q ⊗ₘ 𝟙 (𝟙_ (Over (Spec (.of k))))) :=
    letI := h₂.2.1
    letI := h₂.2.2
    epi_over_of_flat_surjective _
  have h₃ := tensor_fpqc q q
  haveI := h₃.1
  haveI := h₃.2.1
  haveI := h₃.2.2
  have h₄ := tensor_fpqc (q ⊗ₘ q) q
  haveI : Epi ((q ⊗ₘ q) ⊗ₘ q) :=
    letI := h₄.2.1
    letI := h₄.2.2
    epi_over_of_flat_surjective _
  grpObjOfEpi q (exists_quotientMul A H Q).choose (exists_quotientMul A H Q).choose_spec
    (exists_quotientInv A H Q).choose (exists_quotientInv A H Q).choose_spec

/-- The finite-flat quotient map is an actual homomorphism for the descended structure. -/
theorem quotient_isMonHom : letI := quotientGrp A H Q; IsMonHom Q.q := by
  letI := quotientGrp A H Q
  constructor
  · rfl
  · exact (exists_quotientMul A H Q).choose_spec.symm

/-- The exact action relation embedded into A×A. -/
abbrev quotientRelation : H.obj ⊗ A.X ⟶ A.X ⊗ A.X :=
  lift (quotientTarget A H) (snd H.obj A.X)

/-- The exact action relation is monic, because the subgroup inclusion is monic. -/
theorem mono_quotientRelation : Mono (quotientRelation A H) := by
  haveI : Mono H.incl := Over.mono_of_mono_left H.incl
  constructor
  intro T u v h
  have ht : u ≫ quotientTarget A H = v ≫ quotientTarget A H := by
    simpa using congrArg (· ≫ fst A.X A.X) h
  have hs : u ≫ snd H.obj A.X = v ≫ snd H.obj A.X := by
    simpa using congrArg (· ≫ snd A.X A.X) h
  have hj : u ≫ fst H.obj A.X ≫ H.incl = v ≫ fst H.obj A.X ≫ H.incl := by
    simp only [quotientTarget, MonObj.comp_mul] at ht
    rw [hs] at ht
    exact mul_right_cancel ht
  have hk : u ≫ fst H.obj A.X = v ≫ fst H.obj A.X := by
    apply (cancel_mono H.incl).1
    simpa only [Category.assoc] using hj
  ext
  · exact congrArg Over.Hom.left hk
  · exact congrArg Over.Hom.left hs

/-- The action relation is an actual closed immersion, not just a relation on geometric points. -/
theorem closed_quotientRelation : IsClosedImmersion (quotientRelation A H).left := by
  haveI : IsProper (H.obj ⊗ A.X).hom := by rw [Over.tensorObj_hom]; infer_instance
  haveI : IsSeparated (A.X ⊗ A.X).hom := by rw [Over.tensorObj_hom]; infer_instance
  haveI : Mono (quotientRelation A H) := mono_quotientRelation A H
  haveI : IsProper (quotientRelation A H).left := isProper_over_hom _
  exact (IsClosedImmersion.iff_isProper_and_mono _).mpr ⟨inferInstance, inferInstance⟩

/-- The relation is exactly the pullback of the quotient's diagonal along q×q. -/
theorem quotientDiagonal_isPullback :
    IsPullback (quotientRelation A H) (quotientTarget A H ≫ Q.q)
      (Q.q ⊗ₘ Q.q) (lift (𝟙 Q.Q) (𝟙 Q.Q)) := by
  haveI : Mono (quotientRelation A H) := mono_quotientRelation A H
  refine IsPullback.mk' (by ext <;> simp [quotientRelation, Q.kernelPair.w])
    (fun {T} {u v} hu _ => (cancel_mono (quotientRelation A H)).1 hu) ?_
  intro T c d hc
  have h₁ : c ≫ fst A.X A.X ≫ Q.q = d := by
    simpa using congrArg (· ≫ fst Q.Q Q.Q) hc
  have h₂ : c ≫ snd A.X A.X ≫ Q.q = d := by
    simpa using congrArg (· ≫ snd Q.Q Q.Q) hc
  let r := Q.kernelPair.lift (c ≫ fst A.X A.X) (c ≫ snd A.X A.X) (h₁.trans h₂.symm)
  refine ⟨r, ?_, ?_⟩
  · ext <;> simp [r, quotientRelation]
  · rw [← Category.assoc, Q.kernelPair.lift_fst]
    exact h₁

/-- The quotient is separated: its diagonal descends from the actual closed action relation. -/
theorem quotient_separated : IsSeparated Q.Q.hom := by
  obtain ⟨hfin, hflat, hsurj⟩ := tensor_fpqc Q.q Q.q
  haveI := hfin
  haveI := hflat
  haveI := hsurj
  let δ : Q.Q ⟶ Q.Q ⊗ Q.Q := lift (𝟙 Q.Q) (𝟙 Q.Q)
  haveI : IsClosedImmersion (quotientRelation A H).left := closed_quotientRelation A H
  have hp := (quotientDiagonal_isPullback A H Q).map (Over.forget (Spec (.of k)))
  change IsPullback (quotientRelation A H).left (quotientTarget A H ≫ Q.q).left
    (Q.q ⊗ₘ Q.q).left δ.left at hp
  haveI : UniversallyClosed δ.left :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @UniversallyClosed)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hp
      ⟨⟨hsurj, hflat⟩, inferInstance⟩ inferInstance
  haveI : Mono δ := by dsimp [δ]; infer_instance
  haveI : LocallyOfFiniteType (δ.left ≫ (fst Q.Q Q.Q).left) := by
    have hδ : δ.left ≫ (fst Q.Q Q.Q).left = 𝟙 Q.Q.left := by
      change (δ ≫ fst Q.Q Q.Q).left = _
      simp [δ]
    rw [hδ]
    infer_instance
  haveI : LocallyOfFiniteType δ.left := locallyOfFiniteType_of_comp δ.left (fst Q.Q Q.Q).left
  haveI : IsProper δ.left := {}
  have hc : IsClosedImmersion δ.left :=
    (IsClosedImmersion.iff_isProper_and_mono _).mpr ⟨inferInstance, inferInstance⟩
  constructor
  exact hc

/-- The supplied quotient has geometric integrality, proved by actual field base change. -/
theorem quotient_geometricallyIntegral : GeometricallyIntegral Q.Q.hom :=
  geometricallyIntegral_of_finite_flat_surjective Q.q

/-- The action shear (h,a)↦(h,j(h)a), with its actual inverse. -/
def stabilizerActionShear : H.obj ⊗ A.X ≅ H.obj ⊗ A.X where
  hom := lift (fst H.obj A.X) (quotientTarget A H)
  inv := lift (fst H.obj A.X) ((fst H.obj A.X ≫ H.incl)⁻¹ * snd H.obj A.X)
  hom_inv_id := by
    ext <;> simp [quotientTarget, MonObj.comp_mul, GrpObj.comp_inv]
  inv_hom_id := by
    ext <;> simp [quotientTarget, MonObj.comp_mul]

@[simp] theorem stabilizerActionShear_hom_snd :
    (stabilizerActionShear A H).hom ≫ snd H.obj A.X = quotientTarget A H := by
  simp [stabilizerActionShear]

/-- Native finite/flat/LFP projection data, the exact finite-locally-free criterion. -/
theorem stabilizer_projection_finite_flat_lfp [CharZero k] :
    IsFinite (snd H.obj A.X).left ∧ Flat (snd H.obj A.X).left ∧
      LocallyOfFinitePresentation (snd H.obj A.X).left := by
  haveI : Smooth H.obj.hom := L3.cartierSmooth_proof k H.obj inferInstance
  change IsFinite (pullback.snd H.obj.hom A.X.hom) ∧
    Flat (pullback.snd H.obj.hom A.X.hom) ∧
    LocallyOfFinitePresentation (pullback.snd H.obj.hom A.X.hom)
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- The actual action has the same native finite/flat/LFP properties as the projection. -/
theorem stabilizer_action_finite_flat_lfp [CharZero k] :
    IsFinite (quotientTarget A H).left ∧ Flat (quotientTarget A H).left ∧
      LocallyOfFinitePresentation (quotientTarget A H).left := by
  obtain ⟨hf, ht, hp⟩ := stabilizer_projection_finite_flat_lfp A H
  haveI := hf
  haveI := ht
  haveI := hp
  have he : (quotientTarget A H).left =
      (stabilizerActionShear A H).hom.left ≫ (snd H.obj A.X).left := by
    change _ = ((stabilizerActionShear A H).hom ≫ snd H.obj A.X).left
    rw [stabilizerActionShear_hom_snd]
  rw [he]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Reflexivity map for the literal action relation. -/
abbrev stabilizerRelationUnit : A.X ⟶ H.obj ⊗ A.X := lift (1 : A.X ⟶ H.obj) (𝟙 A.X)

/-- Symmetry map for the literal action relation. -/
abbrev stabilizerRelationInv : H.obj ⊗ A.X ⟶ H.obj ⊗ A.X :=
  lift (fst H.obj A.X)⁻¹ (quotientTarget A H)

/-- Composition map on the actual source/target pullback of the action relation. -/
abbrev stabilizerRelationComp :
    pullback (snd H.obj A.X) (quotientTarget A H) ⟶ H.obj ⊗ A.X :=
  lift ((pullback.fst _ _ ≫ fst H.obj A.X) * (pullback.snd _ _ ≫ fst H.obj A.X))
    (pullback.snd _ _ ≫ snd H.obj A.X)

/-- The actual action/projection pair is an internal equivalence relation. -/
theorem stabilizer_action_isEquivalenceRelation :
    IsEquivalenceRelation (quotientTarget A H) (snd H.obj A.X) := by
  haveI : Mono (quotientRelation A H) := mono_quotientRelation A H
  apply EquivalenceRelation.isEquivalenceRelation
  refine {
    right_cancellation := ?_
    r := stabilizerRelationUnit A H
    reflexivity₁ := ?_
    reflexivity₂ := ?_
    s := stabilizerRelationInv A H
    symmetry₁ := ?_
    symmetry₂ := ?_
    c := PullbackCone.mk (pullback.fst _ _) (pullback.snd _ _) pullback.condition
    isLimit := (IsPullback.of_hasPullback (snd H.obj A.X) (quotientTarget A H)).isLimit
    t := stabilizerRelationComp A H
    transitivity₁ := ?_
    transitivity₂ := ?_ }
  · intro T f g hf hg
    apply (cancel_mono (quotientRelation A H)).1
    ext
    · simpa [quotientRelation, Over.comp_left] using congrArg Over.Hom.left hf
    · simpa [quotientRelation, Over.comp_left] using congrArg Over.Hom.left hg
  · simp [stabilizerRelationUnit, quotientTarget, MonObj.comp_mul, MonObj.one_comp]
  · simp [stabilizerRelationUnit]
  · simp [stabilizerRelationInv, quotientTarget, MonObj.comp_mul, GrpObj.inv_comp]
  · simp [stabilizerRelationInv]
  · change stabilizerRelationComp A H ≫ quotientTarget A H =
      pullback.fst (snd H.obj A.X) (quotientTarget A H) ≫ quotientTarget A H
    have hc := pullback.condition (f := snd H.obj A.X) (g := quotientTarget A H)
    simp only [quotientTarget, MonObj.comp_mul] at hc
    simp only [stabilizerRelationComp, quotientTarget, MonObj.comp_mul,
      lift_fst_assoc, lift_snd, MonObj.mul_comp, Category.assoc]
    rw [_root_.mul_assoc, ← hc]
  · simp [stabilizerRelationComp]

/-- Properness is proved, not part of the supplied quotient record. -/
theorem quotient_proper : IsProper Q.Q.hom := by
  haveI : IsSeparated Q.Q.hom := quotient_separated A H Q
  haveI : LocallyOfFiniteType Q.Q.hom := locallyFiniteType_of_finite_flat_surjective Q.q
  haveI : UniversallyClosed (Q.q.left ≫ Q.Q.hom) := by rw [Over.w]; infer_instance
  haveI : UniversallyClosed Q.Q.hom := UniversallyClosed.of_comp_surjective Q.q.left Q.Q.hom
  exact {}

/-- Smoothness follows from the proved descended group object and L3's actual Cartier theorem. -/
theorem quotient_smooth [CharZero k] : Smooth Q.Q.hom := by
  letI := quotientGrp A H Q
  exact L3.cartierSmooth_proof k Q.Q (locallyFiniteType_of_finite_flat_surjective Q.q)

/-- The actual quotient scheme, with its proved descended structure, as a PkgI3 abelian variety. -/
def quotientAbVar [CharZero k] : PkgI3.AbVar k where
  X := Q.Q
  grp := quotientGrp A H Q
  proper := quotient_proper A H Q
  smooth := quotient_smooth A H Q
  geomInt := quotient_geometricallyIntegral A H Q

/-- The literal quotient arrow, packaged as an actual abelian-variety homomorphism. -/
def quotientAbVarHom [CharZero k] : PkgI3.AbVar.Hom A (quotientAbVar A H Q) :=
  letI := quotientGrp A H Q
  haveI := quotient_isMonHom A H Q
  PkgI3.AbVar.Hom.mk' Q.q

@[simp] theorem quotientAbVarHom_hom [CharZero k] :
    (quotientAbVarHom A H Q).hom = Q.q := rfl

/-- Every finite closed subgroup has a finite, faithfully flat quotient over k. -/
theorem exists_presentation [CharZero k] : Nonempty (Presentation A H) := by
  classical
  let s : (H.obj ⊗ A.X).left ⟶ A.X.left := (snd H.obj A.X).left
  let t : (H.obj ⊗ A.X).left ⟶ A.X.left := (quotientTarget A H).left
  obtain ⟨hsfin, hsflat, hsfp⟩ := stabilizer_projection_finite_flat_lfp A H
  obtain ⟨htfin, htflat, htfp⟩ := stabilizer_action_finite_flat_lfp A H
  haveI : IsFinite s := hsfin
  haveI : Flat s := hsflat
  haveI : LocallyOfFinitePresentation s := hsfp
  haveI : IsFinite t := htfin
  haveI : Flat t := htflat
  haveI : LocallyOfFinitePresentation t := htfp
  let e := (stabilizer_action_isEquivalenceRelation A H).nonempty_equivalenceRelation.some
  let es : EquivalenceRelation t s := schemeRelationOfOver e
  have hmono : ∀ {T : Scheme} (a b : T ⟶ (H.obj ⊗ A.X).left),
      a ≫ s = b ≫ s → a ≫ t = b ≫ t → a = b :=
    fun a b hs ht => es.right_cancellation a b ht hs
  have hequiv : ∀ T : Scheme, Equivalence fun x y : T ⟶ A.X.left =>
      ∃ φ : T ⟶ (H.obj ⊗ A.X).left, φ ≫ s = x ∧ φ ≫ t = y :=
    fun T => homRelation_equivalence_swap es T
  have haff : ∀ x : A.X.left, ∃ U : A.X.left.Opens, IsAffineOpen U ∧
      ∀ r : (H.obj ⊗ A.X).left, s r = x → t r ∈ U := by
    intro x
    obtain ⟨U, hU, hEU⟩ := abVar_finiteSet_affineOpen A
      (t '' (s ⁻¹' {x})) ((s.finite_preimage_singleton x).image t)
    exact ⟨U, hU, fun r hr => hEU ⟨r, hr, rfl⟩⟩
  obtain ⟨Y, p, w, hpfin, hpflat, hpfp, hpsurj, hpb, hcol⟩ :=
    ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.exists_quotient_of_finiteLocallyFree_equivalenceRelation
      s t hmono hequiv haff

  let hc := hcol.some
  have hbase : s ≫ A.X.hom = t ≫ A.X.hom := by
    change (snd H.obj A.X).left ≫ A.X.hom = (quotientTarget A H).left ≫ A.X.hom
    rw [Over.w, Over.w]
  let qbase : Y ⟶ Spec (.of k) := Cofork.IsColimit.desc hc A.X.hom hbase
  have hqbase : p ≫ qbase = A.X.hom := Cofork.IsColimit.π_desc' hc A.X.hom hbase
  let q : A.X ⟶ Over.mk qbase := Over.homMk p hqbase
  exact ⟨{
    Q := Over.mk qbase
    q := q
    flat := hpflat
    finite := hpfin
    surjective := hpsurj
    finitePresentation := hpfp
    kernelPair := over_kernelPair_of_scheme (quotientTarget A H) (snd H.obj A.X) q hpb.flip }⟩

/-- The quotient homomorphism has the prescribed kernel on every test scheme. -/
theorem exists_isogeny_with_kernel [CharZero k] :
    ∃ (B : PkgI3.AbVar k) (f : PkgI3.AbVar.Hom A B), ZInQ.DefFaltings.IsIsogeny f.hom ∧
      ∀ (T : Over (Spec (.of k))) (P : T ⟶ A.X), P ≫ f.hom = 1 ↔ ∃ h : T ⟶ H.obj, h ≫ H.incl = P := by
  obtain ⟨D⟩ := exists_presentation A H
  letI := quotientGrp A H D
  let B := quotientAbVar A H D
  let f : PkgI3.AbVar.Hom A B := quotientAbVarHom A H D
  have hi : ZInQ.DefFaltings.IsIsogeny f.hom :=
    ⟨inferInstance, inferInstanceAs (IsFinite D.q.left), inferInstanceAs (Surjective D.q.left)⟩
  refine ⟨B, f, hi, fun T P => ⟨?_, ?_⟩⟩
  · intro hP
    have heq : P ≫ D.q = (1 : T ⟶ A.X) ≫ D.q := by
      change P ≫ f.hom = 1 ≫ f.hom
      rw [MonObj.one_comp, hP]
    let h := D.kernelPair.lift P 1 heq
    have hfst : h ≫ quotientTarget A H = P := D.kernelPair.lift_fst ..
    have hsnd : h ≫ snd H.obj A.X = 1 := D.kernelPair.lift_snd ..
    refine ⟨h ≫ fst H.obj A.X, ?_⟩
    simpa only [quotientTarget, MonObj.comp_mul, hsnd, _root_.mul_one, Category.assoc] using hfst
  · rintro ⟨h,rfl⟩
    have heq := congrArg (fun a => (lift h (1 : T ⟶ A.X)) ≫ a) D.kernelPair.w
    change (h ≫ H.incl) ≫ D.q = 1
    simpa only [← Category.assoc, MonObj.comp_mul, lift_fst, lift_snd, _root_.mul_one,
      show (1 : T ⟶ A.X) ≫ D.q = 1 from MonObj.one_comp (f := f.hom)] using heq

end ZInQ.Contrib.TateFiniteApproximation.SubgroupQuotient

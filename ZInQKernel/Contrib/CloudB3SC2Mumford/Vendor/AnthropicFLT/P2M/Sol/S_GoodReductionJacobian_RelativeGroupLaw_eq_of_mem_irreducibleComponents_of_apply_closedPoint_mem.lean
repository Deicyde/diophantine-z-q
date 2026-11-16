/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal_and_le_ker
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian TopologicalSpace

noncomputable section

universe u

namespace P2mGroupSchemeComponents

section Maps

variable {k : Type u} [Field k] {N : Scheme.{u}} {gN : N ⟶ Spec (CommRingCat.of k)}
  (LN : RelativeGroupLaw k gN)

-- [port] local notation `pt` removed (build-time syntax); its uses below are expanded to `(𝟙 (Spec (CommRingCat.of k)))`

def const {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) gN) :
    SchemeHomOver t gN :=
  GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) s

@[scoped simp]
theorem const_coe {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) gN) :
    (const t s).1 = t ≫ s.1 := rfl

theorem const_pt (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) gN) : const (𝟙 (Spec (CommRingCat.of k))) s = s :=
  Subtype.ext (Category.id_comp _)

theorem const_transition {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (t' : T' ⟶ Spec (CommRingCat.of k)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) gN) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (const t s) = const t' s :=
  Subtype.ext (by simp [← hψ])

theorem const_mul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (s s' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) gN) :
    const t (LN.mul (𝟙 (Spec (CommRingCat.of k))) s s') = LN.mul t (const t s) (const t s') :=
  LN.mul_natural (𝟙 (Spec (CommRingCat.of k))) t t (Category.comp_id t) s s'

theorem const_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) :
    const t (LN.one (𝟙 (Spec (CommRingCat.of k)))) = LN.one t :=
  LN.one_natural (𝟙 (Spec (CommRingCat.of k))) t t (Category.comp_id t)

theorem inv_natural {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (t' : T' ⟶ Spec (CommRingCat.of k)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (x : SchemeHomOver t gN) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (LN.inv t x) =
      LN.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  letI := LN.pointGroup t'
  have h : GoodReductionJacobian.schemeHomOverComp ψ hψ (LN.inv t x) *
      GoodReductionJacobian.schemeHomOverComp ψ hψ x = 1 := by
    show LN.mul t' _ _ = LN.one t'
    rw [← LN.mul_natural t t' ψ hψ, LN.inv_mul_cancel, LN.one_natural]
  exact eq_inv_of_mul_eq_one_left h

theorem const_inv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) gN) :
    const t (LN.inv (𝟙 (Spec (CommRingCat.of k))) s) = LN.inv t (const t s) :=
  inv_natural LN (𝟙 (Spec (CommRingCat.of k))) t t (Category.comp_id t) s

def transl (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) gN) : N ⟶ N :=
  (LN.mul gN (const gN s) RelativeGroupLaw.idPoint).1

theorem transl_over (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) gN) : transl LN s ≫ gN = gN :=
  (LN.mul gN (const gN s) RelativeGroupLaw.idPoint).2

theorem comp_transl {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (x : SchemeHomOver t gN)
    (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) gN) : x.1 ≫ transl LN s = (LN.mul t (const t s) x).1 := by
  have h := LN.mul_natural gN t x.1 x.2 (const gN s) RelativeGroupLaw.idPoint
  have h1 : GoodReductionJacobian.schemeHomOverComp x.1 x.2 (const gN s) = const t s :=
    const_transition gN t x.1 x.2 s
  have h2 : GoodReductionJacobian.schemeHomOverComp x.1 x.2
      (RelativeGroupLaw.idPoint : SchemeHomOver gN gN) = x :=
    Subtype.ext (Category.comp_id _)
  rw [h1, h2] at h
  exact congrArg Subtype.val h

theorem transl_point {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (x : SchemeHomOver t gN)
    (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) gN) :
    (⟨x.1 ≫ transl LN s, by rw [Category.assoc, transl_over, x.2]⟩ : SchemeHomOver t gN) =
      LN.mul t (const t s) x :=
  Subtype.ext (comp_transl LN x s)

theorem transl_one : transl LN (LN.one (𝟙 (Spec (CommRingCat.of k)))) = 𝟙 N := by
  have h := comp_transl LN (RelativeGroupLaw.idPoint : SchemeHomOver gN gN) (LN.one (𝟙 (Spec (CommRingCat.of k))))
  rw [const_one, LN.one_mul] at h
  simpa using h

theorem transl_comp (s s' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) gN) :
    transl LN s ≫ transl LN s' = transl LN (LN.mul (𝟙 (Spec (CommRingCat.of k))) s' s) := by
  have h := comp_transl LN (LN.mul gN (const gN s) RelativeGroupLaw.idPoint) s'
  rw [← LN.mul_assoc, ← const_mul] at h
  exact h

scoped instance isIso_transl (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) gN) : IsIso (transl LN s) := by
  letI := LN.pointGroup (𝟙 (Spec (CommRingCat.of k)))
  refine ⟨⟨transl LN (LN.inv (𝟙 (Spec (CommRingCat.of k))) s), ?_, ?_⟩⟩
  · rw [transl_comp, show LN.mul (𝟙 (Spec (CommRingCat.of k))) (LN.inv (𝟙 (Spec (CommRingCat.of k))) s) s = LN.one (𝟙 (Spec (CommRingCat.of k))) from LN.inv_mul_cancel (𝟙 (Spec (CommRingCat.of k))) s,
      transl_one]
  · rw [transl_comp, show LN.mul (𝟙 (Spec (CommRingCat.of k))) s (LN.inv (𝟙 (Spec (CommRingCat.of k))) s) = LN.one (𝟙 (Spec (CommRingCat.of k))) from LN.mul_inv_cancel (𝟙 (Spec (CommRingCat.of k))) s,
      transl_one]

abbrev clpt (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) gN) : N := x.1 (IsLocalRing.closedPoint k)

theorem transl_clpt (x s : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) gN) :
    transl LN s (clpt x) = clpt (LN.mul (𝟙 (Spec (CommRingCat.of k))) s x) := by
  have h := comp_transl LN x s
  rw [const_pt] at h
  show (x.1 ≫ transl LN s) (IsLocalRing.closedPoint k) = _
  rw [h]

theorem transl_clpt_one (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) gN) :
    transl LN s (clpt (LN.one (𝟙 (Spec (CommRingCat.of k))))) = clpt s := by
  rw [transl_clpt, LN.mul_one]

end Maps

section Topology

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

theorem image_mem_irreducibleComponents (h : α ≃ₜ β) {Z : Set α}
    (hZ : Z ∈ irreducibleComponents α) : h '' Z ∈ irreducibleComponents β := by
  refine ⟨hZ.1.image h h.continuous.continuousOn, fun W hW hZW => ?_⟩
  have h1 : IsIrreducible (h.symm '' W) := hW.image h.symm h.symm.continuous.continuousOn
  have h2 : Z ⊆ h.symm '' W := by
    intro z hz
    exact ⟨h z, hZW ⟨z, hz, rfl⟩, h.symm_apply_apply z⟩
  have h3 : h.symm '' W ⊆ Z := hZ.2 h1 h2
  intro w hw
  refine ⟨h.symm w, h3 ⟨w, hw, rfl⟩, h.apply_symm_apply w⟩

theorem eq_of_mem_irreducibleComponents_of_subset {Z W : Set α} (hZ : Z ∈ irreducibleComponents α)
    (hW : IsIrreducible W) (hZW : Z ⊆ W) : W = Z :=
  Set.Subset.antisymm (hZ.2 hW hZW) hZW

end Topology

section Component

variable {k : Type u} [Field k] {N : Scheme.{u}} {gN : N ⟶ Spec (CommRingCat.of k)}

open AlgebraicGeometry.Scheme.IdealSheafData

abbrev redSub (Z : Closeds N) : Scheme.{u} := (vanishingIdeal Z).subscheme

abbrev redι (Z : Closeds N) : redSub Z ⟶ N := (vanishingIdeal Z).subschemeι

scoped instance isReduced_redSub (Z : Closeds N) : IsReduced (redSub Z) :=
  (AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal_and_le_ker Z).1

theorem range_redι (Z : Closeds N) : Set.range (redι Z) = (Z : Set N) := by
  rw [range_subschemeι]
  rfl

theorem redι_apply_mem (Z : Closeds N) (a : redSub Z) : redι Z a ∈ (Z : Set N) := by
  rw [← range_redι Z]
  exact ⟨a, rfl⟩

def redLift (Z : Closeds N) {T : Scheme.{u}} [IsReduced T] (f : T ⟶ N)
    (hf : Set.range f ⊆ Z) : T ⟶ redSub Z :=
  IsClosedImmersion.lift (redι Z) f (by
    rw [ker_subschemeι]
    exact (AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal_and_le_ker
      Z).2 f hf)

@[reassoc (attr := simp)]
theorem redLift_ι (Z : Closeds N) {T : Scheme.{u}} [IsReduced T] (f : T ⟶ N)
    (hf : Set.range f ⊆ Z) : redLift Z f hf ≫ redι Z = f :=
  IsClosedImmersion.lift_fac _ _ _

theorem irreducibleSpace_redSub {Z : Closeds N} (hZ : IsIrreducible (Z : Set N)) :
    IrreducibleSpace (redSub Z) := by
  have h : IsIrreducible (Set.range (redι Z)) := by rwa [range_redι]
  have e : Set.range (redι Z) ≃ₜ redSub Z :=
    ((redι Z).isEmbedding.toHomeomorph).symm
  haveI := Subtype.irreducibleSpace h
  exact e.irreducibleSpace_iff.mp inferInstance

theorem isIntegral_redSub {Z : Closeds N} (hZ : IsIrreducible (Z : Set N)) :
    IsIntegral (redSub Z) := by
  haveI := irreducibleSpace_redSub hZ
  exact isIntegral_of_irreducibleSpace_of_isReduced (redSub Z)

end Component

section Identity

variable {k : Type u} [Field k] {N : Scheme.{u}} {gN : N ⟶ Spec (CommRingCat.of k)}
  (LN : RelativeGroupLaw k gN)

-- [port] local notation `pt` removed (build-time syntax); its uses below are expanded to `(𝟙 (Spec (CommRingCat.of k)))`

def ratLift (Z : Closeds N) (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) gN) (hs : clpt s ∈ (Z : Set N)) :
    Spec (CommRingCat.of k) ⟶ redSub Z :=
  redLift Z s.1 (by
    rintro _ ⟨p, rfl⟩
    have : p = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    rw [this]; exact hs)

@[reassoc (attr := simp)]
theorem ratLift_ι (Z : Closeds N) (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) gN) (hs : clpt s ∈ (Z : Set N)) :
    ratLift Z s hs ≫ redι Z = s.1 :=
  redLift_ι _ _ _

theorem ratLift_over (Z : Closeds N) (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) gN) (hs : clpt s ∈ (Z : Set N)) :
    ratLift Z s hs ≫ redι Z ≫ gN = 𝟙 _ := by
  rw [ratLift_ι_assoc, s.2]

def mulMap (C₁ C₂ : Closeds N) : pullback (redι C₁ ≫ gN) (redι C₂ ≫ gN) ⟶ N :=
  (LN.mul (pullback.fst (redι C₁ ≫ gN) (redι C₂ ≫ gN) ≫ redι C₁ ≫ gN)
    ⟨pullback.fst _ _ ≫ redι C₁, by simp⟩
    ⟨pullback.snd _ _ ≫ redι C₂, by simpa using pullback.condition.symm⟩).1

theorem lift_mulMap (C₁ C₂ : Closeds N) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (a : T ⟶ redSub C₁) (b : T ⟶ redSub C₂) (ha : a ≫ redι C₁ ≫ gN = t)
    (hb : b ≫ redι C₂ ≫ gN = t) :
    pullback.lift a b (ha.trans hb.symm) ≫ mulMap LN C₁ C₂ =
      (LN.mul t ⟨a ≫ redι C₁, by simpa using ha⟩ ⟨b ≫ redι C₂, by simpa using hb⟩).1 := by
  have hψ : pullback.lift a b (ha.trans hb.symm) ≫
      (pullback.fst (redι C₁ ≫ gN) (redι C₂ ≫ gN) ≫ redι C₁ ≫ gN) = t := by
    rw [pullback.lift_fst_assoc, ha]
  have hnat := LN.mul_natural _ t (pullback.lift a b (ha.trans hb.symm)) hψ
    ⟨pullback.fst _ _ ≫ redι C₁, by simp⟩
    ⟨pullback.snd _ _ ≫ redι C₂, by simpa using pullback.condition.symm⟩
  have h1 : GoodReductionJacobian.schemeHomOverComp (pullback.lift a b (ha.trans hb.symm)) hψ
      (⟨pullback.fst _ _ ≫ redι C₁, by simp⟩ : SchemeHomOver _ gN) =
      ⟨a ≫ redι C₁, by simpa using ha⟩ :=
    Subtype.ext (by rw [GoodReductionJacobian.schemeHomOverComp_coe, ← Category.assoc,
      pullback.lift_fst])
  have h2 : GoodReductionJacobian.schemeHomOverComp (pullback.lift a b (ha.trans hb.symm)) hψ
      (⟨pullback.snd _ _ ≫ redι C₂, by simpa using pullback.condition.symm⟩ :
        SchemeHomOver _ gN) =
      ⟨b ≫ redι C₂, by simpa using hb⟩ :=
    Subtype.ext (by rw [GoodReductionJacobian.schemeHomOverComp_coe, ← Category.assoc,
      pullback.lift_snd])
  rw [h1, h2] at hnat
  exact congrArg Subtype.val hnat

theorem subset_range_mulMap_left (C₁ C₂ : Closeds N) (e₂ : clpt (LN.one (𝟙 (Spec (CommRingCat.of k)))) ∈ (C₂ : Set N)) :
    (C₁ : Set N) ⊆ Set.range (mulMap LN C₁ C₂) := by
  let e₂' : Spec (CommRingCat.of k) ⟶ redSub C₂ := ratLift C₂ (LN.one (𝟙 (Spec (CommRingCat.of k)))) e₂
  have hb : ((redι C₁ ≫ gN) ≫ e₂') ≫ redι C₂ ≫ gN = redι C₁ ≫ gN := by
    simp only [Category.assoc, e₂']
    rw [ratLift_over, Category.comp_id]
  have hj := lift_mulMap LN C₁ C₂ (redι C₁ ≫ gN) (𝟙 _) ((redι C₁ ≫ gN) ≫ e₂')
    (Category.id_comp _) hb
  have hone : (⟨((redι C₁ ≫ gN) ≫ e₂') ≫ redι C₂, by simpa using hb⟩ :
      SchemeHomOver (redι C₁ ≫ gN) gN) = LN.one (redι C₁ ≫ gN) := by
    apply Subtype.ext
    rw [← const_one LN, const_coe]
    simp [e₂']
  rw [hone, LN.mul_one] at hj
  have hj' : pullback.lift (𝟙 _) ((redι C₁ ≫ gN) ≫ e₂') ((Category.id_comp _).trans hb.symm) ≫
      mulMap LN C₁ C₂ = redι C₁ := hj.trans (Category.id_comp _)
  intro z hz
  have hz' : z ∈ Set.range (redι C₁) := by rw [range_redι]; exact hz
  obtain ⟨a, rfl⟩ := hz'
  exact ⟨pullback.lift (𝟙 _) ((redι C₁ ≫ gN) ≫ e₂') ((Category.id_comp _).trans hb.symm) a,
    by rw [← Scheme.Hom.comp_apply, hj']⟩

theorem subset_range_mulMap_right (C₁ C₂ : Closeds N) (e₁ : clpt (LN.one (𝟙 (Spec (CommRingCat.of k)))) ∈ (C₁ : Set N)) :
    (C₂ : Set N) ⊆ Set.range (mulMap LN C₁ C₂) := by
  let e₁' : Spec (CommRingCat.of k) ⟶ redSub C₁ := ratLift C₁ (LN.one (𝟙 (Spec (CommRingCat.of k)))) e₁
  have ha : ((redι C₂ ≫ gN) ≫ e₁') ≫ redι C₁ ≫ gN = redι C₂ ≫ gN := by
    simp only [Category.assoc, e₁']
    rw [ratLift_over, Category.comp_id]
  have hj := lift_mulMap LN C₁ C₂ (redι C₂ ≫ gN) ((redι C₂ ≫ gN) ≫ e₁') (𝟙 _)
    ha (Category.id_comp _)
  have hone : (⟨((redι C₂ ≫ gN) ≫ e₁') ≫ redι C₁, by simpa using ha⟩ :
      SchemeHomOver (redι C₂ ≫ gN) gN) = LN.one (redι C₂ ≫ gN) := by
    apply Subtype.ext
    rw [← const_one LN, const_coe]
    simp [e₁']
  rw [hone, LN.one_mul] at hj
  have hj' : pullback.lift ((redι C₂ ≫ gN) ≫ e₁') (𝟙 _) (ha.trans (Category.id_comp _).symm) ≫
      mulMap LN C₁ C₂ = redι C₂ := hj.trans (Category.id_comp _)
  intro z hz
  have hz' : z ∈ Set.range (redι C₂) := by rw [range_redι]; exact hz
  obtain ⟨b, rfl⟩ := hz'
  exact ⟨pullback.lift ((redι C₂ ≫ gN) ≫ e₁') (𝟙 _) (ha.trans (Category.id_comp _).symm) b,
    by rw [← Scheme.Hom.comp_apply, hj']⟩

variable [IsAlgClosed k] [LocallyOfFiniteType gN]

theorem isIrreducible_range_mulMap (C₁ C₂ : Closeds N) (h₁ : IsIrreducible (C₁ : Set N))
    (h₂ : IsIrreducible (C₂ : Set N)) : IsIrreducible (Set.range (mulMap LN C₁ C₂)) := by
  haveI : IsIntegral (redSub C₁) := isIntegral_redSub h₁
  haveI : IsIntegral (redSub C₂) := isIntegral_redSub h₂
  haveI : GeometricallyIntegral (redι C₁ ≫ gN) :=
    AlgebraicGeometry.geometricallyIntegral_of_isAlgClosed _
  haveI : IsLocallyNoetherian (redSub C₂) := LocallyOfFiniteType.isLocallyNoetherian (redι C₂ ≫ gN)
  haveI : IsIntegral (pullback (redι C₁ ≫ gN) (redι C₂ ≫ gN)) := inferInstance
  rw [← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ _).image _ (mulMap LN C₁ C₂).continuous.continuousOn

theorem eq_of_one_mem {Z₁ Z₂ : Set N} (h₁ : Z₁ ∈ irreducibleComponents N)
    (h₂ : Z₂ ∈ irreducibleComponents N) (e₁ : clpt (LN.one (𝟙 (Spec (CommRingCat.of k)))) ∈ Z₁)
    (e₂ : clpt (LN.one (𝟙 (Spec (CommRingCat.of k)))) ∈ Z₂) : Z₁ = Z₂ := by
  let C₁ : Closeds N := ⟨Z₁, isClosed_of_mem_irreducibleComponents _ h₁⟩
  let C₂ : Closeds N := ⟨Z₂, isClosed_of_mem_irreducibleComponents _ h₂⟩
  have hirr := isIrreducible_range_mulMap LN C₁ C₂ h₁.1 h₂.1
  obtain ⟨W, hW, hμW⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ hirr
  have hZ₁ : Z₁ ⊆ Set.range (mulMap LN C₁ C₂) := subset_range_mulMap_left LN C₁ C₂ e₂
  have hZ₂ : Z₂ ⊆ Set.range (mulMap LN C₁ C₂) := subset_range_mulMap_right LN C₁ C₂ e₁
  have hW1 : W = Z₁ := eq_of_mem_irreducibleComponents_of_subset h₁ hW.1 (hZ₁.trans hμW)
  have hW2 : W = Z₂ := eq_of_mem_irreducibleComponents_of_subset h₂ hW.1 (hZ₂.trans hμW)
  rw [← hW1, hW2]

include LN in

theorem eq_of_clpt_mem (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) gN) {Z Z' : Set N}
    (hZ : Z ∈ irreducibleComponents N) (hZ' : Z' ∈ irreducibleComponents N)
    (hx : clpt x ∈ Z) (hx' : clpt x ∈ Z') : Z = Z' := by
  letI := LN.pointGroup (𝟙 (Spec (CommRingCat.of k)))

  let s : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) gN := LN.inv (𝟙 (Spec (CommRingCat.of k))) x
  let h : N ≃ₜ N := (transl LN s).homeomorph
  have hs : h (clpt x) = clpt (LN.one (𝟙 (Spec (CommRingCat.of k)))) := by
    show transl LN s (clpt x) = _
    rw [transl_clpt, show LN.mul (𝟙 (Spec (CommRingCat.of k))) (LN.inv (𝟙 (Spec (CommRingCat.of k))) x) x = LN.one (𝟙 (Spec (CommRingCat.of k))) from LN.inv_mul_cancel (𝟙 (Spec (CommRingCat.of k))) x]
  have h1 := image_mem_irreducibleComponents h hZ
  have h2 := image_mem_irreducibleComponents h hZ'
  have e1 : clpt (LN.one (𝟙 (Spec (CommRingCat.of k)))) ∈ h '' Z := ⟨_, hx, hs⟩
  have e2 : clpt (LN.one (𝟙 (Spec (CommRingCat.of k)))) ∈ h '' Z' := ⟨_, hx', hs⟩
  have := eq_of_one_mem LN h1 h2 e1 e2
  exact h.injective.image_injective this

end Identity

end P2mGroupSchemeComponents
-- [port] was: p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem.P2mGroupSchemeComponents"
open scoped _root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem.P2mGroupSchemeComponents

open P2mGroupSchemeComponents in
theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {N : Scheme.{u}} {gN : N ⟶ Spec (CommRingCat.of k)}
    [LocallyOfFiniteType gN] (LN : RelativeGroupLaw k gN)
    (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) gN)
    {Z Z' : Set N} (hZ : Z ∈ irreducibleComponents N) (hZ' : Z' ∈ irreducibleComponents N)
    (hx : x.1 (IsLocalRing.closedPoint k) ∈ Z) (hx' : x.1 (IsLocalRing.closedPoint k) ∈ Z') :
    Z = Z' :=
  eq_of_clpt_mem LN x hZ hZ' hx hx'

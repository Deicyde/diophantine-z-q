/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
import ZInQKernel.Contrib.CloudB3W13.Dictionary.D7.Defs
import ZInQKernel.Contrib.CloudB3W13.Dictionary.D7.Glue

/-!
# W13 dictionary D7: the universal family over a fine moduli scheme

Given a fine moduli scheme `M → Spec 𝒪` of the FLT problem `(Λ, 1, 3)` with `3` a unit:
* over every affine open `U` of `M`, `ptF_surjective` gives an object `u_U` over `Γ(M, U)` whose
  moduli point is `U ↪ M`;
* for `U ≤ V`, base change (`BCInput`), `ptF_pullback` and `ptF_injective` give a level pullback
  `u_U.A ⟶ u_V.A`. It is unique by rigidity (`RigidInput`), which makes the transition maps
  strictly functorial;
* the resulting `LocalFamily` (`Glue.lean`) glues to a kernel `QMFamily` over `M`;
* at every field point `(ptF K s u).1`, `u` is the fibre of the family (`IsFibreOf`).

`d7_of_inputs` derives `D7_Obligation` from `BCInput`, `RigidInput` and `DimInput`, which are
proved from FLT source theorems in `BaseChange.lean`, `Rigid.lean` and `Dim.lean`. No other
hypothesis is used. The separatedness, finiteness and characteristic hypotheses of
`D7_Obligation` are not needed.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB2Shimura.Dictionary.D7

open CategoryTheory AlgebraicGeometry Limits Opposite
open scoped Quaternion
open ZInQ.Contrib.CloudW03NeronSurj ZInQ.Contrib.CloudW03NeronSurj.FLT
open ZInQ.Contrib.CloudW03NeronSurj.FLT.NeronModelInfra
open ZInQ.Contrib.CloudW03NeronSurj.FLT.GoodReductionJacobian
open ZInQ.Contrib.CloudW03NeronSurj.FLT.CerednikDrinfeld.QM
open ZInQ.Contrib.CloudB2Shimura.Dictionary

variable {𝒪 : Type} [CommRing 𝒪] {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of 𝒪)}
  {ptF : PtF 𝒪 πM}

/-- The moduli point of the affine open `U`. -/
abbrev sU (πM : M ⟶ Spec (CommRingCat.of 𝒪)) (U : M.affineOpens) :
    Spec (CommRingCat.of Γ(M, U.1)) ⟶ Spec (CommRingCat.of 𝒪) :=
  U.2.fromSpec ≫ πM

/-- Restriction of sections. -/
abbrev res {U V : M.affineOpens} (h : U ≤ V) : Γ(M, V.1) →+* Γ(M, U.1) :=
  (M.presheaf.map (homOfLE (show U.1 ≤ V.1 from h)).op).hom

lemma spec_res {U V : M.affineOpens} (h : U ≤ V) :
    Spec.map (CommRingCat.ofHom (res h)) =
      Spec.map (M.presheaf.map (homOfLE (show U.1 ≤ V.1 from h)).op) := by
  rw [CommRingCat.ofHom_hom]

lemma res_fromSpec {U V : M.affineOpens} (h : U ≤ V) :
    Spec.map (CommRingCat.ofHom (res h)) ≫ V.2.fromSpec = U.2.fromSpec := by
  rw [spec_res]
  exact IsAffineOpen.map_fromSpec (U := V.1) V.2 U.2 (homOfLE (show U.1 ≤ V.1 from h)).op

lemma isoSpec_nat {U V : M.affineOpens} (h : U ≤ V) :
    U.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (res h)) = M.homOfLE h ≫ V.2.isoSpec.hom := by
  have e1 : V.2.isoSpec.inv ≫ V.1.ι = V.2.fromSpec := IsAffineOpen.isoSpec_inv_ι V.2
  have e2 : U.2.isoSpec.hom ≫ U.2.fromSpec = U.1.ι := IsAffineOpen.isoSpec_hom_fromSpec U.2
  have e3 : V.2.isoSpec.hom ≫ V.2.fromSpec = V.1.ι := IsAffineOpen.isoSpec_hom_fromSpec V.2
  rw [← cancel_mono (V.2.isoSpec.inv ≫ V.1.ι)]
  rw [Category.assoc, e1, Category.assoc, res_fromSpec, e2, e3, Scheme.homOfLE_ι]

lemma res_inv_nat {U V : M.affineOpens} (h : U ≤ V) :
    Spec.map (CommRingCat.ofHom (res h)) ≫ V.2.isoSpec.inv = U.2.isoSpec.inv ≫ M.homOfLE h := by
  rw [Iso.eq_inv_comp, ← Category.assoc, isoSpec_nat, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

lemma res_refl (U : M.affineOpens) : res (le_refl U) = RingHom.id _ := by
  rw [res, show homOfLE (show U.1 ≤ U.1 from le_refl U) = 𝟙 U.1 from Subsingleton.elim _ _,
    op_id, M.presheaf.map_id, CommRingCat.hom_id]

lemma res_trans {U V W : M.affineOpens} (h₁ : U ≤ V) (h₂ : V ≤ W) :
    (res h₁).comp (res h₂) = res (h₁.trans h₂) := by
  rw [res, res, res, ← CommRingCat.hom_comp, ← Functor.map_comp, ← op_comp]
  rfl

lemma isUnit_three (πM : M ⟶ Spec (CommRingCat.of 𝒪)) (h3 : IsUnit ((3 : ℕ) : 𝒪))
    (U : M.affineOpens) : IsUnit ((3 : ℕ) : Γ(M, U.1)) := by
  have := h3.map (Spec.preimage (sU πM U)).hom
  rwa [map_natCast] at this

section Construction

variable (hM : IsFineModuli Λ 1 3 M πM ptF)
include hM

lemma exists_uU (U : M.affineOpens) :
    ∃ u : L3 Γ(M, U.1), ptF Γ(M, U.1) (sU πM U) u = ⟨U.2.fromSpec, rfl⟩ :=
  hM.ptF_surjective _ _ ⟨U.2.fromSpec, rfl⟩

/-- The chosen object over the affine open `U` (its moduli point is `U ↪ M`). -/
def uU (U : M.affineOpens) : L3 Γ(M, U.1) := (exists_uU hM U).choose

lemma ptF_uU (U : M.affineOpens) : (ptF Γ(M, U.1) (sU πM U) (uU hM U)).1 = U.2.fromSpec :=
  congrArg Subtype.val (exists_uU hM U).choose_spec

variable (hBC : BCInput)
include hBC

lemma exists_trans {U V : M.affineOpens} (h : U ≤ V) :
    ∃ g : (uU hM U).1.A ⟶ (uU hM V).1.A, IsLevelPB (res h) (uU hM V) (uU hM U) g := by
  obtain ⟨u', hu'⟩ := hBC _ _ (res h) (uU hM V)
  have hs : Spec.map (CommRingCat.ofHom (res h)) ≫ sU πM V = sU πM U := by
    rw [sU, sU, ← Category.assoc, res_fromSpec]
  have hpt : ptF Γ(M, U.1) (sU πM U) (uU hM U) = ptF Γ(M, U.1) (sU πM U) u' := by
    apply Subtype.ext
    rw [hM.ptF_pullback _ _ (res h) (sU πM V) (sU πM U) hs (uU hM V) u' hu', ptF_uU, ptF_uU,
      res_fromSpec]
  obtain ⟨e, he, hmul, hact, -, hP⟩ := hM.ptF_injective _ _ (uU hM U) u' hpt
  obtain ⟨g, hg⟩ := exists_isLevelPB_of_isPullback hu'
  exact ⟨e.hom ≫ g,
    isLevelPB_congr (hg.comp (isLevelPB_of_iso e he hmul hact hP)) (RingHom.id_comp _)⟩

/-- The transition map `u_U.A ⟶ u_V.A`. -/
def trans {U V : M.affineOpens} (h : U ≤ V) : (uU hM U).1.A ⟶ (uU hM V).1.A :=
  (exists_trans hM hBC h).choose

lemma trans_spec {U V : M.affineOpens} (h : U ≤ V) :
    IsLevelPB (res h) (uU hM V) (uU hM U) (trans hM hBC h) :=
  (exists_trans hM hBC h).choose_spec

variable (hR : RigidInput) (hD : DimInput) (h3 : IsUnit ((3 : ℕ) : 𝒪))
include hR hD h3

/-- **The local family over the affine opens of `M`.** -/
abbrev localFamily : LocalFamily M where
  X U := (uU hM U).1.A
  p U := (uU hM U).1.f ≫ U.2.isoSpec.inv
  τ h := trans hM hBC h
  τ_id U := IsLevelPB.unique hR (isUnit_three πM h3 U) (trans_spec hM hBC (le_refl U))
    (isLevelPB_congr (isLevelPB_id _) (res_refl U).symm)
  τ_comp h₁ h₂ := IsLevelPB.unique hR (isUnit_three πM h3 _)
    (isLevelPB_congr ((trans_spec hM hBC h₂).comp (trans_spec hM hBC h₁)) (res_trans h₁ h₂))
    (trans_spec hM hBC (h₁.trans h₂))
  pb {U V} h := by
    refine IsPullback.of_iso (trans_spec hM hBC h).1 (Iso.refl _) (Iso.refl _)
      U.2.isoSpec.symm V.2.isoSpec.symm ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp
    · simp only [Iso.symm_hom]
      exact res_inv_nat h
  iota a U := (uU hM U).1.act (toΛ a)
  iota_p a U := by
    rw [← Category.assoc, (uU hM U).1.act_over]
  iota_τ a {U V} h := ((trans_spec hM hBC h).2.2.1 (toΛ a)).symm
  sec a U := U.2.isoSpec.hom ≫ (uU hM U).2.P.1 ≫ (uU hM U).1.act (toΛ a)
  sec_p a U := by
    simp only [Category.assoc]
    rw [← Category.assoc ((uU hM U).1.act (toΛ a)), (uU hM U).1.act_over,
      ← Category.assoc ((uU hM U).2.P.1), (uU hM U).2.P.2, Category.id_comp, Iso.hom_inv_id]
  sec_τ a {U V} h := by
    simp only [Category.assoc]
    rw [(trans_spec hM hBC h).2.2.1 (toΛ a), ← Category.assoc ((uU hM U).2.P.1),
      (trans_spec hM hBC h).2.2.2]
    simp only [Category.assoc]
    rw [← Category.assoc U.2.isoSpec.hom, isoSpec_nat, Category.assoc]
  proper U := by
    haveI := (uU hM U).1.bundle.proper
    infer_instance
  smooth U := by
    haveI := hD _ (uU hM U).1
    show SmoothOfRelativeDimension (2 + 0) _
    infer_instance

/-- **Fibres of the universal family at field points.** -/
theorem fibre (K : Type) [Field K] (s : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of 𝒪))
    (u : L3 K) :
    ∃ g : u.1.A ⟶ (localFamily hM hBC hR hD h3).glued,
      IsPullback g u.1.f (localFamily hM hBC hR hD h3).toBase (ptF K s u).1 ∧
      (∀ x : ↥Λ, ∀ a : LeafQM.O, x = toΛ a →
        u.1.act x ≫ g = g ≫ (localFamily hM hBC hR hD h3).iotaG a) ∧
      (∀ a : LeafQM.O, (u.2.P.1 ≫ u.1.act (toΛ a)) ≫ g =
        (ptF K s u).1 ≫ (localFamily hM hBC hR hD h3).etaG a) := by
  set F := localFamily hM hBC hR hD h3 with hF
  set y := (ptF K s u).1 with hy
  -- an affine open containing the image of `Spec K`
  obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  let U : M.affineOpens := M.directedAffineCover.idx (y.base pt)
  have hU : y.base pt ∈ Set.range U.1.ι.base := M.directedAffineCover.covers (y.base pt)
  have hrange : Set.range y.base ⊆ Set.range U.1.ι.base := by
    rintro _ ⟨z, rfl⟩
    rwa [Subsingleton.elim z pt]
  let y' : Spec (CommRingCat.of K) ⟶ (U.1 : Scheme.{0}) := IsOpenImmersion.lift U.1.ι y hrange
  have hy' : y' ≫ U.1.ι = y := IsOpenImmersion.lift_fac _ _ _
  let ψ : CommRingCat.of Γ(M, U.1) ⟶ CommRingCat.of K := Spec.preimage (y' ≫ U.2.isoSpec.hom)
  have hψ : Spec.map (CommRingCat.ofHom ψ.hom) = y' ≫ U.2.isoSpec.hom := by
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  -- base change of `u_U` to `K`, isomorphic to `u`
  obtain ⟨v, hv⟩ := hBC _ _ ψ.hom (uU hM U)
  have hyπ : y ≫ πM = s := (ptF K s u).2
  have e2 : U.2.isoSpec.hom ≫ U.2.fromSpec = U.1.ι := IsAffineOpen.isoSpec_hom_fromSpec U.2
  have hs : Spec.map (CommRingCat.ofHom ψ.hom) ≫ sU πM U = s := by
    rw [hψ, sU]
    simp only [Category.assoc]
    rw [← Category.assoc U.2.isoSpec.hom, e2, ← Category.assoc, hy', hyπ]
  have hpt : ptF K s u = ptF K s v := by
    apply Subtype.ext
    rw [hM.ptF_pullback _ _ ψ.hom (sU πM U) s hs (uU hM U) v hv, ptF_uU, hψ, Category.assoc,
      e2, hy']
  obtain ⟨e, he, hmul, hact, -, hP⟩ := hM.ptF_injective _ _ u v hpt
  obtain ⟨gv, hgv⟩ := exists_isLevelPB_of_isPullback hv
  have hG := isLevelPB_congr (hgv.comp (isLevelPB_of_iso e he hmul hact hP)) (RingHom.id_comp _)
  obtain ⟨hGpb, -, hGact, hGP⟩ := hG
  refine ⟨(e.hom ≫ gv) ≫ F.ι U, ?_, ?_, ?_⟩
  · have h1 : IsPullback (e.hom ≫ gv) u.1.f (F.p U) y' := by
      refine IsPullback.of_iso hGpb (Iso.refl _) (Iso.refl _) (Iso.refl _) U.2.isoSpec.symm
        ?_ ?_ ?_ ?_
      · simp
      · simp
      · rw [Iso.refl_hom, Category.id_comp]; rfl
      · simp only [Iso.symm_hom, Iso.refl_hom, Category.id_comp]
        rw [hψ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have h2 := h1.paste_horiz (F.isPullback_ι U).flip
    rwa [hy'] at h2
  · intro x a hx
    subst hx
    have h1 : F.ι U ≫ F.iotaG a = (uU hM U).1.act (toΛ a) ≫ F.ι U := F.ι_iotaG a U
    calc u.1.act (toΛ a) ≫ (e.hom ≫ gv) ≫ F.ι U
        = (u.1.act (toΛ a) ≫ e.hom ≫ gv) ≫ F.ι U := by simp only [Category.assoc]
      _ = ((e.hom ≫ gv) ≫ (uU hM U).1.act (toΛ a)) ≫ F.ι U := by rw [hGact]
      _ = (e.hom ≫ gv) ≫ ((uU hM U).1.act (toΛ a) ≫ F.ι U) := by simp only [Category.assoc]
      _ = ((e.hom ≫ gv) ≫ F.ι U) ≫ F.iotaG a := by rw [← h1]; simp only [Category.assoc]
  · intro a
    have h2 : U.1.ι ≫ F.etaG a =
        (U.2.isoSpec.hom ≫ (uU hM U).2.P.1 ≫ (uU hM U).1.act (toΛ a)) ≫ F.ι U := F.ι_etaG a U
    calc (u.2.P.1 ≫ u.1.act (toΛ a)) ≫ (e.hom ≫ gv) ≫ F.ι U
        = (u.2.P.1 ≫ (u.1.act (toΛ a) ≫ e.hom ≫ gv)) ≫ F.ι U := by simp only [Category.assoc]
      _ = (u.2.P.1 ≫ ((e.hom ≫ gv) ≫ (uU hM U).1.act (toΛ a))) ≫ F.ι U := by rw [hGact]
      _ = ((u.2.P.1 ≫ e.hom ≫ gv) ≫ (uU hM U).1.act (toΛ a)) ≫ F.ι U := by
          simp only [Category.assoc]
      _ = ((Spec.map (CommRingCat.ofHom ψ.hom) ≫ (uU hM U).2.P.1) ≫
            (uU hM U).1.act (toΛ a)) ≫ F.ι U := by rw [hGP]
      _ = y' ≫ (U.2.isoSpec.hom ≫ (uU hM U).2.P.1 ≫ (uU hM U).1.act (toΛ a)) ≫ F.ι U := by
          rw [hψ]; simp only [Category.assoc]
      _ = y' ≫ U.1.ι ≫ F.etaG a := by rw [h2]
      _ = y ≫ F.etaG a := by rw [← Category.assoc, hy']

end Construction

/-- **D7 from the three inputs.** -/
theorem d7_of_inputs (hBC : BCInput) (hR : RigidInput) (hD : DimInput) : D7_Obligation := by
  intro 𝒪 _ _ h3 M πM ptF hM _ _ _ _
  refine ⟨(localFamily hM hBC hR hD h3).toQMFamily, ?_⟩
  intro K _ _ s u h hs q e hpk
  obtain ⟨g, hpb, hact, hP⟩ := fibre hM hBC hR hD h3 K s u
  refine ⟨g, hpb, ?_, ?_⟩
  · intro a
    rw [hpk.1 a]
    exact hact (toΛ a) a rfl
  · intro a
    rw [hpk.2 a]
    exact hP a

end ZInQ.Contrib.CloudB2Shimura.Dictionary.D7

import ZInQKernel.Contrib.OneProof.PicDictionary
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.Limits.Objects
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.Limits.FiniteMaps
import ZInQKernel.Contrib.CloudW06PoincareRigidity.AdjoinFinset
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.Quasicoherent
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.FinitePresentation

/-! # piclft (III): spreading out invertible sheaves along directed inverse limits -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits Opposite
open Scheme.Modules

set_option linter.style.haveILetI false

namespace PicLFT

section Triv

variable {X Y : Scheme.{0}}

/-- `M` is trivial on the open `U`. -/
def Triv (M : X.Modules) (U : X.Opens) : Prop :=
  Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)

lemma triv_of_iso {M N : X.Modules} (e : M ≅ N) {U : X.Opens} (h : Triv M U) : Triv N U :=
  ⟨(Scheme.Modules.pullback U.ι).mapIso e.symm ≪≫ h.some⟩

lemma triv_mono {M : X.Modules} {U U' : X.Opens} (hle : U' ≤ U) (h : Triv M U) : Triv M U' :=
  ⟨(pullbackCompOfEq (X.homOfLE hle) U.ι U'.ι (X.homOfLE_ι hle) M).symm ≪≫
    (Scheme.Modules.pullback (X.homOfLE hle)).mapIso h.some ≪≫ pullbackObjUnitIso _⟩

lemma triv_pullback (f : Y ⟶ X) {M : X.Modules} {U : X.Opens} (h : Triv M U) :
    Triv ((Scheme.Modules.pullback f).obj M) (f ⁻¹ᵁ U) :=
  ⟨pullbackCompOfEq (f ⁻¹ᵁ U).ι f _ rfl M ≪≫
    (pullbackCompOfEq (f ∣_ U) U.ι ((f ⁻¹ᵁ U).ι ≫ f) (morphismRestrict_ι f U) M).symm ≪≫
    (Scheme.Modules.pullback (f ∣_ U)).mapIso h.some ≪≫ pullbackObjUnitIso _⟩

end Triv

/-! ## (L2) triviality on one affine open descends to a finite stage -/

lemma pullbackCompOfEq_naturality {X Y Z : Scheme.{0}} (g : Z ⟶ Y) (f : Y ⟶ X) (fg : Z ⟶ X)
    (h : g ≫ f = fg) {M N : X.Modules} (φ : M ⟶ N) :
    (Scheme.Modules.pullback g).map ((Scheme.Modules.pullback f).map φ) ≫
        (pullbackCompOfEq g f fg h N).hom =
      (pullbackCompOfEq g f fg h M).hom ≫ (Scheme.Modules.pullback fg).map φ := by
  simp only [pullbackCompOfEq, Iso.trans_hom, Iso.app_hom]
  rw [← Category.assoc]
  erw [(pullbackComp g f).hom.naturality φ]
  rw [Category.assoc, Category.assoc]
  erw [(pullbackCongr h).hom.naturality φ]

lemma qcOfFp {X : Scheme.{0}} (M : X.Modules) [M.IsFinitePresentation] : M.IsQuasicoherent :=
  (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M).choose.isQuasicoherent

/-- Two-step transition pullbacks along a preorder diagram. -/
def pbTrans {T : Type} [Preorder T] (P : Tᵒᵖ ⥤ Scheme.{0}) {a b c : T} (hab : a ≤ b) (hbc : b ≤ c)
    (M : (P.obj (op a)).Modules) :
    (Scheme.Modules.pullback (P.map (homOfLE hbc).op)).obj
        ((Scheme.Modules.pullback (P.map (homOfLE hab).op)).obj M) ≅
      (Scheme.Modules.pullback (P.map (homOfLE (hab.trans hbc)).op)).obj M :=
  pullbackCompOfEq _ _ _ (by rw [← P.map_comp]; rfl) M

set_option maxHeartbeats 1600000 in
/-- **Generic core**: an isomorphism between the pullbacks to an affine limit of two finitely presented modules at
stage `a` descends to an isomorphism at some later stage. -/
theorem exists_iso_stage {T : Type} [Preorder T] [Nonempty T] [IsDirected T (· ≤ ·)]
    (P : Tᵒᵖ ⥤ Scheme.{0}) [∀ j, IsAffine (P.obj j)] (Pc : Cone P) (hPc : IsLimit Pc) [IsAffine Pc.pt]
    (a : T) (S0 U0 : (P.obj (op a)).Modules) [S0.IsFinitePresentation] [U0.IsFinitePresentation]
    (e : (Scheme.Modules.pullback (Pc.π.app (op a))).obj S0 ≅ (Scheme.Modules.pullback (Pc.π.app (op a))).obj U0) :
    ∃ (b : T) (h : a ≤ b), Nonempty ((Scheme.Modules.pullback (P.map (homOfLE h).op)).obj S0 ≅
      (Scheme.Modules.pullback (P.map (homOfLE h).op)).obj U0) := by
  haveI : S0.IsQuasicoherent := qcOfFp S0
  haveI : U0.IsQuasicoherent := qcOfFp U0
  -- first descent `S0 → U0`
  obtain ⟨j1, h01, f, hf⟩ := exists_hom_of_affine_limit P Pc hPc a S0 U0 e.hom
  let t01 := P.map (homOfLE h01).op
  let cS1 := pullbackCompOfEq (Pc.π.app (op j1)) t01 (Pc.π.app (op a)) (Pc.w (homOfLE h01).op) S0
  let cU1 := pullbackCompOfEq (Pc.π.app (op j1)) t01 (Pc.π.app (op a)) (Pc.w (homOfLE h01).op) U0
  let F1 := (Scheme.Modules.pullback (Pc.π.app (op j1))).map f
  have hF1 : F1 = cS1.hom ≫ e.hom ≫ cU1.inv := by
    exact ((Iso.eq_comp_inv cU1).mpr hf).trans (Category.assoc _ _ _)
  haveI : IsIso F1 := by rw [hF1]; infer_instance
  let S1 := (Scheme.Modules.pullback t01).obj U0
  let T1 := (Scheme.Modules.pullback t01).obj S0
  haveI : S1.IsFinitePresentation := isFinitePresentation_pullback _ _
  haveI : S1.IsQuasicoherent := qcOfFp S1
  haveI : T1.IsFinitePresentation := isFinitePresentation_pullback _ _
  haveI : T1.IsQuasicoherent := qcOfFp T1
  -- second descent `S1 → T1`
  obtain ⟨j2, h12, g, hg⟩ := exists_hom_of_affine_limit P Pc hPc j1 S1 T1 (inv F1)
  let t12 := P.map (homOfLE h12).op
  let c2 := fun X : (P.obj (op j1)).Modules =>
    pullbackCompOfEq (Pc.π.app (op j2)) t12 (Pc.π.app (op j1)) (Pc.w (homOfLE h12).op) X
  let f2 := (Scheme.Modules.pullback t12).map f
  have hF2 : (Scheme.Modules.pullback (Pc.π.app (op j2))).map f2 = (c2 T1).hom ≫ F1 ≫ (c2 S1).inv := by
    exact ((Iso.eq_comp_inv (c2 S1)).mpr (pullbackCompOfEq_naturality _ _ _ _ f)).trans (Category.assoc _ _ _)
  have hG : (Scheme.Modules.pullback (Pc.π.app (op j2))).map g = (c2 S1).hom ≫ inv F1 ≫ (c2 T1).inv := by
    exact ((Iso.eq_comp_inv (c2 T1)).mpr hg).trans (Category.assoc _ _ _)
  have eq1 : (Scheme.Modules.pullback (Pc.π.app (op j2))).map (f2 ≫ g) =
      (Scheme.Modules.pullback (Pc.π.app (op j2))).map (𝟙 _) := by
    rw [CategoryTheory.Functor.map_comp, hF2, hG, CategoryTheory.Functor.map_id]; simp
  have eq2 : (Scheme.Modules.pullback (Pc.π.app (op j2))).map (g ≫ f2) =
      (Scheme.Modules.pullback (Pc.π.app (op j2))).map (𝟙 _) := by
    rw [CategoryTheory.Functor.map_comp, hF2, hG, CategoryTheory.Functor.map_id]; simp
  -- equalities at finite stages
  haveI : ((Scheme.Modules.pullback t12).obj T1).IsFinitePresentation := isFinitePresentation_pullback _ _
  haveI : ((Scheme.Modules.pullback t12).obj T1).IsQuasicoherent := qcOfFp _
  haveI : ((Scheme.Modules.pullback t12).obj S1).IsFinitePresentation := isFinitePresentation_pullback _ _
  haveI : ((Scheme.Modules.pullback t12).obj S1).IsQuasicoherent := qcOfFp _
  obtain ⟨j3, h23, E1⟩ := exists_hom_eq_of_affine_limit P Pc hPc j2 (f2 ≫ g) (𝟙 _) eq1
  let t23 := P.map (homOfLE h23).op
  let a := (Scheme.Modules.pullback t23).map (g ≫ f2)
  have eq3 : (Scheme.Modules.pullback (Pc.π.app (op j3))).map a =
      (Scheme.Modules.pullback (Pc.π.app (op j3))).map (𝟙 _) := by
    let c3 := pullbackCompOfEq (Pc.π.app (op j3)) t23 (Pc.π.app (op j2)) (Pc.w (homOfLE h23).op)
      ((Scheme.Modules.pullback t12).obj S1)
    have := pullbackCompOfEq_naturality (Pc.π.app (op j3)) t23 (Pc.π.app (op j2))
      (Pc.w (homOfLE h23).op) (g ≫ f2)
    rw [eq2, CategoryTheory.Functor.map_id, Category.comp_id, ← Iso.eq_comp_inv, Iso.hom_inv_id] at this
    rw [this, CategoryTheory.Functor.map_id]
  haveI : ((Scheme.Modules.pullback t23).obj ((Scheme.Modules.pullback t12).obj S1)).IsFinitePresentation :=
    isFinitePresentation_pullback _ _
  haveI : ((Scheme.Modules.pullback t23).obj ((Scheme.Modules.pullback t12).obj S1)).IsQuasicoherent :=
    qcOfFp _
  obtain ⟨j4, h34, E2⟩ := exists_hom_eq_of_affine_limit P Pc hPc j3 a (𝟙 _) eq3
  let t34 := P.map (homOfLE h34).op
  let iso4 : (Scheme.Modules.pullback t34).obj ((Scheme.Modules.pullback t23).obj
      ((Scheme.Modules.pullback t12).obj T1)) ≅ (Scheme.Modules.pullback t34).obj
      ((Scheme.Modules.pullback t23).obj ((Scheme.Modules.pullback t12).obj S1)) :=
    { hom := (Scheme.Modules.pullback t34).map ((Scheme.Modules.pullback t23).map f2)
      inv := (Scheme.Modules.pullback t34).map ((Scheme.Modules.pullback t23).map g)
      hom_inv_id := by
        rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, E1, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
      inv_hom_id := by
        rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
        change (Scheme.Modules.pullback t34).map a = _
        rw [E2, CategoryTheory.Functor.map_id] }
  refine ⟨j4, h01.trans (h12.trans (h23.trans h34)), ⟨?_⟩⟩
  exact (pbTrans P (h01.trans (h12.trans h23)) h34 S0).symm ≪≫
    (Scheme.Modules.pullback t34).mapIso ((pbTrans P (h01.trans h12) h23 S0).symm ≪≫
      (Scheme.Modules.pullback t23).mapIso (pbTrans P h01 h12 S0).symm) ≪≫ iso4 ≪≫
    (Scheme.Modules.pullback t34).mapIso ((Scheme.Modules.pullback t23).mapIso (pbTrans P h01 h12 U0) ≪≫
      pbTrans P (h01.trans h12) h23 U0) ≪≫ pbTrans P (h01.trans (h12.trans h23)) h34 U0

theorem triv_stage {I : Type} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{0}) [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c) (i : I) (W : (D.obj (op i)).Opens) (hW : IsAffineOpen W)
    (M : (D.obj (op i)).Modules) [M.IsFinitePresentation]
    (hT : Triv ((Scheme.Modules.pullback (c.π.app (op i))).obj M) (c.π.app (op i) ⁻¹ᵁ W)) :
    ∃ (j : I) (h : i ≤ j),
      Triv ((Scheme.Modules.pullback (D.map (homOfLE h).op)).obj M) (D.map (homOfLE h).op ⁻¹ᵁ W) := by
  classical
  let Tl := {j : I // i ≤ j}
  haveI : Nonempty Tl := ⟨⟨i, le_rfl⟩⟩
  haveI : IsDirectedOrder Tl := ⟨by
    intro a b
    obtain ⟨k, hak, hbk⟩ := exists_ge_ge a.val b.val
    exact ⟨⟨k, a.property.trans hak⟩, hak, hbk⟩⟩
  let inc : Tl ⥤ I := (Subtype.mono_coe (fun j : I ↦ i ≤ j)).functor
  haveI : inc.Final := (Monotone.final_functor_iff _).mpr (by
    intro j
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    exact ⟨⟨k, hik⟩, hjk⟩)
  let Dt : Tlᵒᵖ ⥤ Scheme.{0} := inc.op ⋙ D
  let ct : Cone Dt := c.whisker inc.op
  have hct : IsLimit ct := (Functor.Initial.isLimitWhiskerEquiv inc.op c).symm hc
  let tr : Dt ⟶ (Functor.const Tlᵒᵖ).obj (D.obj (op i)) :=
    { app := fun j ↦ D.map (homOfLE j.unop.property).op
      naturality := by
        intro a b e
        change D.map (inc.op.map e) ≫ D.map _ = D.map _ ≫ 𝟙 _
        rw [Category.comp_id, ← D.map_comp]
        rfl }
  have fact : ∀ j, ct.π.app j ≫ tr.app j = c.π.app (op i) := fun j => c.w (homOfLE j.unop.property).op
  haveI : IsConnected Tlᵒᵖ := IsCofiltered.isConnected _
  let P := preimageDiagram Dt tr W
  let Pc := preimageCone Dt tr ct (c.π.app (op i)) fact W
  have hPc : IsLimit Pc := isLimit_preimageCone Dt tr ct _ fact hct W
  haveI : ∀ j, IsAffine (P.obj j) := fun j => hW.preimage (tr.app j)
  haveI : IsAffineHom (c.π.app (op i)) := isAffineHom_π_app D c hc (op i)
  haveI : IsAffine Pc.pt := hW.preimage (c.π.app (op i))
  let i₀ : Tl := ⟨i, le_rfl⟩
  let ιP := preimageDiagramι Dt tr W
  let S0 : (P.obj (op i₀)).Modules := (Scheme.Modules.pullback (ιP.app (op i₀))).obj M
  let U0 : (P.obj (op i₀)).Modules := SheafOfModules.unit _
  have h1 : Pc.π.app (op i₀) ≫ ιP.app (op i₀) = (c.π.app (op i) ⁻¹ᵁ W).ι ≫ c.π.app (op i) :=
    restrictPreimage_ι (ct.π.app (op i₀)) (fact (op i₀)) le_rfl
  obtain ⟨e⟩ : Nonempty ((Scheme.Modules.pullback (Pc.π.app (op i₀))).obj S0 ≅
      (Scheme.Modules.pullback (Pc.π.app (op i₀))).obj U0) := ⟨
    pullbackCompOfEq (Pc.π.app (op i₀)) (ιP.app (op i₀)) _ h1 M ≪≫
      (pullbackCompOfEq (c.π.app (op i) ⁻¹ᵁ W).ι (c.π.app (op i)) _ rfl M).symm ≪≫ hT.some ≪≫
      (pullbackObjUnitIso _).symm⟩
  haveI : S0.IsFinitePresentation := isFinitePresentation_pullback _ _
  obtain ⟨b, hb, ⟨E⟩⟩ := exists_iso_stage P Pc hPc i₀ S0 U0 e
  refine ⟨b.val, b.property, ⟨?_⟩⟩
  have hB : P.map (homOfLE hb).op ≫ ιP.app (op i₀) =
      (D.map (homOfLE b.property).op ⁻¹ᵁ W).ι ≫ D.map (homOfLE b.property).op :=
    ιP.naturality (homOfLE hb).op
  exact pullbackCompOfEq _ _ _ rfl M ≪≫ (pullbackCongr hB.symm).app M ≪≫
    (pullbackCompOfEq (P.map (homOfLE hb).op) (ιP.app (op i₀)) _ rfl M).symm ≪≫ E ≪≫
    pullbackObjUnitIso _

/-! ## (L3) invertibility descends to a finite stage -/

theorem invAtStage {I : Type} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{0}) [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] (c : Cone D) (hc : IsLimit c) (i0 : I)
    (M0 : (D.obj (op i0)).Modules) [M0.IsFinitePresentation]
    (hL : ((Scheme.Modules.pullback (c.π.app (op i0))).obj M0).IsInvertible) :
    ∃ (j : I) (h : i0 ≤ j), ((Scheme.Modules.pullback (D.map (homOfLE h).op)).obj M0).IsInvertible := by
  classical
  let Mj : ∀ j : I, i0 ≤ j → (D.obj (op j)).Modules := fun j h => (Scheme.Modules.pullback (D.map (homOfLE h).op)).obj M0
  have hMcomp : ∀ (j k : I) (hj : i0 ≤ j) (hjk : j ≤ k),
      Nonempty ((Scheme.Modules.pullback (D.map (homOfLE hjk).op)).obj (Mj j hj) ≅ Mj k (hj.trans hjk)) :=
    fun j k hj hjk => ⟨pullbackCompOfEq _ _ _ (by rw [← D.map_comp]; rfl) M0⟩
  have hMlim : ∀ (j : I) (hj : i0 ≤ j),
      Nonempty ((Scheme.Modules.pullback (c.π.app (op j))).obj (Mj j hj) ≅ (Scheme.Modules.pullback (c.π.app (op i0))).obj M0) :=
    fun j hj => ⟨pullbackCompOfEq _ _ _ (c.w _) M0⟩
  have hgood : ∀ x : c.pt, ∃ (j : I) (hj : i0 ≤ j) (O : (D.obj (op j)).Opens),
      Triv (Mj j hj) O ∧ x ∈ c.π.app (op j) ⁻¹ᵁ O := by
    intro x
    obtain ⟨U, hxU, hU⟩ := (isInvertible_iff_forall_exists_pullback_unit _).1 hL x
    obtain ⟨_, ⟨i, V, hV, rfl⟩, hxV, hVU⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.1 (isBasis_preimage_isAffineOpen D c hc)) hxU
    obtain ⟨k, hk0, hki⟩ := exists_ge_ge i0 i.unop
    let t := D.map (homOfLE hki).op
    have hpre : c.π.app (op k) ⁻¹ᵁ (t ⁻¹ᵁ V) = c.π.app i ⁻¹ᵁ V := by
      rw [← Scheme.Hom.comp_preimage]
      exact congrArg (· ⁻¹ᵁ V) (c.w (homOfLE hki).op)
    have hT : Triv ((Scheme.Modules.pullback (c.π.app (op k))).obj (Mj k hk0)) (c.π.app (op k) ⁻¹ᵁ (t ⁻¹ᵁ V)) := by
      rw [hpre]
      exact triv_of_iso (hMlim k hk0).some.symm (triv_mono hVU hU)
    obtain ⟨j, hkj, hTj⟩ := triv_stage D c hc k (t ⁻¹ᵁ V) (hV.preimage t) (Mj k hk0) hT
    refine ⟨j, hk0.trans hkj, D.map (homOfLE hkj).op ⁻¹ᵁ (t ⁻¹ᵁ V),
      triv_of_iso (hMcomp k j hk0 hkj).some hTj, ?_⟩
    have : c.π.app (op j) ⁻¹ᵁ (D.map (homOfLE hkj).op ⁻¹ᵁ (t ⁻¹ᵁ V)) = c.π.app (op k) ⁻¹ᵁ (t ⁻¹ᵁ V) := by
      rw [← Scheme.Hom.comp_preimage]
      exact congrArg (· ⁻¹ᵁ (t ⁻¹ᵁ V)) (c.w (homOfLE hkj).op)
    rw [this, hpre]; exact hxV
  choose j hj O hOT hxO using hgood
  haveI : CompactSpace c.pt := Scheme.compactSpace_of_isLimit D c hc
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover
    (fun x => ((c.π.app (op (j x)) ⁻¹ᵁ O x : c.pt.Opens) : Set c.pt))
    (fun x => (show c.pt.Opens from c.π.app (op (j x)) ⁻¹ᵁ O x).isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxO x⟩)
  obtain ⟨m, hm⟩ := (insert i0 (F.image j)).exists_le
  have hm0 : i0 ≤ m := hm _ (Finset.mem_insert_self _ _)
  have hjm : ∀ x ∈ F, j x ≤ m := fun x hx => hm _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hx))
  let O' : F → (D.obj (op m)).Opens := fun x => D.map (homOfLE (hjm x.1 x.2)).op ⁻¹ᵁ O x.1
  have hO'T : ∀ x : F, Triv (Mj m hm0) (O' x) := fun x =>
    triv_of_iso (hMcomp _ _ _ (hjm x.1 x.2)).some (triv_pullback _ (hOT x.1))
  have hcov : c.π.app (op m) ⁻¹ᵁ (⨆ x : F, O' x) = ⊤ := by
    rw [Scheme.Hom.preimage_iSup, eq_top_iff]
    intro y _
    obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ y))
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hx⟩, ?_⟩
    have : c.π.app (op m) ⁻¹ᵁ O' ⟨x, hx⟩ = c.π.app (op (j x)) ⁻¹ᵁ O x := by
      rw [← Scheme.Hom.comp_preimage]
      exact congrArg (· ⁻¹ᵁ O x) (c.w (homOfLE (hjm x hx)).op)
    rw [this]; exact hyx
  obtain ⟨j', f, hf⟩ := exists_map_eq_top D c hc (i := op m) _ hcov
  have hmj : m ≤ j'.unop := leOfHom f.unop
  have hfeq : f = (homOfLE hmj).op := Subsingleton.elim _ _
  refine ⟨j'.unop, hm0.trans hmj, ?_⟩
  apply (isInvertible_iff_forall_exists_pullback_unit _).2
  intro y
  have hy : y ∈ D.map f ⁻¹ᵁ (⨆ x : F, O' x) := by rw [hf]; trivial
  rw [Scheme.Hom.preimage_iSup] at hy
  obtain ⟨x, hx⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  refine ⟨D.map f ⁻¹ᵁ O' x, hx, ?_⟩
  have := triv_of_iso (hMcomp m j'.unop hm0 hmj).some (triv_pullback (D.map (homOfLE hmj).op) (hO'T x))
  rw [hfeq]
  exact this

end PicLFT

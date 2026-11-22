import ZInQKernel.Contrib.OneProof.NeronBaseChangeStrictHenselization
import ZInQKernel.Contrib.OneProof.NeronExtSpread
import ZInQKernel.Contrib.CloudW01Spread.StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.GlueingAux2

/-!
# Spreading a smooth separated model to a stage

The principal-open argument of `NeronExt.exists_spread_sep` applies to
any directed inverse system with affine transition maps and quasi-compact,
quasi-separated stages. Descend finite presentation and smoothness by
the EGA limit theorems, and descend the diagonal as a closed immersion.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace NeronDVR

open ZInQ.Contrib.SpreadOut

/-- A smooth separated quasi-compact model over the inverse limit descends to
a smooth separated quasi-compact model at some stage. -/
theorem exists_spread_smooth_separated
    {I : Type} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{0}) [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (V : Over c.pt)
    [Smooth V.hom] [IsSeparated V.hom] [QuasiCompact V.hom] :
    ∃ (i : Iᵒᵖ) (W : Over (D.obj i)), Smooth W.hom ∧ IsSeparated W.hom ∧
      QuasiCompact W.hom ∧ Nonempty ((Over.pullback (c.π.app i)).obj W ≅ V) := by
  obtain ⟨i, Xi, hl, hq, hs, ⟨e⟩⟩ := EGAIV_8_8_2_ii_proof I D c hc V inferInstance
    inferInstance inferInstance
  have := hl; have := hq; have := hs
  have hsm : Smooth ((Over.pullback (c.π.app i)).obj Xi).hom := smooth_of_iso e
  obtain ⟨j₁, a₁, hj₁⟩ := EGAIV_17_7_8_ii_proof I D c hc i Xi hl hq hs hsm
  -- separatedness, via the diagonal
  have : CompactSpace Xi.left := QuasiCompact.compactSpace_of_compactSpace Xi.hom
  have : QuasiSeparatedSpace Xi.left := quasiSeparatedSpace_of_quasiSeparated Xi.hom
  let Y₀ : Over (D.obj i) := Over.mk (pullback.snd Xi.hom Xi.hom ≫ Xi.hom)
  have : QuasiCompact Y₀.hom := show QuasiCompact (pullback.snd Xi.hom Xi.hom ≫ Xi.hom) from inferInstance
  have : QuasiSeparated Y₀.hom :=
    show QuasiSeparated (pullback.snd Xi.hom Xi.hom ≫ Xi.hom) from inferInstance
  have : CompactSpace Y₀.left := QuasiCompact.compactSpace_of_compactSpace Y₀.hom
  have : QuasiSeparatedSpace Y₀.left := quasiSeparatedSpace_of_quasiSeparated Y₀.hom
  have : CompactSpace (Over.mk Xi.hom).left := ‹CompactSpace Xi.left›
  have : QuasiSeparatedSpace (Over.mk Xi.hom).left := ‹QuasiSeparatedSpace Xi.left›
  let f₀ : Over.mk Xi.hom ⟶ Y₀ := Over.homMk (pullback.diagonal Xi.hom) (by simp [Y₀])
  have : LocallyOfFiniteType f₀.left := by
    have : f₀.left ≫ pullback.fst Xi.hom Xi.hom = 𝟙 _ := by simp [f₀]
    have : LocallyOfFiniteType (f₀.left ≫ pullback.fst Xi.hom Xi.hom) := by
      rw [this]; infer_instance
    exact locallyOfFiniteType_of_comp f₀.left (pullback.fst Xi.hom Xi.hom)
  have : IsSeparated ((Over.pullback (c.π.app i)).obj (Over.mk Xi.hom)).hom :=
    NeronExt.isSeparated_of_iso e
  have : IsClosedImmersion ((Over.pullback (c.π.app i)).map f₀).left :=
    (NeronExt.isSeparated_pb_iff (c.π.app i) Xi).mpr inferInstance
  obtain ⟨j₂, a₂, hj₂⟩ := exists_isClosedImmersion_baseChange_of_isLimit D c hc i
    (Over.mk Xi.hom) Y₀ f₀
  have hsep₂ : IsSeparated ((Over.pullback (D.map a₂)).obj (Over.mk Xi.hom)).hom :=
    (NeronExt.isSeparated_pb_iff (D.map a₂) Xi).mp hj₂
  -- a common stage
  obtain ⟨k, b₁, b₂, -⟩ := IsCofiltered.cospan a₁ a₂
  let b : k ⟶ i := b₁ ≫ a₁
  have hb : b₂ ≫ a₂ = b := Subsingleton.elim _ _
  let W : Over (D.obj k) := (Over.pullback (D.map b)).obj Xi
  have eW₁ : W ≅ (Over.pullback (D.map b₁)).obj ((Over.pullback (D.map a₁)).obj Xi) :=
    eqToIso (by simp only [W, b, Functor.map_comp]) ≪≫ (Over.pullbackComp _ _).app Xi
  have eW₂ : W ≅ (Over.pullback (D.map b₂)).obj ((Over.pullback (D.map a₂)).obj (Over.mk Xi.hom)) :=
    eqToIso (by simp only [W, ← hb, Functor.map_comp]; rfl) ≪≫ (Over.pullbackComp _ _).app _
  refine ⟨k, W, ?_, ?_, ?_, ⟨?_⟩⟩
  · have : Smooth ((Over.pullback (D.map a₁)).obj Xi).hom := hj₁
    have : Smooth ((Over.pullback (D.map b₁)).obj ((Over.pullback (D.map a₁)).obj Xi)).hom :=
      show Smooth (pullback.snd _ _) from inferInstance
    exact smooth_of_iso eW₁
  · have := hsep₂
    have : IsSeparated ((Over.pullback (D.map b₂)).obj
        ((Over.pullback (D.map a₂)).obj (Over.mk Xi.hom))).hom :=
      show IsSeparated (pullback.snd _ _) from inferInstance
    exact NeronExt.isSeparated_of_iso eW₂
  · show QuasiCompact (pullback.snd _ _)
    infer_instance
  · exact (Over.pullbackComp (c.π.app k) (D.map b)).symm.app Xi ≪≫ NeronExt.pbCongr (c.w b) Xi ≪≫ e

/-- Two models over a stage with isomorphic pullbacks to the limit have isomorphic
pullbacks at a common later stage. This form applies to the prescribed generic fibre. -/
theorem exists_spread_model_iso
    {I : Type} [Category.{0} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{0}) [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    (X Y : Over (D.obj i)) (hX : FinitePresentation X.hom) (hY : FinitePresentation Y.hom)
    (e : (Over.pullback (c.π.app i)).obj X ≅ (Over.pullback (c.π.app i)).obj Y) :
    ∃ (k : I) (a : k ⟶ i), Nonempty ((Over.pullback (D.map a)).obj X ≅ (Over.pullback (D.map a)).obj Y) := by
  have h₁ := IsPullback.of_hasPullback X.hom (c.π.app i)
  have h₂ := isPullback_left_fst_of_overIso Y e
  obtain ⟨k, a, U, V, pu, pv, _, _, _, _, φ, hu, hv, _, _, hφ, _⟩ :=
    exists_iso_of_isPullback_of_isPullback D c hc i hX hY h₁ h₂
  let eu : Over.mk pu ≅ (Over.pullback (D.map a)).obj X :=
    Over.isoMk hu.isoPullback hu.isoPullback_hom_snd
  let ev : Over.mk pv ≅ (Over.pullback (D.map a)).obj Y :=
    Over.isoMk hv.isoPullback hv.isoPullback_hom_snd
  let ep : Over.mk pu ≅ Over.mk pv := Over.isoMk φ hφ
  exact ⟨k, a, ⟨eu.symm ≪≫ ep ≪≫ ev⟩⟩

/-- Spread a model and its specified generic-fibre isomorphism to the same stage.
The two inverse systems are the models' bases and their generic fibres. -/
theorem exists_spread_model_with_generic_fibre
    {I : Type} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (D G : Iᵒᵖ ⥤ Scheme.{0})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (G.map a)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    [∀ i, CompactSpace (G.obj i)] [∀ i, QuasiSeparatedSpace (G.obj i)]
    (cD : Cone D) (hcD : IsLimit cD) (cG : Cone G) (hcG : IsLimit cG)
    {T : Scheme.{0}} (η : G ⟶ D) (π : G ⟶ (Functor.const (Iᵒᵖ)).obj T)
    (j : cG.pt ⟶ cD.pt) (t : cG.pt ⟶ T)
    (hj : ∀ i, cG.π.app i ≫ η.app i = j ≫ cD.π.app i)
    (ht : ∀ i, cG.π.app i ≫ π.app i = t)
    (V : Over cD.pt) [Smooth V.hom] [IsSeparated V.hom] [QuasiCompact V.hom]
    (A : Over T) (hA : FinitePresentation A.hom)
    (e : (Over.pullback j).obj V ≅ (Over.pullback t).obj A) :
    ∃ (k : Iᵒᵖ) (M : Over (D.obj k)), Smooth M.hom ∧ IsSeparated M.hom ∧ QuasiCompact M.hom ∧
      Nonempty ((Over.pullback (cD.π.app k)).obj M ≅ V) ∧
      Nonempty ((Over.pullback (η.app k)).obj M ≅ (Over.pullback (π.app k)).obj A) := by
  obtain ⟨i, W, hsm, hsep, hqc, ⟨eW⟩⟩ := exists_spread_smooth_separated D cD hcD V
  let X := (Over.pullback (η.app i)).obj W
  let Y := (Over.pullback (π.app i)).obj A
  have hη : (Over.pullback (cG.π.app i)).obj X ≅ (Over.pullback j).obj V :=
    (Over.pullbackComp (cG.π.app i) (η.app i)).symm.app W ≪≫
      NeronExt.pbCongr (hj i) W ≪≫ (Over.pullbackComp j (cD.π.app i)).app W ≪≫
      (Over.pullback j).mapIso eW
  have hπ : (Over.pullback (cG.π.app i)).obj Y ≅ (Over.pullback t).obj A :=
    (Over.pullbackComp (cG.π.app i) (π.app i)).symm.app A ≪≫ NeronExt.pbCongr (ht i) A
  have hX : FinitePresentation X.hom := by
    have := hsm
    have := hsep
    have := hqc
    change FinitePresentation (pullback.snd W.hom (η.app i))
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  have hY : FinitePresentation Y.hom := by
    obtain ⟨_, _, _⟩ := hA
    change FinitePresentation (pullback.snd A.hom (π.app i))
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨k, a, ⟨eη⟩⟩ := exists_spread_model_iso G cG hcG i X Y hX hY (hη ≪≫ e ≪≫ hπ.symm)
  let M := (Over.pullback (D.map a)).obj W
  have hM : (Over.pullback (cD.π.app k)).obj M ≅ V :=
    (Over.pullbackComp (cD.π.app k) (D.map a)).symm.app W ≪≫ NeronExt.pbCongr (cD.w a) W ≪≫ eW
  have he₁ : (Over.pullback (η.app k)).obj M ≅ (Over.pullback (G.map a)).obj X :=
    (Over.pullbackComp (η.app k) (D.map a)).symm.app W ≪≫
      NeronExt.pbCongr (η.naturality a).symm W ≪≫ (Over.pullbackComp (G.map a) (η.app i)).app W
  have hp : G.map a ≫ π.app i = π.app k := by
    have hn := π.naturality a
    change G.map a ≫ π.app i = π.app k ≫ 𝟙 T at hn
    exact hn.trans (Category.comp_id _)
  have he₂ : (Over.pullback (G.map a)).obj Y ≅ (Over.pullback (π.app k)).obj A :=
    (Over.pullbackComp (G.map a) (π.app i)).symm.app A ≪≫
      NeronExt.pbCongr hp A
  letI : Smooth W.hom := hsm
  letI : IsSeparated W.hom := hsep
  letI : QuasiCompact W.hom := hqc
  refine ⟨k, M, ?_, ?_, ?_, ⟨hM⟩, ⟨he₁ ≪≫ eη ≪≫ he₂⟩⟩
  · change Smooth (pullback.snd W.hom (D.map a))
    infer_instance
  · change IsSeparated (pullback.snd W.hom (D.map a))
    infer_instance
  · change QuasiCompact (pullback.snd W.hom (D.map a))
    infer_instance

/-- Spread a model with a prescribed generic fibre along a diagram over a fixed
base, using the base-changed diagram for the generic schemes. -/
theorem exists_spread_model_over
    {I : Type} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    {S T T' : Scheme.{0}} (j : T ⟶ S) [CompactSpace T] [QuasiSeparatedSpace T]
    (D : Iᵒᵖ ⥤ Over S)
    [∀ {i k : Iᵒᵖ} (a : i ⟶ k), IsAffineHom (D.map a).left]
    [∀ i, IsAffineHom (D.obj i).hom]
    [hcompact : ∀ i, CompactSpace (D.obj i).left]
    [hquasiSeparated : ∀ i, QuasiSeparatedSpace (D.obj i).left]
    (c : Cone D) (hc : IsLimit c)
    (j' : T' ⟶ c.pt.left) (t : T' ⟶ T) (hpb : IsPullback j' t c.pt.hom j)
    (V : Over c.pt.left) [Smooth V.hom] [IsSeparated V.hom] [QuasiCompact V.hom]
    (A : Over T) (hA : FinitePresentation A.hom)
    (e : (Over.pullback j').obj V ≅ (Over.pullback t).obj A) :
    ∃ (i : Iᵒᵖ) (M : Over (D.obj i).left),
      Nonempty ((Over.pullback (c.π.app i).left).obj M ≅ V) ∧
      Nonempty ((Over.pullback (pullback.fst (D.obj i).hom j)).obj M ≅
        (Over.pullback (pullback.snd (D.obj i).hom j)).obj A) := by
  have : IsConnected Iᵒᵖ := IsCofiltered.isConnected _
  let D₀ := D ⋙ Over.forget S
  let G₁ := D ⋙ Over.pullback j
  let G₀ := G₁ ⋙ Over.forget T
  let cD := (Over.forget S).mapCone c
  let cG := (Over.forget T).mapCone ((Over.pullback j).mapCone c)
  have hcD : IsLimit cD := isLimitOfPreserves (Over.forget S) hc
  have hcG : IsLimit cG :=
    isLimitOfPreserves (Over.forget T) (isLimitOfPreserves (Over.pullback j) hc)
  let η : G₀ ⟶ D₀ :=
    NatTrans.mk (fun i => pullback.fst (D.obj i).hom j) (fun _ _ a => by
      change ((Over.pullback j).map (D.map a)).left ≫ pullback.fst _ _ = _
      simp [D₀])
  let π : G₀ ⟶ (Functor.const _).obj T :=
    NatTrans.mk (fun i => ((Over.pullback j).obj (D.obj i)).hom)
      (fun _ _ a => Over.w ((Over.pullback j).map (D.map a)))
  let j₀ := pullback.fst c.pt.hom j
  let t₀ := pullback.snd c.pt.hom j
  have hj (i : Iᵒᵖ) : cG.π.app i ≫ η.app i = j₀ ≫ cD.π.app i := by
    change ((Over.pullback j).map (c.π.app i)).left ≫ pullback.fst _ _ = _
    simp [j₀, cD]
  have ht (i : Iᵒᵖ) : cG.π.app i ≫ π.app i = t₀ :=
    Over.w ((Over.pullback j).map (c.π.app i))
  have (i : Iᵒᵖ) : CompactSpace (D₀.obj i) := hcompact i
  have (i : Iᵒᵖ) : QuasiSeparatedSpace (D₀.obj i) := hquasiSeparated i
  have {i k : Iᵒᵖ} (a : i ⟶ k) : IsAffineHom (D₀.map a) :=
    show IsAffineHom (D.map a).left from inferInstance
  have {i k : Iᵒᵖ} (a : i ⟶ k) : IsAffineHom (G₀.map a) :=
    NeronSH.isAffineHom_pullback_map_left j (D.map a)
  have (i : Iᵒᵖ) : CompactSpace (G₀.obj i) := by
    change CompactSpace (pullback (D.obj i).hom j : Scheme.{0})
    exact QuasiCompact.compactSpace_of_compactSpace (pullback.snd (D.obj i).hom j)
  have (i : Iᵒᵖ) : QuasiSeparatedSpace (G₀.obj i) := by
    change QuasiSeparatedSpace (pullback (D.obj i).hom j : Scheme.{0})
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.snd (D.obj i).hom j)
  let g := hpb.isoPullback.inv
  let e₀ : (Over.pullback j₀).obj V ≅ (Over.pullback t₀).obj A :=
    NeronExt.pbCongr hpb.isoPullback_inv_fst.symm V ≪≫
      (Over.pullbackComp g j').app V ≪≫ (Over.pullback g).mapIso e ≪≫
      (Over.pullbackComp g t).symm.app A ≪≫ NeronExt.pbCongr hpb.isoPullback_inv_snd A
  obtain ⟨i, M, _, _, _, eM, eA⟩ :=
    exists_spread_model_with_generic_fibre D₀ G₀ cD hcD cG hcG η π j₀ t₀ hj ht V A hA e₀
  exact ⟨i, M, eM, eA⟩

end NeronDVR

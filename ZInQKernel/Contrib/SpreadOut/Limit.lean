import Mathlib
import ZInQKernel.Contrib.SpreadOut.GrpDescent

/-!
# Spreading out, II: morphisms over a cofiltered limit of schemes, in `Over` form

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task spread-out, 2026-11-13).

Mathlib only, no hypotheses.  Setting: `D : I ⥤ Scheme`, `I` cofiltered, affine transition maps,
qcqs terms, `c` a limit cone.  For `Y, Z` over a stage `D k` (Y qcqs, Z of finite presentation):
* `exists_lift` (EGA IV₃ 8.8.2 (i), surjectivity): every morphism `Y ×_{D k} lim ⟶ Z ×_{D k} lim`
  over `lim` is the base change of a morphism `Y ×_{D k} D k' ⟶ Z ×_{D k} D k'` over some later
  stage `D k'`;
* `exists_map_eq` (injectivity): two morphisms `Y ⟶ Z` over `D k` with the same base change to
  `lim` agree over some later stage.
Both are deduced from Mathlib's `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation` and
`Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType` (Stacks 01ZC), applied to the diagram
`l ↦ Y ×_{D k} D l` over `Over k` (`bcDiag`), whose limit is `Y ×_{D k} lim` (`bcConeIsLimit`).
`pbNat` is an explicit form of `Over.pullbackComp` (composite of base changes).
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry

namespace ZInQ.Contrib.SpreadOut

universe u

/-! ### Explicit composites of base change -/

section PbNat

variable {X Y Z : Scheme.{u}}

/-- `(G ×_Z Y) ×_Y X ≅ G ×_Z X` along `f ≫ g = h`, with explicit components. -/
noncomputable def pbNatLeft (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h) (G : Over Z) :
    pullback (pullback.snd G.hom g) f ≅ pullback G.hom h where
  hom := pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc, w])
  inv := pullback.lift (pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ f) (by
      rw [pullback.condition, ← w, Category.assoc])) (pullback.snd _ _) (by simp)
  hom_inv_id := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp
      · simp [pullback.condition]
    · simp
  inv_hom_id := by
    apply pullback.hom_ext <;> simp

@[reassoc (attr := simp)]
theorem pbNatLeft_hom_fst (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h) (G : Over Z) :
    (pbNatLeft f g h w G).hom ≫ pullback.fst G.hom h = pullback.fst _ _ ≫ pullback.fst _ _ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem pbNatLeft_hom_snd (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h) (G : Over Z) :
    (pbNatLeft f g h w G).hom ≫ pullback.snd G.hom h = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem pbNatLeft_inv_fst_fst (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h) (G : Over Z) :
    (pbNatLeft f g h w G).inv ≫ pullback.fst (pullback.snd G.hom g) f ≫ pullback.fst G.hom g =
      pullback.fst _ _ := by
  simp [pbNatLeft]

@[reassoc (attr := simp)]
theorem pbNatLeft_inv_fst_snd (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h) (G : Over Z) :
    (pbNatLeft f g h w G).inv ≫ pullback.fst (pullback.snd G.hom g) f ≫ pullback.snd G.hom g =
      pullback.snd _ _ ≫ f := by
  simp [pbNatLeft]

@[reassoc (attr := simp)]
theorem pbNatLeft_inv_snd (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h) (G : Over Z) :
    (pbNatLeft f g h w G).inv ≫ pullback.snd (pullback.snd G.hom g) f = pullback.snd _ _ := by
  simp [pbNatLeft]

/-- `g^* ⋙ f^* ≅ h^*` for `f ≫ g = h` (explicit form of `Over.pullbackComp`). -/
noncomputable def pbNat (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h) :
    Over.pullback g ⋙ Over.pullback f ≅ Over.pullback h :=
  NatIso.ofComponents (fun G => Over.isoMk (pbNatLeft f g h w G) (by
      simp only [Functor.comp_obj, Over.pullback_obj_left, Over.pullback_obj_hom]
      exact pbNatLeft_hom_snd f g h w G))
    (by
      intro G G' φ
      ext1
      apply pullback.hom_ext
      · simp [Over.pullback]
      · simp [Over.pullback])

@[simp]
theorem pbNat_hom_app_left (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h) (G : Over Z) :
    ((pbNat f g h w).hom.app G).left = (pbNatLeft f g h w G).hom := rfl

@[simp]
theorem pbNat_inv_app_left (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h) (G : Over Z) :
    ((pbNat f g h w).inv.app G).left = (pbNatLeft f g h w G).inv := rfl

/-- Equal base changes stay equal after a further base change. -/
theorem pullback_map_eq_of_comp {W : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y) {G G' : Over Y}
    {g₁ g₂ : G ⟶ G'} (hg : (Over.pullback g).map g₁ = (Over.pullback g).map g₂) :
    (Over.pullback (f ≫ g)).map g₁ = (Over.pullback (f ≫ g)).map g₂ := by
  rw [← NatIso.naturality_1 (pbNat f g (f ≫ g) rfl) g₁,
    ← NatIso.naturality_1 (pbNat f g (f ≫ g) rfl) g₂]
  simp only [Functor.comp_map, hg]

end PbNat

/-! ### The base-changed diagram `l ↦ Y ×_{D k} D l` over `Over k` -/

section Diagram

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)

/-- The comparison `θ_b : (D b)^* ⋙ (π k')^* ≅ (π k)^*` for `b : k' ⟶ k`. -/
noncomputable abbrev stθ {k k' : I} (b : k' ⟶ k) :
    Over.pullback (D.map b) ⋙ Over.pullback (c.π.app k') ≅ Over.pullback (c.π.app k) :=
  pbNat (c.π.app k') (D.map b) (c.π.app k) (c.w b)

/-- The diagram `l ↦ Y ×_{D k} D l` indexed by `Over k`. -/
@[simps] noncomputable def bcDiag {k : I} (Y : Over (D.obj k)) : Over k ⥤ Scheme.{u} where
  obj l := pullback Y.hom (D.map l.hom)
  map {l l'} φ := pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ D.map φ.left) (by
    rw [pullback.condition, Category.assoc, ← D.map_comp, Over.w φ])
  map_id l := by apply pullback.hom_ext <;> simp
  map_comp φ ψ := by apply pullback.hom_ext <;> simp

/-- `Y ×_{D k} lim` as a cone over `bcDiag`. -/
@[simps] noncomputable def bcCone {k : I} (Y : Over (D.obj k)) : Cone (bcDiag D Y) where
  pt := pullback Y.hom (c.π.app k)
  π :=
    { app l := pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ c.π.app l.left) (by
        rw [pullback.condition, Category.assoc, c.w])
      naturality l l' φ := by
        apply pullback.hom_ext
        · simp
        · simp }

/-- The projection `bcDiag ⟶ D` (restricted to `Over k`). -/
@[simps] noncomputable def bcDiagι {k : I} (Y : Over (D.obj k)) :
    bcDiag D Y ⟶ Over.forget k ⋙ D where
  app l := pullback.snd _ _

theorem bcDiag_isPullback {k : I} (Y : Over (D.obj k)) {l l' : Over k} (φ : l ⟶ l') :
    IsPullback ((bcDiag D Y).map φ) (pullback.snd Y.hom (D.map l.hom))
      (pullback.snd Y.hom (D.map l'.hom)) (D.map φ.left) := by
  refine IsPullback.of_right (h₁₂ := pullback.fst Y.hom (D.map l'.hom)) (v₁₃ := Y.hom)
    (h₂₂ := D.map l'.hom) ?_ (by simp) (IsPullback.of_hasPullback _ _)
  have e1 : (bcDiag D Y).map φ ≫ pullback.fst Y.hom (D.map l'.hom) =
      pullback.fst Y.hom (D.map l.hom) := by simp
  have e2 : D.map φ.left ≫ D.map l'.hom = D.map l.hom := by rw [← D.map_comp, Over.w φ]
  rw [e1, e2]
  exact IsPullback.of_hasPullback _ _

theorem bcCone_isPullback {k : I} (Y : Over (D.obj k)) (l : Over k) :
    IsPullback ((bcCone D c Y).π.app l) (pullback.snd Y.hom (c.π.app k))
      (pullback.snd Y.hom (D.map l.hom)) (c.π.app l.left) := by
  refine IsPullback.of_right (h₁₂ := pullback.fst Y.hom (D.map l.hom)) (v₁₃ := Y.hom)
    (h₂₂ := D.map l.hom) ?_ (by simp) (IsPullback.of_hasPullback _ _)
  have e1 : (bcCone D c Y).π.app l ≫ pullback.fst Y.hom (D.map l.hom) =
      pullback.fst Y.hom (c.π.app k) := by simp
  rw [e1, c.w]
  exact IsPullback.of_hasPullback _ _

attribute [local instance] CategoryTheory.isConnected_of_hasTerminal

/-- `Y ×_{D k} lim = lim_{l → k} Y ×_{D k} D l`. -/
noncomputable def bcConeIsLimit [IsCofiltered I] (hc : IsLimit c) {k : I} (Y : Over (D.obj k)) :
    IsLimit (bcCone D c Y) :=
  isLimitOfIsPullbackOfIsConnected (bcDiagι D Y) (bcCone D c Y) (Cone.whisker (Over.forget k) c)
    { hom := pullback.snd _ _
      w l := by simp }
    (fun l => bcCone_isPullback D c Y l)
    ((Functor.Initial.isLimitWhiskerEquiv (Over.forget k) c).symm hc)

theorem bcDiag_isAffineHom [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] {k : I}
    (Y : Over (D.obj k)) {l l' : Over k} (φ : l ⟶ l') : IsAffineHom ((bcDiag D Y).map φ) :=
  MorphismProperty.of_isPullback (P := @IsAffineHom) (bcDiag_isPullback D Y φ).flip inferInstance

theorem bcDiag_compactSpace [∀ i, CompactSpace (D.obj i)] {k : I} (Y : Over (D.obj k))
    [QuasiCompact Y.hom] (l : Over k) : CompactSpace ((bcDiag D Y).obj l) :=
  QuasiCompact.compactSpace_of_compactSpace (pullback.snd Y.hom (D.map l.hom))

theorem bcDiag_quasiSeparatedSpace [∀ i, QuasiSeparatedSpace (D.obj i)] {k : I}
    (Y : Over (D.obj k)) [QuasiSeparated Y.hom] (l : Over k) :
    QuasiSeparatedSpace ((bcDiag D Y).obj l) :=
  quasiSeparatedSpace_of_quasiSeparated (pullback.snd Y.hom (D.map l.hom))

/-- The structure maps `Y ×_{D k} D l → D k`. -/
@[simps] noncomputable def bcDiagT {k : I} (Y : Over (D.obj k)) :
    bcDiag D Y ⟶ (Functor.const (Over k)).obj (D.obj k) where
  app l := pullback.snd _ _ ≫ D.map l.hom
  naturality l l' φ := by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id, bcDiag_map,
      pullback.lift_snd_assoc, Category.assoc, ← D.map_comp, Over.w φ]

/-- **Descent of morphisms (EGA IV₃ 8.8.2 (i), surjectivity), `Over` form.**  For `Y` qcqs and
`Z` locally of finite presentation over the stage `D k`, every morphism of base changes to `lim D`
is the base change of a morphism over some later stage, up to the comparisons `stθ`. -/
theorem exists_lift [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] (hc : IsLimit c) {k : I}
    (Y Z : Over (D.obj k)) [QuasiCompact Y.hom] [QuasiSeparated Y.hom]
    [LocallyOfFinitePresentation Z.hom]
    (g : (Over.pullback (c.π.app k)).obj Y ⟶ (Over.pullback (c.π.app k)).obj Z) :
    ∃ (k' : I) (b : k' ⟶ k)
      (g' : (Over.pullback (D.map b)).obj Y ⟶ (Over.pullback (D.map b)).obj Z),
      (Over.pullback (c.π.app k')).map g' = (stθ D c b).hom.app Y ≫ g ≫ (stθ D c b).inv.app Z := by
  haveI : ∀ {l l' : Over k} (φ : l ⟶ l'), IsAffineHom ((bcDiag D Y).map φ) :=
    fun φ => bcDiag_isAffineHom D Y φ
  haveI : ∀ l, CompactSpace ((bcDiag D Y).obj l) := bcDiag_compactSpace D Y
  haveI : ∀ l, QuasiSeparatedSpace ((bcDiag D Y).obj l) := bcDiag_quasiSeparatedSpace D Y
  have hgw : g.left ≫ pullback.snd Z.hom (c.π.app k) = pullback.snd Y.hom (c.π.app k) := Over.w g
  obtain ⟨l, g₀, h1, h2⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (bcDiag D Y) (bcDiagT D Y) Z.hom (bcCone D c Y) (bcConeIsLimit D c hc Y)
    (g.left ≫ pullback.fst _ _) (by
      ext l
      simp only [NatTrans.comp_app, Functor.const_obj_obj, bcCone_pt, bcCone_π_app, bcDiagT_app,
        pullback.lift_snd_assoc, Category.assoc, c.w, Functor.const_map_app]
      rw [pullback.condition, reassoc_of% hgw])
  have h2' : g₀ ≫ Z.hom = pullback.snd Y.hom (D.map l.hom) ≫ D.map l.hom := h2
  refine ⟨l.left, l.hom, Over.homMk (pullback.lift g₀ (pullback.snd _ _) h2') (by simp), ?_⟩
  ext1
  show pullback.lift (pullback.fst (pullback.snd Y.hom (D.map l.hom)) (c.π.app l.left) ≫
      pullback.lift g₀ (pullback.snd _ _) h2') (pullback.snd _ _) _ =
    (pbNatLeft _ _ _ (c.w l.hom) Y).hom ≫ g.left ≫ (pbNatLeft _ _ _ (c.w l.hom) Z).inv
  have hgw' : g.left ≫ pullback.snd Z.hom (c.π.app k) = pullback.snd Y.hom (c.π.app k) := hgw
  have h1' : pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ c.π.app l.left)
      (by rw [pullback.condition, Category.assoc, c.w]) ≫ g₀ =
      g.left ≫ pullback.fst Z.hom (c.π.app k) := h1
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, pbNatLeft_inv_fst_fst]
      rw [← h1', ← Category.assoc]
      congr 1
      apply pullback.hom_ext
      · simp
      · simp [pullback.condition]
    · simp only [Category.assoc, pullback.lift_fst_assoc, pullback.lift_snd, pbNatLeft_inv_fst_snd]
      rw [reassoc_of% hgw', pbNatLeft_hom_snd_assoc]
      exact pullback.condition
  · simp only [Category.assoc, pullback.lift_snd, pbNatLeft_inv_snd]
    rw [hgw', pbNatLeft_hom_snd]

/-- **Descent of equalities of morphisms (EGA IV₃ 8.8.2 (i), injectivity), `Over` form.** -/
theorem exists_map_eq [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] (hc : IsLimit c) {k : I} {Y Z : Over (D.obj k)}
    [QuasiCompact Y.hom] [LocallyOfFiniteType Z.hom] (g₁ g₂ : Y ⟶ Z)
    (h : (Over.pullback (c.π.app k)).map g₁ = (Over.pullback (c.π.app k)).map g₂) :
    ∃ (k' : I) (b : k' ⟶ k),
      (Over.pullback (D.map b)).map g₁ = (Over.pullback (D.map b)).map g₂ := by
  haveI : ∀ {l l' : Over k} (φ : l ⟶ l'), IsAffineHom ((bcDiag D Y).map φ) :=
    fun φ => bcDiag_isAffineHom D Y φ
  haveI : ∀ l, CompactSpace ((bcDiag D Y).obj l) := bcDiag_compactSpace D Y
  have h' : pullback.fst Y.hom (c.π.app k) ≫ g₁.left = pullback.fst Y.hom (c.π.app k) ≫ g₂.left := by
    have := congrArg (fun φ => φ.left ≫ pullback.fst _ _) h
    simpa [Over.pullback] using this
  have w₁ : g₁.left ≫ Z.hom = Y.hom := Over.w g₁
  have w₂ : g₂.left ≫ Z.hom = Y.hom := Over.w g₂
  obtain ⟨l, hl, e⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType (bcDiag D Y)
    (bcDiagT D Y) Z.hom (bcCone D c Y) (bcConeIsLimit D c hc Y) (i := Over.mk (𝟙 k))
    (pullback.fst _ _ ≫ g₁.left) (pullback.fst _ _ ≫ g₂.left)
    (by simp [w₁, pullback.condition]) (by simp [w₂, pullback.condition])
    (by simp [h'])
  refine ⟨l.left, l.hom, ?_⟩
  ext1
  apply pullback.hom_ext
  · have e' : pullback.fst Y.hom (D.map l.hom) ≫ g₁.left =
        pullback.fst Y.hom (D.map l.hom) ≫ g₂.left := by
      simpa using e
    simpa [Over.pullback] using e'
  · simp [Over.pullback]

end Diagram

end ZInQ.Contrib.SpreadOut

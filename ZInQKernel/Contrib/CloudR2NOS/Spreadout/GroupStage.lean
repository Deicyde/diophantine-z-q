/-
# H5 / NOS round 2, lane 3 (`Spreadout/`): group schemes over a cofiltered limit, universe `u`

New glue (no vendored source in this file). It generalizes the published universe-0
`ZInQ.Contrib.SpreadOut.Spread` group-descent argument (Deicyde/diophantine-z-q, task spread-out,
2026-11-13) to an arbitrary universe `u`, which the universe-polymorphic `PkgI2.NeronOggShafarevich`
needs, and drops the proper/smooth fields from the stage record so that properness is never
assumed at a stage.

Inputs actually used (all published, unchanged):
* `ZInQ.Contrib.SpreadOut.{exists_lift, exists_map_eq, stθ, pullback_map_eq_of_comp}`
  (`SpreadOut/Limit.lean`, universe `u`; EGA IV₃ 8.8.2 (i) via Mathlib's Stacks 01ZC);
* `ZInQ.Contrib.SpreadOut.{CompatM, CompatU, CompatI, FAx, fAx_of_compat, compat*_transport,
  compat*_of_lift, isMonHom_descend, grpAx_map_iff}` (`SpreadOut/GrpDescent.lean`);
* `AlgebraicGeometry.LimitDescent.exists_model_of_finitePresentation_of_essentiallySmall`
  (Stacks 01ZM, AxiomMath/Stacks@c496df0d port in the published `Contrib/CloudW01Spread`);
* `AlgebraicGeometry.exists_smooth_baseChange_of_smooth_limitBaseChange` (Stacks 0C0C / EGA IV
  17.7.8 (ii), same published port) and `ZInQ.Contrib.CloudW01Spread.pullback_to_identity_iff`.

Properness is NOT descended here: `ProperDescendsFor D c` is the exact stage statement of
EGA IV₃ 8.10.5 (xii) / Stacks 081F for the given system, kept as an explicit input (owned by the
H65 row; for universe 0 it is implied by the published leaf `ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii`,
see `properDescendsFor_of_ega`).
-/
import ZInQKernel.Contrib.SpreadOut.Spread
import ZInQKernel.Contrib.CloudW01Spread.FinitePresentation
import ZInQKernel.Contrib.CloudW01Spread.Smooth

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

namespace ZInQ.Contrib.CloudR2NOS.Spreadout

universe u

open ZInQ.Contrib.SpreadOut (stθ exists_lift exists_map_eq pullback_map_eq_of_comp CompatM CompatU
  CompatI FAx fAx_of_compat compatM_transport compatU_transport compatI_transport compatM_of_lift
  compatU_of_lift compatI_of_lift isMonHom_descend grpAx_map_iff)

/-! ### Finiteness instances in `Over S`, universe `u` -/

section Instances

variable {S T : Scheme.{u}}

instance qc_tensor (X Y : Over S) [QuasiCompact X.hom] [QuasiCompact Y.hom] :
    QuasiCompact (X ⊗ Y).hom :=
  show QuasiCompact (pullback.fst X.hom Y.hom ≫ X.hom) from inferInstance

instance qs_tensor (X Y : Over S) [QuasiSeparated X.hom] [QuasiSeparated Y.hom] :
    QuasiSeparated (X ⊗ Y).hom :=
  show QuasiSeparated (pullback.fst X.hom Y.hom ≫ X.hom) from inferInstance

instance lfp_tensor (X Y : Over S) [LocallyOfFinitePresentation X.hom]
    [LocallyOfFinitePresentation Y.hom] : LocallyOfFinitePresentation (X ⊗ Y).hom :=
  show LocallyOfFinitePresentation (pullback.fst X.hom Y.hom ≫ X.hom) from inferInstance

instance qc_unit : QuasiCompact (𝟙_ (Over S)).hom :=
  show QuasiCompact (𝟙 S) from inferInstance

instance qs_unit : QuasiSeparated (𝟙_ (Over S)).hom :=
  show QuasiSeparated (𝟙 S) from inferInstance

instance qc_pb (f : T ⟶ S) (X : Over S) [QuasiCompact X.hom] :
    QuasiCompact ((Over.pullback f).obj X).hom :=
  show QuasiCompact (pullback.snd X.hom f) from inferInstance

instance qs_pb (f : T ⟶ S) (X : Over S) [QuasiSeparated X.hom] :
    QuasiSeparated ((Over.pullback f).obj X).hom :=
  show QuasiSeparated (pullback.snd X.hom f) from inferInstance

instance lfp_pb (f : T ⟶ S) (X : Over S) [LocallyOfFinitePresentation X.hom] :
    LocallyOfFinitePresentation ((Over.pullback f).obj X).hom :=
  show LocallyOfFinitePresentation (pullback.snd X.hom f) from inferInstance

/-- Any base-change-stable morphism property passes to `(Over.pullback f).obj X`. -/
theorem prop_pb (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange] (f : T ⟶ S)
    (X : Over S) (h : P X.hom) : P ((Over.pullback f).obj X).hom :=
  P.pullback_snd X.hom f h

/-- Any isomorphism-invariant morphism property transfers along an isomorphism in `Over S`. -/
theorem prop_of_iso (P : MorphismProperty Scheme.{u}) [P.RespectsIso] {X Y : Over S} (e : X ≅ Y)
    (h : P Y.hom) : P X.hom := by
  rw [← Over.w e.hom]
  haveI : IsIso e.hom.left := ⟨e.inv.left, by rw [← Over.comp_left, e.hom_inv_id]; rfl,
    by rw [← Over.comp_left, e.inv_hom_id]; rfl⟩
  exact (P.cancel_left_of_respectsIso e.hom.left Y.hom).2 h

end Instances

/-! ### Eventually-true predicates along a cofiltered category -/

section Eventually

variable {I : Type u} [Category.{u} I]

/-- `Q` holds along every map factoring through some `b : k' ⟶ k`. -/
def Ev {k : I} (Q : ∀ {k' : I}, (k' ⟶ k) → Prop) : Prop :=
  ∃ (k' : I) (b : k' ⟶ k), ∀ {k'' : I} (b' : k'' ⟶ k'), Q (b' ≫ b)

theorem Ev.and [IsCofiltered I] {k : I} {Q₁ Q₂ : ∀ {k' : I}, (k' ⟶ k) → Prop} (h₁ : Ev Q₁)
    (h₂ : Ev Q₂) : Ev (fun b => Q₁ b ∧ Q₂ b) := by
  obtain ⟨k₁, b₁, h₁⟩ := h₁
  obtain ⟨k₂, b₂, h₂⟩ := h₂
  obtain ⟨m, i, j, hij⟩ := IsCofiltered.cospan b₁ b₂
  refine ⟨m, i ≫ b₁, fun b' => ⟨?_, ?_⟩⟩
  · have := h₁ (b' ≫ i); rwa [Category.assoc] at this
  · have := h₂ (b' ≫ j); rwa [Category.assoc, ← hij] at this

theorem Ev.exists {k : I} {Q : ∀ {k' : I}, (k' ⟶ k) → Prop} (h : Ev Q) :
    ∃ (k' : I) (b : k' ⟶ k), Q b := by
  obtain ⟨k', b, h⟩ := h
  exact ⟨k', b, by simpa using h (𝟙 k')⟩

end Eventually

/-! ### Descent of a group structure to a finite stage, universe `u` -/

section Descent

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
  [∀ i, QuasiSeparatedSpace (D.obj i)] (c : Cone D) (hc : IsLimit c)

include hc in
theorem ev_map_eq {k : I} {Y Z : Over (D.obj k)} [QuasiCompact Y.hom]
    [LocallyOfFiniteType Z.hom] (g₁ g₂ : Y ⟶ Z)
    (h : (Over.pullback (c.π.app k)).map g₁ = (Over.pullback (c.π.app k)).map g₂) :
    Ev (fun {k'} (b : k' ⟶ k) =>
      (Over.pullback (D.map b)).map g₁ = (Over.pullback (D.map b)).map g₂) := by
  obtain ⟨k', b, hb⟩ := exists_map_eq D c hc g₁ g₂ h
  refine ⟨k', b, fun b' => ?_⟩
  show (Over.pullback (D.map (b' ≫ b))).map g₁ = (Over.pullback (D.map (b' ≫ b))).map g₂
  rw [D.map_comp]
  exact pullback_map_eq_of_comp _ _ hb

include hc in
/-- The group axioms for raw data compatible with a group object at the limit hold over some
later stage. -/
theorem ev_fAx {k : I} {M : Over (D.obj k)} [QuasiCompact M.hom] [QuasiSeparated M.hom]
    [LocallyOfFinitePresentation M.hom] {N : Over c.pt} [GrpObj N]
    (e : (Over.pullback (c.π.app k)).obj M ≅ N) {m : M ⊗ M ⟶ M} {u : 𝟙_ _ ⟶ M} {i : M ⟶ M}
    (hm : CompatM _ e m) (hu : CompatU _ e u) (hi : CompatI _ e i) :
    ∃ (k' : I) (b : k' ⟶ k), FAx (Over.pullback (D.map b)) m u i := by
  have hF := fAx_of_compat _ e hm hu hi
  obtain ⟨k', b, ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ :=
    ((((ev_map_eq D c hc _ _ hF.one_mul).and (ev_map_eq D c hc _ _ hF.mul_one)).and
      (ev_map_eq D c hc _ _ hF.mul_assoc)).and (ev_map_eq D c hc _ _ hF.left_inv)).and
      (ev_map_eq D c hc _ _ hF.right_inv) |>.exists
  exact ⟨k', b, ⟨h1, h2, h3, h4, h5⟩⟩

/-- A finitely presented stage object with an identification of its base change with `N`.
No properness or smoothness is recorded. -/
structure FPStage (N : Over c.pt) where
  k : I
  M : Over (D.obj k)
  qc : QuasiCompact M.hom
  qs : QuasiSeparated M.hom
  lfp : LocallyOfFinitePresentation M.hom
  e : (Over.pullback (c.π.app k)).obj M ≅ N

attribute [instance] FPStage.qc FPStage.qs FPStage.lfp

variable {D c}

/-- Base change of a stage along `b : k' ⟶ k`. -/
def FPStage.next {N : Over c.pt} (s : FPStage D c N) {k' : I} (b : k' ⟶ s.k) :
    FPStage D c N where
  k := k'
  M := (Over.pullback (D.map b)).obj s.M
  qc := inferInstance
  qs := inferInstance
  lfp := inferInstance
  e := (stθ D c b).app s.M ≪≫ s.e

theorem FPStage.next_prop (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    {N : Over c.pt} (s : FPStage D c N) {k' : I} (b : k' ⟶ s.k) (h : P s.M.hom) :
    P (s.next b).M.hom :=
  prop_pb P (D.map b) s.M h

include hc in
theorem exists_mul {N : Over c.pt} [GrpObj N] (s : FPStage D c N) :
    ∃ (k' : I) (b : k' ⟶ s.k) (m : (s.next b).M ⊗ (s.next b).M ⟶ (s.next b).M),
      CompatM _ (s.next b).e m := by
  obtain ⟨k', b, g', hg⟩ := exists_lift D c hc (s.M ⊗ s.M) s.M
    (inv (Functor.LaxMonoidal.μ (Over.pullback (c.π.app s.k)) s.M s.M) ≫
      (s.e.hom ⊗ₘ s.e.hom) ≫ μ[N] ≫ s.e.inv)
  exact ⟨k', b, _, compatM_of_lift (Over.pullback (D.map b)) (Over.pullback (c.π.app k'))
    (Over.pullback (c.π.app s.k)) (stθ D c b) s.e hg⟩

include hc in
theorem exists_one {N : Over c.pt} [GrpObj N] (s : FPStage D c N) :
    ∃ (k' : I) (b : k' ⟶ s.k) (u : 𝟙_ _ ⟶ (s.next b).M), CompatU _ (s.next b).e u := by
  obtain ⟨k', b, g', hg⟩ := exists_lift D c hc (𝟙_ _) s.M
    (inv (Functor.LaxMonoidal.ε (Over.pullback (c.π.app s.k))) ≫ η[N] ≫ s.e.inv)
  exact ⟨k', b, _, compatU_of_lift (Over.pullback (D.map b)) (Over.pullback (c.π.app k'))
    (Over.pullback (c.π.app s.k)) (stθ D c b) s.e hg⟩

include hc in
theorem exists_inv {N : Over c.pt} [GrpObj N] (s : FPStage D c N) :
    ∃ (k' : I) (b : k' ⟶ s.k) (i : (s.next b).M ⟶ (s.next b).M), CompatI _ (s.next b).e i := by
  obtain ⟨k', b, g', hg⟩ := exists_lift D c hc s.M s.M (s.e.hom ≫ ι[N] ≫ s.e.inv)
  exact ⟨k', b, _, compatI_of_lift (Over.pullback (D.map b)) (Over.pullback (c.π.app k'))
    (Over.pullback (c.π.app s.k)) (stθ D c b) s.e hg⟩

include hc in
/-- **Descent of a group structure to a finite stage (universe `u`).**  A finitely presented
stage object whose base change to `lim D` is identified with a group object `N` carries, after a
further base change, a group structure for which the identification is a morphism of group
objects. Every base-change-stable property of the original stage object is kept. -/
theorem exists_grp_stage {N : Over c.pt} [GrpObj N] (s : FPStage D c N) :
    ∃ (t : FPStage D c N) (_ : GrpObj t.M),
      (∀ (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange], P s.M.hom → P t.M.hom) ∧
      letI : GrpObj ((Over.pullback (c.π.app t.k)).obj t.M) := Functor.grpObjObj
      IsMonHom t.e.hom := by
  obtain ⟨k₁, b₁, m₁, hm₁⟩ := exists_mul hc s
  obtain ⟨k₂, b₂, u₂, hu₂⟩ := exists_one hc (s.next b₁)
  have hm₂ := compatM_transport (Over.pullback (D.map b₂)) (Over.pullback (c.π.app k₂))
    (Over.pullback (c.π.app (s.next b₁).k)) (stθ D c b₂) (s.next b₁).e hm₁
  obtain ⟨k₃, b₃, i₃, hi₃⟩ := exists_inv hc ((s.next b₁).next b₂)
  have hm₃ := compatM_transport (Over.pullback (D.map b₃)) (Over.pullback (c.π.app k₃))
    (Over.pullback (c.π.app ((s.next b₁).next b₂).k)) (stθ D c b₃) ((s.next b₁).next b₂).e hm₂
  have hu₃ := compatU_transport (Over.pullback (D.map b₃)) (Over.pullback (c.π.app k₃))
    (Over.pullback (c.π.app ((s.next b₁).next b₂).k)) (stθ D c b₃) ((s.next b₁).next b₂).e hu₂
  obtain ⟨k₄, b₄, hF⟩ := ev_fAx D c hc (((s.next b₁).next b₂).next b₃).e hm₃ hu₃ hi₃
  letI : GrpObj ((Over.pullback (D.map b₄)).obj (((s.next b₁).next b₂).next b₃).M) :=
    ((grpAx_map_iff (Over.pullback (D.map b₄)) _ _ _).2 hF).grpObj
  refine ⟨(((s.next b₁).next b₂).next b₃).next b₄, this, fun P _ hP => ?_, isMonHom_descend
    (Over.pullback (D.map b₄)) (Over.pullback (c.π.app k₄))
    (Over.pullback (c.π.app (((s.next b₁).next b₂).next b₃).k)) (stθ D c b₄)
    (((s.next b₁).next b₂).next b₃).e hm₃ hu₃ hi₃ hF⟩
  exact FPStage.next_prop P _ b₄ (FPStage.next_prop P _ b₃ (FPStage.next_prop P _ b₂
    (FPStage.next_prop P s b₁ hP)))

end Descent

/-! ### A first finitely presented stage, smoothness, and the properness input -/

section Stages

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
  [∀ i, QuasiSeparatedSpace (D.obj i)] (c : Cone D) (hc : IsLimit c)

include hc in
/-- Every finitely presented object over `lim D` has a finitely presented stage model
(Stacks 01ZM, via the published H65/W01 port). -/
theorem nonempty_fpStage (N : Over c.pt) [LocallyOfFinitePresentation N.hom]
    [QuasiCompact N.hom] [QuasiSeparated N.hom] : Nonempty (FPStage D c N) := by
  haveI : EssentiallySmall.{u} I := inferInstance
  obtain ⟨i, Xi, hXi, ⟨e⟩⟩ :=
    AlgebraicGeometry.LimitDescent.exists_model_of_finitePresentation_of_essentiallySmall
      D c hc N ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨h1, h2, h3⟩ := hXi
  exact ⟨{ k := i, M := Xi, qc := h2, qs := h3, lfp := h1, e := e.symm }⟩

variable {D c}

include hc in
/-- Smoothness of the limit object holds at a later stage (Stacks 0C0C / EGA IV 17.7.8 (ii),
via the published H65/W01 port). -/
theorem exists_smooth_next {N : Over c.pt} [Smooth N.hom] (s : FPStage D c N) :
    ∃ (k' : I) (b : k' ⟶ s.k), Smooth (s.next b).M.hom := by
  haveI : CompactSpace s.M.left := QuasiCompact.compactSpace_of_compactSpace s.M.hom
  haveI : QuasiSeparatedSpace s.M.left := quasiSeparatedSpace_of_quasiSeparated s.M.hom
  let Y : Over (D.obj s.k) := Over.mk (𝟙 (D.obj s.k))
  let τ : s.M ⟶ Y := Over.homMk s.M.hom
  haveI : CompactSpace Y.left := by
    change CompactSpace (D.obj s.k)
    infer_instance
  haveI : QuasiSeparatedSpace Y.left := by
    change QuasiSeparatedSpace (D.obj s.k)
    infer_instance
  haveI : MorphismProperty.RespectsIso (@Smooth : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  haveI : LocallyOfFinitePresentation τ.left := inferInstanceAs (LocallyOfFinitePresentation s.M.hom)
  have hN : Smooth ((Over.pullback (c.π.app s.k)).obj s.M).hom :=
    prop_of_iso (@Smooth) s.e inferInstance
  haveI : Smooth ((Over.pullback (c.π.app s.k)).map τ).left :=
    (ZInQ.Contrib.CloudW01Spread.pullback_to_identity_iff (@Smooth) (c.π.app s.k) s.M).2 hN
  obtain ⟨j, a, hj⟩ :=
    AlgebraicGeometry.exists_smooth_baseChange_of_smooth_limitBaseChange D c s.k s.M Y τ hc
  exact ⟨j, a, (ZInQ.Contrib.CloudW01Spread.pullback_to_identity_iff (@Smooth) (D.map a) s.M).1 hj⟩

variable (D c)

/-- **Properness input (exact stage statement of EGA IV₃ 8.10.5 (xii) / Stacks 081F for the given
system).**  Kept explicit: it is not proved here (owned by the H65 row). -/
def ProperDescendsFor : Prop :=
  ∀ (i : I) (X : Over (D.obj i)), LocallyOfFinitePresentation X.hom → QuasiCompact X.hom →
    QuasiSeparated X.hom → IsProper ((Over.pullback (c.π.app i)).obj X).hom →
    ∃ (j : I) (a : j ⟶ i), IsProper ((Over.pullback (D.map a)).obj X).hom

variable {D c}

/-- With the properness input, properness of the limit object holds at a later stage. -/
theorem exists_proper_next (hpr : ProperDescendsFor D c) {N : Over c.pt} [IsProper N.hom]
    (s : FPStage D c N) : ∃ (k' : I) (b : k' ⟶ s.k), IsProper (s.next b).M.hom := by
  haveI : MorphismProperty.RespectsIso (@IsProper : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact hpr s.k s.M inferInstance inferInstance inferInstance
    (prop_of_iso (@IsProper) s.e inferInstance)

end Stages

/-- For universe `0` and a directed preorder, the published H65 leaf gives the properness input. -/
theorem properDescendsFor_of_ega (hpr : ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii)
    {J : Type} [Preorder J] [IsDirectedOrder J] [Nonempty J] (D : Jᵒᵖ ⥤ Scheme.{0})
    [∀ {i j : Jᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] (c : Cone D) (hc : IsLimit c) : ProperDescendsFor D c :=
  fun i X h1 h2 h3 h4 => hpr J D c hc i X h1 h2 h3 h4

/-! ### Main stage theorem -/

section Main

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ Scheme.{u}}
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
  [∀ i, QuasiSeparatedSpace (D.obj i)] {c : Cone D}

/-- **A smooth, finitely presented group object over `lim D` spreads to a smooth, finitely
presented group object over some stage, by an isomorphism of group objects.** -/
theorem exists_grpObj_smooth_stage (hc : IsLimit c) (N : Over c.pt) [GrpObj N]
    [LocallyOfFinitePresentation N.hom] [QuasiCompact N.hom] [QuasiSeparated N.hom]
    [Smooth N.hom] :
    ∃ (t : FPStage D c N) (_ : GrpObj t.M), Smooth t.M.hom ∧
      letI : GrpObj ((Over.pullback (c.π.app t.k)).obj t.M) := Functor.grpObjObj
      IsMonHom t.e.hom := by
  obtain ⟨s₀⟩ := nonempty_fpStage D c hc N
  obtain ⟨k₁, b₁, hs₁⟩ := exists_smooth_next hc s₀
  obtain ⟨t, hG, hP, hmon⟩ := exists_grp_stage hc (s₀.next b₁)
  exact ⟨t, hG, hP (@Smooth) hs₁, hmon⟩

/-- **The same, also proper, given the exact properness input for the system.** -/
theorem exists_grpObj_proper_smooth_stage (hc : IsLimit c) (hpr : ProperDescendsFor D c)
    (N : Over c.pt) [GrpObj N] [LocallyOfFinitePresentation N.hom] [QuasiCompact N.hom]
    [QuasiSeparated N.hom] [Smooth N.hom] [IsProper N.hom] :
    ∃ (t : FPStage D c N) (_ : GrpObj t.M), Smooth t.M.hom ∧ IsProper t.M.hom ∧
      letI : GrpObj ((Over.pullback (c.π.app t.k)).obj t.M) := Functor.grpObjObj
      IsMonHom t.e.hom := by
  obtain ⟨s₀⟩ := nonempty_fpStage D c hc N
  obtain ⟨k₁, b₁, hs₁⟩ := exists_smooth_next hc s₀
  obtain ⟨k₂, b₂, hp₂⟩ := exists_proper_next hpr (s₀.next b₁)
  have hs₂ : Smooth ((s₀.next b₁).next b₂).M.hom := FPStage.next_prop (@Smooth) _ b₂ hs₁
  obtain ⟨t, hG, hP, hmon⟩ := exists_grp_stage hc ((s₀.next b₁).next b₂)
  exact ⟨t, hG, hP (@Smooth) hs₂, hP (@IsProper) hp₂, hmon⟩

end Main

end ZInQ.Contrib.CloudR2NOS.Spreadout

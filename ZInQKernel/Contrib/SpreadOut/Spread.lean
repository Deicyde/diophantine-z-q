import Mathlib
import ZInQKernel.Contrib.SpreadOut.Limit

/-!
# Spreading out, III: smooth proper group schemes over a cofiltered limit of schemes

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task spread-out, 2026-11-13).

Three published theorems of EGA IV are stated as `Prop`s (leaves; not in Mathlib 4.35):
* `EGAIV_8_8_2_ii`  — descent of schemes of finite presentation (EGA IV₃ 8.8.2 (ii));
* `EGAIV_8_10_5_xii` — descent of properness (EGA IV₃ 8.10.5 (xii));
* `EGAIV_17_7_8_ii` — descent of smoothness (EGA IV₄ 17.7.8 (ii)).
From them and Mathlib's EGA IV₃ 8.8.2 (i) (in the `Over` form of `Limit.lean`) we prove
`exists_grpObj_descend`: a smooth proper group scheme over `lim D` is the base change of a smooth
proper group scheme over some stage `D k`, compatibly with the group structures.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

namespace ZInQ.Contrib.SpreadOut

/-! ### The three EGA IV leaves -/

/-- **EGA IV₃ 8.8.2 (ii) (LEAF, published; locator UNVERIFIED, quoted from memory; also
Stacks, Tag 01ZM, UNVERIFIED).**  Let `(Dᵢ)` be a cofiltered diagram of quasi-compact
quasi-separated schemes with affine transition maps and `c` a limit cone.  Every scheme `X` of
finite presentation (locally of finite presentation, quasi-compact, quasi-separated) over
`lim Dᵢ` is, up to isomorphism, the base change of a scheme `Xᵢ` of finite presentation over
some `Dᵢ`. -/
def EGAIV_8_8_2_ii : Prop :=
  ∀ (I : Type) [Category.{0} I] [IsCofiltered I] (D : I ⥤ Scheme.{0})
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] (c : Cone D), IsLimit c →
    ∀ (X : Over c.pt), LocallyOfFinitePresentation X.hom → QuasiCompact X.hom →
      QuasiSeparated X.hom →
      ∃ (i : I) (Xi : Over (D.obj i)), LocallyOfFinitePresentation Xi.hom ∧
        QuasiCompact Xi.hom ∧ QuasiSeparated Xi.hom ∧
        Nonempty ((Over.pullback (c.π.app i)).obj Xi ≅ X)

/-- **EGA IV₃ 8.10.5 (xii) (LEAF, published; locator UNVERIFIED, quoted from memory; also
Stacks, Tag 081F, UNVERIFIED).**  In the setting of `EGAIV_8_8_2_ii`, let `Xᵢ` be of finite
presentation over `Dᵢ`.  If the base change of `Xᵢ` to `lim D` is proper, then the base change
of `Xᵢ` to some `Dⱼ` (`j → i`) is proper. -/
def EGAIV_8_10_5_xii : Prop :=
  ∀ (I : Type) [Category.{0} I] [IsCofiltered I] (D : I ⥤ Scheme.{0})
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] (c : Cone D), IsLimit c →
    ∀ (i : I) (Xi : Over (D.obj i)), LocallyOfFinitePresentation Xi.hom → QuasiCompact Xi.hom →
      QuasiSeparated Xi.hom → IsProper ((Over.pullback (c.π.app i)).obj Xi).hom →
      ∃ (j : I) (a : j ⟶ i), IsProper ((Over.pullback (D.map a)).obj Xi).hom

/-- **EGA IV₄ 17.7.8 (ii) (LEAF, published; locator UNVERIFIED, quoted from memory; also
Stacks, Tag 07RP, UNVERIFIED).**  In the setting of `EGAIV_8_8_2_ii`, let `Xᵢ` be of finite
presentation over `Dᵢ`.  If the base change of `Xᵢ` to `lim D` is smooth, then the base change
of `Xᵢ` to some `Dⱼ` (`j → i`) is smooth. -/
def EGAIV_17_7_8_ii : Prop :=
  ∀ (I : Type) [Category.{0} I] [IsCofiltered I] (D : I ⥤ Scheme.{0})
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] (c : Cone D), IsLimit c →
    ∀ (i : I) (Xi : Over (D.obj i)), LocallyOfFinitePresentation Xi.hom → QuasiCompact Xi.hom →
      QuasiSeparated Xi.hom → Smooth ((Over.pullback (c.π.app i)).obj Xi).hom →
      ∃ (j : I) (a : j ⟶ i), Smooth ((Over.pullback (D.map a)).obj Xi).hom

/-! ### Finiteness instances for products and base changes in `Over S` -/

section Instances

variable {S T : Scheme.{0}}

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

instance proper_pb (f : T ⟶ S) (X : Over S) [IsProper X.hom] :
    IsProper ((Over.pullback f).obj X).hom :=
  show IsProper (pullback.snd X.hom f) from inferInstance

instance smooth_pb (f : T ⟶ S) (X : Over S) [Smooth X.hom] :
    Smooth ((Over.pullback f).obj X).hom :=
  show Smooth (pullback.snd X.hom f) from inferInstance

theorem isProper_of_iso {X Y : Over S} (e : X ≅ Y) [IsProper Y.hom] : IsProper X.hom := by
  rw [← Over.w e.hom]
  haveI : IsIso e.hom.left := ⟨e.inv.left, by rw [← Over.comp_left, e.hom_inv_id]; rfl,
    by rw [← Over.comp_left, e.inv_hom_id]; rfl⟩
  infer_instance

theorem smooth_of_iso {X Y : Over S} (e : X ≅ Y) [Smooth Y.hom] : Smooth X.hom := by
  rw [← Over.w e.hom]
  haveI : IsIso e.hom.left := ⟨e.inv.left, by rw [← Over.comp_left, e.hom_inv_id]; rfl,
    by rw [← Over.comp_left, e.inv_hom_id]; rfl⟩
  infer_instance

end Instances

/-! ### Eventually-true predicates along a cofiltered category -/

section Eventually

variable {I : Type} [Category.{0} I]

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

/-! ### The descent of a smooth proper group scheme -/

section Descent

variable {I : Type} [Category.{0} I] [IsCofiltered I] (D : I ⥤ Scheme.{0})
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

/-- A stage object with an identification of its base change with `N`. -/
structure Stage (N : Over c.pt) where
  k : I
  M : Over (D.obj k)
  qc : QuasiCompact M.hom
  qs : QuasiSeparated M.hom
  lfp : LocallyOfFinitePresentation M.hom
  proper : IsProper M.hom
  smooth : Smooth M.hom
  e : (Over.pullback (c.π.app k)).obj M ≅ N

attribute [instance] Stage.qc Stage.qs Stage.lfp Stage.proper Stage.smooth

variable {D c}

/-- Base change of a stage along `b : k' ⟶ k`. -/
noncomputable def Stage.next {N : Over c.pt} (s : Stage D c N) {k' : I} (b : k' ⟶ s.k) :
    Stage D c N where
  k := k'
  M := (Over.pullback (D.map b)).obj s.M
  qc := inferInstance
  qs := inferInstance
  lfp := inferInstance
  proper := inferInstance
  smooth := inferInstance
  e := (stθ D c b).app s.M ≪≫ s.e

include hc in
theorem exists_mul {N : Over c.pt} [GrpObj N] (s : Stage D c N) :
    ∃ (k' : I) (b : k' ⟶ s.k) (m : (s.next b).M ⊗ (s.next b).M ⟶ (s.next b).M),
      CompatM _ (s.next b).e m := by
  obtain ⟨k', b, g', hg⟩ := exists_lift D c hc (s.M ⊗ s.M) s.M
    (inv (Functor.LaxMonoidal.μ (Over.pullback (c.π.app s.k)) s.M s.M) ≫
      (s.e.hom ⊗ₘ s.e.hom) ≫ μ[N] ≫ s.e.inv)
  exact ⟨k', b, _, compatM_of_lift (Over.pullback (D.map b)) (Over.pullback (c.π.app k'))
    (Over.pullback (c.π.app s.k)) (stθ D c b) s.e hg⟩

include hc in
theorem exists_one {N : Over c.pt} [GrpObj N] (s : Stage D c N) :
    ∃ (k' : I) (b : k' ⟶ s.k) (u : 𝟙_ _ ⟶ (s.next b).M), CompatU _ (s.next b).e u := by
  obtain ⟨k', b, g', hg⟩ := exists_lift D c hc (𝟙_ _) s.M
    (inv (Functor.LaxMonoidal.ε (Over.pullback (c.π.app s.k))) ≫ η[N] ≫ s.e.inv)
  exact ⟨k', b, _, compatU_of_lift (Over.pullback (D.map b)) (Over.pullback (c.π.app k'))
    (Over.pullback (c.π.app s.k)) (stθ D c b) s.e hg⟩

include hc in
theorem exists_inv {N : Over c.pt} [GrpObj N] (s : Stage D c N) :
    ∃ (k' : I) (b : k' ⟶ s.k) (i : (s.next b).M ⟶ (s.next b).M), CompatI _ (s.next b).e i := by
  obtain ⟨k', b, g', hg⟩ := exists_lift D c hc s.M s.M (s.e.hom ≫ ι[N] ≫ s.e.inv)
  exact ⟨k', b, _, compatI_of_lift (Over.pullback (D.map b)) (Over.pullback (c.π.app k'))
    (Over.pullback (c.π.app s.k)) (stθ D c b) s.e hg⟩

include hc in
/-- **Descent of a group structure to a finite stage.**  A smooth proper stage object whose base
change to `lim D` is identified with a group object `N` carries, after a further base change, a
group structure for which the identification is a morphism of group objects. -/
theorem exists_grp_stage {N : Over c.pt} [GrpObj N] (s : Stage D c N) :
    ∃ (t : Stage D c N) (_ : GrpObj t.M),
      letI : GrpObj ((Over.pullback (c.π.app t.k)).obj t.M) := Functor.grpObjObj
      IsMonHom t.e.hom := by
  -- multiplication
  obtain ⟨k₁, b₁, m₁, hm₁⟩ := exists_mul hc s
  -- unit
  obtain ⟨k₂, b₂, u₂, hu₂⟩ := exists_one hc (s.next b₁)
  have hm₂ := compatM_transport (Over.pullback (D.map b₂)) (Over.pullback (c.π.app k₂))
    (Over.pullback (c.π.app (s.next b₁).k)) (stθ D c b₂) (s.next b₁).e hm₁
  -- inverse
  obtain ⟨k₃, b₃, i₃, hi₃⟩ := exists_inv hc ((s.next b₁).next b₂)
  have hm₃ := compatM_transport (Over.pullback (D.map b₃)) (Over.pullback (c.π.app k₃))
    (Over.pullback (c.π.app ((s.next b₁).next b₂).k)) (stθ D c b₃) ((s.next b₁).next b₂).e hm₂
  have hu₃ := compatU_transport (Over.pullback (D.map b₃)) (Over.pullback (c.π.app k₃))
    (Over.pullback (c.π.app ((s.next b₁).next b₂).k)) (stθ D c b₃) ((s.next b₁).next b₂).e hu₂
  -- axioms
  obtain ⟨k₄, b₄, hF⟩ := ev_fAx D c hc (((s.next b₁).next b₂).next b₃).e hm₃ hu₃ hi₃
  letI : GrpObj ((Over.pullback (D.map b₄)).obj (((s.next b₁).next b₂).next b₃).M) :=
    ((grpAx_map_iff (Over.pullback (D.map b₄)) _ _ _).2 hF).grpObj
  exact ⟨(((s.next b₁).next b₂).next b₃).next b₄, this, isMonHom_descend
    (Over.pullback (D.map b₄)) (Over.pullback (c.π.app k₄))
    (Over.pullback (c.π.app (((s.next b₁).next b₂).next b₃).k)) (stθ D c b₄)
    (((s.next b₁).next b₂).next b₃).e hm₃ hu₃ hi₃ hF⟩

variable (D c)

include hc in
/-- **Spreading out a smooth proper group scheme (from the three EGA IV leaves).**  Let `D` be a
cofiltered diagram of qcqs schemes with affine transition maps and limit `c`.  A smooth proper
group scheme `B` over `lim D` is the base change of a smooth proper group scheme `G` over some
stage `D k`, by an isomorphism of group schemes. -/
theorem exists_grpObj_descend (h882 : EGAIV_8_8_2_ii) (hpr : EGAIV_8_10_5_xii)
    (hsm : EGAIV_17_7_8_ii) (B : Over c.pt) [GrpObj B] [IsProper B.hom] [Smooth B.hom] :
    ∃ (k : I) (G : Over (D.obj k)) (_ : GrpObj G) (_ : Smooth G.hom) (_ : IsProper G.hom)
      (gen : (Over.pullback (c.π.app k)).obj G ≅ B),
      letI : GrpObj ((Over.pullback (c.π.app k)).obj G) := Functor.grpObjObj
      IsMonHom gen.hom := by
  obtain ⟨i₀, X₀, hl₀, hq₀, hs₀, ⟨e₀⟩⟩ := h882 I D c hc B inferInstance inferInstance
    inferInstance
  have hp₀ : IsProper ((Over.pullback (c.π.app i₀)).obj X₀).hom := isProper_of_iso e₀
  obtain ⟨i₁, a₁, hp₁⟩ := hpr I D c hc i₀ X₀ hl₀ hq₀ hs₀ hp₀
  set X₁ := (Over.pullback (D.map a₁)).obj X₀
  set e₁ : (Over.pullback (c.π.app i₁)).obj X₁ ≅ B := (stθ D c a₁).app X₀ ≪≫ e₀
  have hsm₁ : Smooth ((Over.pullback (c.π.app i₁)).obj X₁).hom := smooth_of_iso e₁
  obtain ⟨i₂, a₂, hs₂⟩ := hsm I D c hc i₁ X₁ inferInstance inferInstance inferInstance hsm₁
  let s : Stage D c B :=
    { k := i₂
      M := (Over.pullback (D.map a₂)).obj X₁
      qc := inferInstance
      qs := inferInstance
      lfp := inferInstance
      proper := inferInstance
      smooth := hs₂
      e := (stθ D c a₂).app X₁ ≪≫ e₁ }
  obtain ⟨t, hG, ht⟩ := exists_grp_stage hc s
  exact ⟨t.k, t.M, hG, t.smooth, t.proper, t.e, ht⟩

end Descent

end ZInQ.Contrib.SpreadOut

/-
# H5 / NOS round 2, lane 3 (`Spreadout/`): spreading isomorphisms between stage models

New glue (no vendored source in this file).

For a cofiltered system `D` of qcqs schemes with affine transition maps and limit `c`, a morphism
`g : M ⟶ M'` between objects over a stage `D k` *models* a morphism `f : N ⟶ N'` over `lim D`
under identifications `e : (π k)^* M ≅ N`, `e' : (π k)^* M' ≅ N'` when `(π k)^* g ≫ e' = e ≫ f`
(`CompatMap`).  Models exist after a further base change (`exists_compatMap`, from the published
`ZInQ.Contrib.SpreadOut.exists_lift`, EGA IV₃ 8.8.2 (i)), are preserved by base change
(`CompatMap.next`), compose, and two models of the same `f` agree after a further base change
(`CompatMap.ev_eq`, from `ZInQ.Contrib.SpreadOut.exists_map_eq`).  Hence an isomorphism over the
limit spreads to an isomorphism over some stage (`exists_iso_compatMap`, EGA IV₃ 8.8.2.5), and a
morphism of group objects to a morphism of group objects (`exists_isMonHom_next`).
-/
import ZInQKernel.Contrib.CloudR2NOS.Spreadout.GroupStage

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace ZInQ.Contrib.CloudR2NOS.Spreadout

universe u

open ZInQ.Contrib.SpreadOut (stθ exists_lift exists_map_eq pullback_map_eq_of_comp)

/-! ### Components of natural transformations between monoidal functors are monoid morphisms -/

section MonHomApp

variable {C C' E : Type*} [Category C] [Category C'] [Category E] [CartesianMonoidalCategory C]
  [CartesianMonoidalCategory C'] [CartesianMonoidalCategory E]

/-- A component `τ.app X : G (F X) ⟶ H X` of a natural transformation `τ : F ⋙ G ⟶ H` of monoidal
functors is a morphism of monoid objects for the iterated image structure on `G (F X)`. -/
theorem isMonHom_app_comp {F : C ⥤ C'} {G : C' ⥤ E} {H : C ⥤ E} [F.Monoidal] [G.Monoidal]
    [H.Monoidal] (τ : F ⋙ G ⟶ H) (X : C) [MonObj X] :
    IsMonHom (M := G.obj (F.obj X)) (N := H.obj X) (τ.app X) := by
  have hu := NatTrans.IsMonoidal.unit (τ := τ)
  have ht := NatTrans.IsMonoidal.tensor (τ := τ) X X
  simp only [Functor.LaxMonoidal.comp_ε, Functor.LaxMonoidal.comp_μ, Category.assoc] at hu ht
  have hn₁ := τ.naturality η[X]
  have hn₂ := τ.naturality μ[X]
  simp only [Functor.comp_map] at hn₁ hn₂
  constructor
  · change (Functor.LaxMonoidal.ε G ≫ G.map (Functor.LaxMonoidal.ε F ≫ F.map η[X])) ≫ τ.app X =
      Functor.LaxMonoidal.ε H ≫ H.map η[X]
    rw [Functor.map_comp, Category.assoc, Category.assoc, hn₁, ← Category.assoc,
      ← Category.assoc, Category.assoc (Functor.LaxMonoidal.ε G), hu]
  · change (Functor.LaxMonoidal.μ G (F.obj X) (F.obj X) ≫
        G.map (Functor.LaxMonoidal.μ F X X ≫ F.map μ[X])) ≫ τ.app X =
      (τ.app X ⊗ₘ τ.app X) ≫ Functor.LaxMonoidal.μ H X X ≫ H.map μ[X]
    rw [Functor.map_comp, Category.assoc, Category.assoc, hn₂, ← Category.assoc,
      ← Category.assoc, Category.assoc (Functor.LaxMonoidal.μ G _ _), ht, Category.assoc]

/-- A component `τ.app X : H X ⟶ G (F X)` of a natural transformation `τ : H ⟶ F ⋙ G` of monoidal
functors is a morphism of monoid objects for the iterated image structure on `G (F X)`. -/
theorem isMonHom_app_to_comp {F : C ⥤ C'} {G : C' ⥤ E} {H : C ⥤ E} [F.Monoidal] [G.Monoidal]
    [H.Monoidal] (τ : H ⟶ F ⋙ G) (X : C) [MonObj X] :
    IsMonHom (M := H.obj X) (N := G.obj (F.obj X)) (τ.app X) := by
  have hu := NatTrans.IsMonoidal.unit (τ := τ)
  have ht := NatTrans.IsMonoidal.tensor (τ := τ) X X
  simp only [Functor.LaxMonoidal.comp_ε, Functor.LaxMonoidal.comp_μ] at hu ht
  have hn₁ := τ.naturality η[X]
  have hn₂ := τ.naturality μ[X]
  simp only [Functor.comp_map] at hn₁ hn₂
  constructor
  · change (Functor.LaxMonoidal.ε H ≫ H.map η[X]) ≫ τ.app X =
      Functor.LaxMonoidal.ε G ≫ G.map (Functor.LaxMonoidal.ε F ≫ F.map η[X])
    rw [Category.assoc, hn₁, ← Category.assoc, hu, Functor.map_comp, Category.assoc]
  · change (Functor.LaxMonoidal.μ H X X ≫ H.map μ[X]) ≫ τ.app X =
      (τ.app X ⊗ₘ τ.app X) ≫ Functor.LaxMonoidal.μ G (F.obj X) (F.obj X) ≫
        G.map (Functor.LaxMonoidal.μ F X X ≫ F.map μ[X])
    rw [Category.assoc, hn₂, ← Category.assoc, ht, Functor.map_comp]
    simp only [Category.assoc]

/-- Composition of monoid morphisms, with the monoid structures fixed by the hypotheses. -/
theorem isMonHom_comp' {M₁ M₂ M₃ : E} {i₁ : MonObj M₁} {i₂ : MonObj M₂} {i₃ : MonObj M₃}
    {f : M₁ ⟶ M₂} {g : M₂ ⟶ M₃} (hf : IsMonHom f) (hg : IsMonHom g) : IsMonHom (f ≫ g) :=
  inferInstance

/-- The image of a monoid morphism under a monoidal functor, for the image structures. -/
theorem isMonHom_map' (P : C ⥤ E) [P.Monoidal] {M₁ M₂ : C} {i₁ : MonObj M₁} {i₂ : MonObj M₂}
    {f : M₁ ⟶ M₂} (hf : IsMonHom f) : IsMonHom (P.map f) :=
  inferInstance

/-- The inverse of an isomorphism of monoid objects. -/
theorem isMonHom_inv' {M₁ M₂ : E} {i₁ : MonObj M₁} {i₂ : MonObj M₂} (e : M₁ ≅ M₂)
    (he : IsMonHom e.hom) : IsMonHom e.inv :=
  inferInstance

end MonHomApp

section CompatMap

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)

/-- `g : M ⟶ M'` over the stage `D k` models `f : N ⟶ N'` over `lim D` under `e`, `e'`. -/
def CompatMap {k : I} {M M' : Over (D.obj k)} {N N' : Over c.pt}
    (e : (Over.pullback (c.π.app k)).obj M ≅ N) (e' : (Over.pullback (c.π.app k)).obj M' ≅ N')
    (f : N ⟶ N') (g : M ⟶ M') : Prop :=
  (Over.pullback (c.π.app k)).map g ≫ e'.hom = e.hom ≫ f

/-- The comparison `θ_b : (π k')^* (D b)^* M ≅ (π k)^* M`, stated in iterated form. -/
def stθIso {k k' : I} (b : k' ⟶ k) (M : Over (D.obj k)) :
    (Over.pullback (c.π.app k')).obj ((Over.pullback (D.map b)).obj M) ≅
      (Over.pullback (c.π.app k)).obj M :=
  (stθ D c b).app M

variable {D c}

theorem CompatMap.id {k : I} {M : Over (D.obj k)} {N : Over c.pt}
    (e : (Over.pullback (c.π.app k)).obj M ≅ N) : CompatMap D c e e (𝟙 N) (𝟙 M) := by
  simp [CompatMap]

theorem CompatMap.comp {k : I} {M M' M'' : Over (D.obj k)} {N N' N'' : Over c.pt}
    {e : (Over.pullback (c.π.app k)).obj M ≅ N} {e' : (Over.pullback (c.π.app k)).obj M' ≅ N'}
    {e'' : (Over.pullback (c.π.app k)).obj M'' ≅ N''} {f : N ⟶ N'} {f' : N' ⟶ N''}
    {g : M ⟶ M'} {g' : M' ⟶ M''} (h : CompatMap D c e e' f g) (h' : CompatMap D c e' e'' f' g') :
    CompatMap D c e e'' (f ≫ f') (g ≫ g') := by
  unfold CompatMap at h h' ⊢
  rw [Functor.map_comp, Category.assoc, h', ← Category.assoc, h, Category.assoc]

theorem CompatMap.map_eq {k : I} {M M' : Over (D.obj k)} {N N' : Over c.pt}
    {e : (Over.pullback (c.π.app k)).obj M ≅ N} {e' : (Over.pullback (c.π.app k)).obj M' ≅ N'}
    {f : N ⟶ N'} {g₁ g₂ : M ⟶ M'} (h₁ : CompatMap D c e e' f g₁)
    (h₂ : CompatMap D c e e' f g₂) :
    (Over.pullback (c.π.app k)).map g₁ = (Over.pullback (c.π.app k)).map g₂ := by
  unfold CompatMap at h₁ h₂
  rw [← cancel_mono e'.hom, h₁, h₂]

theorem CompatMap.next {k k' : I} (b : k' ⟶ k) {M M' : Over (D.obj k)} {N N' : Over c.pt}
    {e : (Over.pullback (c.π.app k)).obj M ≅ N} {e' : (Over.pullback (c.π.app k)).obj M' ≅ N'}
    {f : N ⟶ N'} {g : M ⟶ M'} (h : CompatMap D c e e' f g) :
    CompatMap D c (stθIso D c b M ≪≫ e) (stθIso D c b M' ≪≫ e') f
      ((Over.pullback (D.map b)).map g) := by
  unfold CompatMap at h ⊢
  unfold stθIso
  have hn := (stθ D c b).hom.naturality g
  simp only [Functor.comp_map] at hn
  simp only [Iso.trans_hom, Iso.app_hom]
  rw [reassoc_of% hn, h, Category.assoc]

variable [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]

/-- Models exist after a further base change. -/
theorem exists_compatMap (hc : IsLimit c) {k : I} (M M' : Over (D.obj k)) [QuasiCompact M.hom]
    [QuasiSeparated M.hom] [LocallyOfFinitePresentation M'.hom] {N N' : Over c.pt}
    (e : (Over.pullback (c.π.app k)).obj M ≅ N) (e' : (Over.pullback (c.π.app k)).obj M' ≅ N')
    (f : N ⟶ N') :
    ∃ (k' : I) (b : k' ⟶ k)
      (g : (Over.pullback (D.map b)).obj M ⟶ (Over.pullback (D.map b)).obj M'),
      CompatMap D c (stθIso D c b M ≪≫ e) (stθIso D c b M' ≪≫ e') f g := by
  obtain ⟨k', b, g, hg⟩ := exists_lift D c hc M M' (e.hom ≫ f ≫ e'.inv)
  refine ⟨k', b, g, ?_⟩
  unfold CompatMap stθIso
  rw [hg]
  simp

/-- Two models of the same morphism agree after a further base change (eventually). -/
theorem CompatMap.ev_eq (hc : IsLimit c) {k : I} {M M' : Over (D.obj k)} [QuasiCompact M.hom]
    [LocallyOfFiniteType M'.hom] {N N' : Over c.pt}
    {e : (Over.pullback (c.π.app k)).obj M ≅ N} {e' : (Over.pullback (c.π.app k)).obj M' ≅ N'}
    {f : N ⟶ N'} {g₁ g₂ : M ⟶ M'} (h₁ : CompatMap D c e e' f g₁)
    (h₂ : CompatMap D c e e' f g₂) :
    Ev (fun {k'} (b : k' ⟶ k) =>
      (Over.pullback (D.map b)).map g₁ = (Over.pullback (D.map b)).map g₂) :=
  ev_map_eq D c hc g₁ g₂ (h₁.map_eq h₂)

/-- **Spreading an isomorphism (EGA IV₃ 8.8.2.5).**  An isomorphism over the limit between base
changes of finitely presented stage objects is modelled by an isomorphism over a later stage,
reached by three successive base changes. -/
theorem exists_iso_compatMap (hc : IsLimit c) {k : I} (M M' : Over (D.obj k))
    [QuasiCompact M.hom] [QuasiSeparated M.hom] [LocallyOfFinitePresentation M.hom]
    [QuasiCompact M'.hom] [QuasiSeparated M'.hom] [LocallyOfFinitePresentation M'.hom]
    {N N' : Over c.pt} (e : (Over.pullback (c.π.app k)).obj M ≅ N)
    (e' : (Over.pullback (c.π.app k)).obj M' ≅ N') (f : N ≅ N') :
    ∃ (k₁ : I) (b₁ : k₁ ⟶ k) (k₂ : I) (b₂ : k₂ ⟶ k₁) (k₃ : I) (b₃ : k₃ ⟶ k₂)
      (φ : (Over.pullback (D.map b₃)).obj ((Over.pullback (D.map b₂)).obj
          ((Over.pullback (D.map b₁)).obj M)) ≅
        (Over.pullback (D.map b₃)).obj ((Over.pullback (D.map b₂)).obj
          ((Over.pullback (D.map b₁)).obj M'))),
      CompatMap D c
        (stθIso D c b₃ _ ≪≫ stθIso D c b₂ _ ≪≫ stθIso D c b₁ M ≪≫ e)
        (stθIso D c b₃ _ ≪≫ stθIso D c b₂ _ ≪≫ stθIso D c b₁ M' ≪≫ e') f.hom φ.hom := by
  -- a model `g` of `f.hom`
  obtain ⟨k₁, b₁, g, hg⟩ := exists_compatMap hc M M' e e' f.hom
  -- a model `h` of `f.inv`, one stage further
  obtain ⟨k₂, b₂, h, hh⟩ := exists_compatMap hc ((Over.pullback (D.map b₁)).obj M')
    ((Over.pullback (D.map b₁)).obj M) (stθIso D c b₁ M' ≪≫ e') (stθIso D c b₁ M ≪≫ e)
    f.inv
  have hg₂ := hg.next b₂
  -- both composites model identities
  have h₁ := hg₂.comp hh
  have h₂ := hh.comp hg₂
  rw [f.hom_inv_id] at h₁
  rw [f.inv_hom_id] at h₂
  obtain ⟨k₃, b₃, hb⟩ := ((h₁.ev_eq hc (CompatMap.id _)).and
    (h₂.ev_eq hc (CompatMap.id _))).exists
  obtain ⟨hb₁, hb₂⟩ := hb
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at hb₁ hb₂
  refine ⟨k₁, b₁, k₂, b₂, k₃, b₃,
    { hom := (Over.pullback (D.map b₃)).map ((Over.pullback (D.map b₂)).map g)
      inv := (Over.pullback (D.map b₃)).map h
      hom_inv_id := hb₁
      inv_hom_id := hb₂ }, ?_⟩
  exact hg₂.next b₃

end CompatMap


section MonHom

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} {c : Cone D}

/-- The base-changed identification of a group stage is again a morphism of group objects. -/
theorem isMonHom_next {k k' : I} (b : k' ⟶ k) {M : Over (D.obj k)} [MonObj M] {N : Over c.pt}
    [MonObj N] {e : (Over.pullback (c.π.app k)).obj M ≅ N} (he : IsMonHom e.hom) :
    IsMonHom (M := (Over.pullback (c.π.app k')).obj ((Over.pullback (D.map b)).obj M)) (N := N)
      (stθIso D c b M ≪≫ e).hom :=
  isMonHom_comp' (isMonHom_app_comp (stθ D c b).hom M) he

/-- The unit equation of a morphism of group objects holds over the limit for a model of a
morphism of group objects. Group structures on base changes are the image structures. -/
theorem compat_one_eq {k : I} {M M' : Over (D.obj k)} [MonObj M] [MonObj M']
    {N N' : Over c.pt} [MonObj N] [MonObj N']
    {e : (Over.pullback (c.π.app k)).obj M ≅ N} {e' : (Over.pullback (c.π.app k)).obj M' ≅ N'}
    (he : IsMonHom e.hom) (he' : IsMonHom e'.hom) {f : N ⟶ N'} (hf : IsMonHom f)
    {φ : M ⟶ M'} (hφ : CompatMap D c e e' f φ) :
    (Over.pullback (c.π.app k)).map (η[M] ≫ φ) = (Over.pullback (c.π.app k)).map η[M'] := by
  have hφ' : (Over.pullback (c.π.app k)).map φ ≫ e'.hom = e.hom ≫ f := hφ
  have h1 : η[(Over.pullback (c.π.app k)).obj M] ≫ e.hom = η[N] := IsMonHom.one_hom e.hom
  have h2 : η[N] ≫ f = η[N'] := IsMonHom.one_hom f
  have h3 : η[(Over.pullback (c.π.app k)).obj M'] ≫ e'.hom = η[N'] := IsMonHom.one_hom e'.hom
  have key : η[(Over.pullback (c.π.app k)).obj M] ≫ (Over.pullback (c.π.app k)).map φ ≫ e'.hom =
      η[(Over.pullback (c.π.app k)).obj M'] ≫ e'.hom := by
    rw [hφ', ← Category.assoc, h1, h2, h3]
  rw [Functor.obj.η_def, Functor.obj.η_def] at key
  rw [CategoryTheory.Functor.map_comp]
  rw [← cancel_epi (Functor.LaxMonoidal.ε (Over.pullback (c.π.app k))), ← cancel_mono e'.hom]
  simpa only [Category.assoc] using key

/-- The multiplication equation of a morphism of group objects holds over the limit for a model
of a morphism of group objects. -/
theorem compat_mul_eq {k : I} {M M' : Over (D.obj k)} [MonObj M] [MonObj M']
    {N N' : Over c.pt} [MonObj N] [MonObj N']
    {e : (Over.pullback (c.π.app k)).obj M ≅ N} {e' : (Over.pullback (c.π.app k)).obj M' ≅ N'}
    (he : IsMonHom e.hom) (he' : IsMonHom e'.hom) {f : N ⟶ N'} (hf : IsMonHom f)
    {φ : M ⟶ M'} (hφ : CompatMap D c e e' f φ) :
    (Over.pullback (c.π.app k)).map (μ[M] ≫ φ) =
      (Over.pullback (c.π.app k)).map ((φ ⊗ₘ φ) ≫ μ[M']) := by
  have hφ' : (Over.pullback (c.π.app k)).map φ ≫ e'.hom = e.hom ≫ f := hφ
  have h1 : μ[(Over.pullback (c.π.app k)).obj M] ≫ e.hom = (e.hom ⊗ₘ e.hom) ≫ μ[N] :=
    IsMonHom.mul_hom e.hom
  have h2 : μ[N] ≫ f = (f ⊗ₘ f) ≫ μ[N'] := IsMonHom.mul_hom f
  have h3 : μ[(Over.pullback (c.π.app k)).obj M'] ≫ e'.hom = (e'.hom ⊗ₘ e'.hom) ≫ μ[N'] :=
    IsMonHom.mul_hom e'.hom
  have key : μ[(Over.pullback (c.π.app k)).obj M] ≫ (Over.pullback (c.π.app k)).map φ ≫ e'.hom =
      ((Over.pullback (c.π.app k)).map φ ⊗ₘ (Over.pullback (c.π.app k)).map φ) ≫
        μ[(Over.pullback (c.π.app k)).obj M'] ≫ e'.hom := by
    calc μ[(Over.pullback (c.π.app k)).obj M] ≫ (Over.pullback (c.π.app k)).map φ ≫ e'.hom
        = μ[(Over.pullback (c.π.app k)).obj M] ≫ e.hom ≫ f := by rw [hφ']
      _ = (e.hom ⊗ₘ e.hom) ≫ (f ⊗ₘ f) ≫ μ[N'] := by
          rw [← Category.assoc, h1, Category.assoc, h2]
      _ = ((e.hom ≫ f) ⊗ₘ (e.hom ≫ f)) ≫ μ[N'] := by
          rw [← Category.assoc, tensorHom_comp_tensorHom]
      _ = (((Over.pullback (c.π.app k)).map φ ≫ e'.hom) ⊗ₘ
            ((Over.pullback (c.π.app k)).map φ ≫ e'.hom)) ≫ μ[N'] := by rw [hφ']
      _ = ((Over.pullback (c.π.app k)).map φ ⊗ₘ (Over.pullback (c.π.app k)).map φ) ≫
            μ[(Over.pullback (c.π.app k)).obj M'] ≫ e'.hom := by
          rw [h3, ← Category.assoc, tensorHom_comp_tensorHom]
  rw [Functor.obj.μ_def, Functor.obj.μ_def] at key
  rw [← cancel_epi (Functor.LaxMonoidal.μ (Over.pullback (c.π.app k)) M M), ← cancel_mono e'.hom]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc] at key ⊢
  rw [key, Functor.LaxMonoidal.μ_natural_assoc]

variable [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]

/-- **Spreading a morphism of group objects.**  A model of a morphism of group objects is a
morphism of group objects (for the image group structures) after a further base change. -/
theorem exists_isMonHom_next (hc : IsLimit c) {k : I} {M M' : Over (D.obj k)} [MonObj M]
    [MonObj M'] [QuasiCompact M.hom] [QuasiSeparated M.hom] [LocallyOfFiniteType M'.hom]
    {N N' : Over c.pt} [MonObj N] [MonObj N']
    {e : (Over.pullback (c.π.app k)).obj M ≅ N} {e' : (Over.pullback (c.π.app k)).obj M' ≅ N'}
    (he : IsMonHom e.hom) (he' : IsMonHom e'.hom) {f : N ⟶ N'} (hf : IsMonHom f)
    {φ : M ⟶ M'} (hφ : CompatMap D c e e' f φ) :
    ∃ (k' : I) (b : k' ⟶ k), IsMonHom ((Over.pullback (D.map b)).map φ) := by
  obtain ⟨k', b, h1, h2⟩ := ((ev_map_eq D c hc _ _ (compat_one_eq he he' hf hφ)).and
    (ev_map_eq D c hc _ _ (compat_mul_eq he he' hf hφ))).exists
  refine ⟨k', b, ⟨?_, ?_⟩⟩
  · rw [Functor.obj.η_def, Functor.obj.η_def, Category.assoc,
      ← CategoryTheory.Functor.map_comp, h1]
  · rw [Functor.obj.μ_def, Functor.obj.μ_def, Category.assoc,
      ← CategoryTheory.Functor.map_comp, h2, CategoryTheory.Functor.map_comp,
      Functor.LaxMonoidal.μ_natural_assoc]

end MonHom

end ZInQ.Contrib.CloudR2NOS.Spreadout

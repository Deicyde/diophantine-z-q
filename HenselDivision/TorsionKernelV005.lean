import Mathlib.AlgebraicGeometry.Group.Abelian
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
# The kernel of multiplication by `n` on a group object, as an actual pullback

For a monoid object `G` of a cartesian monoidal category `C` with pullbacks, multiplication by `n`
is `[n] = (𝟙 G)^n` in the monoid `Hom(G, G)`, and the torsion object is the fibre product
`G[n] = G ×_{[n], G, η} 𝟙`. Its `T`-points are exactly the `T`-points of `G` killed by `n`
(`torsionKerHomEquiv`), naturally in `T`.

Over a base scheme `S`: if `G → S` is separated, the unit section is a closed immersion and so is
`G[n] → G`; if `[n]` is étale, then `G[n] → S` is étale, being the base change of `[n]` along the
unit section. Whether `[n]` is étale is a property of the actual group scheme (true for smooth
commutative group schemes with `n` invertible on `S`); it is kept as an explicit hypothesis here,
not derived.

Edition V005: the base change of the identity uses `MorphismProperty.of_isPullback`.
Statements as in V001.
-/

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped MonObj

namespace HenselDivision

section Generic

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- Multiplication by `n` on a monoid object: `(𝟙 G)^n` in `Hom(G, G)`. -/
noncomputable def powHom (G : C) [MonObj G] (n : ℕ) : G ⟶ G := (𝟙 G) ^ n

lemma comp_powHom {G T : C} [MonObj G] (n : ℕ) (f : T ⟶ G) : f ≫ powHom G n = f ^ n := by
  rw [powHom, MonObj.comp_pow, Category.comp_id]

variable [HasPullbacks C]

/-- The `n`-torsion object `G[n] = G ×_{[n], G, η} 𝟙`. -/
noncomputable abbrev torsionKer (G : C) [MonObj G] (n : ℕ) : C := pullback (powHom G n) η[G]

/-- The inclusion `G[n] → G`. -/
noncomputable abbrev torsionKerι (G : C) [MonObj G] (n : ℕ) : torsionKer G n ⟶ G :=
  pullback.fst _ _

lemma torsionKer_isPullback (G : C) [MonObj G] (n : ℕ) :
    IsPullback (torsionKerι G n) (pullback.snd (powHom G n) η[G]) (powHom G n) η[G] :=
  IsPullback.of_hasPullback _ _

lemma torsionKerι_pow {G T : C} [MonObj G] (n : ℕ) (g : T ⟶ torsionKer G n) :
    (g ≫ torsionKerι G n) ^ n = 1 := by
  rw [← comp_powHom, Category.assoc, torsionKerι, pullback.condition, ← Category.assoc,
    CategoryTheory.Hom.one_def, toUnit_unique (g ≫ pullback.snd _ _) (toUnit T)]

/-- **The functor of points of `G[n]`**: `T`-points of `G[n]` are the `T`-points of `G` killed by
`n`. -/
noncomputable def torsionKerHomEquiv (G : C) [MonObj G] (n : ℕ) (T : C) :
    (T ⟶ torsionKer G n) ≃ {f : T ⟶ G // f ^ n = 1} where
  toFun g := ⟨g ≫ torsionKerι G n, torsionKerι_pow n g⟩
  invFun f := pullback.lift f.1 (toUnit T) (by
    rw [comp_powHom, f.2, CategoryTheory.Hom.one_def])
  left_inv g := by
    apply pullback.hom_ext
    · simp [torsionKerι]
    · exact toUnit_unique _ _
  right_inv f := by
    apply Subtype.ext
    simp [torsionKerι]

@[simp]
lemma torsionKerHomEquiv_apply (G : C) [MonObj G] (n : ℕ) (T : C) (g : T ⟶ torsionKer G n) :
    (torsionKerHomEquiv G n T g).1 = g ≫ torsionKerι G n := rfl

lemma torsionKerHomEquiv_naturality (G : C) [MonObj G] (n : ℕ) {T T' : C} (h : T' ⟶ T)
    (g : T ⟶ torsionKer G n) :
    (torsionKerHomEquiv G n T' (h ≫ g)).1 = h ≫ (torsionKerHomEquiv G n T g).1 := by
  simp

lemma torsionKerι_mono (G : C) [MonObj G] (n : ℕ) : Mono (torsionKerι G n) := by
  unfold torsionKerι
  infer_instance

omit [HasPullbacks C] in
/-- For a commutative group object, the `n`-torsion of `Hom(T, G)` as a subgroup. -/
noncomputable def torsionPts [BraidedCategory C] (G : C) [GrpObj G] [IsCommMonObj G] (T : C)
    (n : ℕ) : Subgroup (T ⟶ G) :=
  (powMonoidHom n : (T ⟶ G) →* (T ⟶ G)).ker

omit [HasPullbacks C] in
lemma mem_torsionPts [BraidedCategory C] {G : C} [GrpObj G] [IsCommMonObj G] {T : C} {n : ℕ}
    (f : T ⟶ G) : f ∈ torsionPts G T n ↔ f ^ n = 1 := by
  simp [torsionPts, MonoidHom.mem_ker]

end Generic

section Scheme

open AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (G : Over S) [GrpObj G] (n : ℕ)

lemma tensorUnit_over_hom : (𝟙_ (Over S)).hom = 𝟙 S := rfl

lemma eta_comp_hom : η[G].left ≫ G.hom = 𝟙 S := by
  rw [Over.w η[G]]; rfl

/-- The unit section of a separated group scheme is a closed immersion: it is the graph
`S → S ×_S G` of `η` followed by the base change `S ×_S G → G` of the identity. -/
lemma isClosedImmersion_eta [IsSeparated G.hom] : IsClosedImmersion η[G].left := by
  let g : G.left ⟶ S := G.hom
  let e : S ⟶ G.left := η[G].left
  have hc : e ≫ g = 𝟙 S := eta_comp_hom G
  have hsep : IsSeparated g := ‹_›
  have hid : IsClosedImmersion (e ≫ g) := by
    rw [hc]; exact inferInstanceAs (IsClosedImmersion (𝟙 S))
  have h2 : IsClosedImmersion (pullback.snd (e ≫ g) g) :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) (IsPullback.of_hasPullback (e ≫ g) g)
      hid
  have hgr : IsClosedImmersion (pullback.lift (𝟙 S) e (Category.id_comp (e ≫ g))) :=
    inferInstance
  have key : pullback.lift (𝟙 S) e (Category.id_comp (e ≫ g)) ≫ pullback.snd (e ≫ g) g = e :=
    pullback.lift_snd _ _ _
  show IsClosedImmersion e
  rw [← key]
  infer_instance

lemma torsionKer_isPullback_left :
    IsPullback (torsionKerι G n).left (pullback.snd (powHom G n) η[G]).left (powHom G n).left
      η[G].left :=
  (torsionKer_isPullback G n).map (Over.forget S)

/-- `G[n] → G` is a closed immersion for separated `G`. -/
lemma isClosedImmersion_torsionKerι [IsSeparated G.hom] :
    IsClosedImmersion (torsionKerι G n).left := by
  have := isClosedImmersion_eta G
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (torsionKer_isPullback_left G n).flip this

/-- If `[n]` is étale, then `G[n] → S` is étale (base change of `[n]` along the unit section). -/
lemma etale_torsionKer_hom (hn : Etale (powHom G n).left) : Etale (torsionKer G n).hom := by
  have h1 : Etale (pullback.snd (powHom G n) η[G]).left :=
    MorphismProperty.of_isPullback (P := @Etale) (torsionKer_isPullback_left G n) hn
  have h3 : Etale (𝟙_ (Over S)).hom := by
    change Etale (𝟙 S : S ⟶ S)
    infer_instance
  rw [← Over.w (pullback.snd (powHom G n) η[G])]
  infer_instance

end Scheme

end HenselDivision

#check @HenselDivision.torsionKerHomEquiv
#check @HenselDivision.isClosedImmersion_torsionKerι
#check @HenselDivision.etale_torsionKer_hom
#print axioms HenselDivision.torsionKerHomEquiv
#print axioms HenselDivision.torsionKerHomEquiv_naturality
#print axioms HenselDivision.isClosedImmersion_torsionKerι
#print axioms HenselDivision.etale_torsionKer_hom
#print axioms HenselDivision.mem_torsionPts

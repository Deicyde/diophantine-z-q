/-
# H5 / NOS round 2, lane 3 (`Spreadout/`): a proper smooth group model at a finite étale stage

New glue (no vendored source in this file).

`exists_spread_stage`: let `pres` be a filtered colimit presentation of an `R`-algebra `S` (for
the ordinary henselization: H4's ind-étale presentation of `Rh` over `O`), `K` an `R`-algebra (the
fraction field), `N` a smooth proper group object over `Spec S` and `A` a finitely presented group
object over `Spec K`, with a group-object isomorphism `φ` between the generic fibres of `N` and of
`A` over `Spec S ×_{Spec R} Spec K`.  Given the exact properness input `ProperDescendsFor` for the
system (EGA IV₃ 8.10.5 (xii) / Stacks 081F, owned by H65), there is a stage `j` and a smooth
proper group object `G` over `Spec Bⱼ` with
* a group-object isomorphism `(Spec S → Spec Bⱼ)^* G ≅ N` (the cartesian identification upstairs),
* a group-object isomorphism `(Spec Bⱼ ×_R K → Spec Bⱼ)^* G ≅ (Spec Bⱼ ×_R K → Spec K)^* A`
  on the WHOLE generic fibre of the stage (the original `A` itself, base changed),
* and, for every `R`-algebra augmentation `S →ₐ[R] k`, the corresponding `k`-point of `Spec Bⱼ`.
The stage group law, smoothness, properness and both isomorphisms are spread by the published
EGA IV 8.8.2 / 17.7.8 machinery; only properness uses the explicit input.  No model at a stage,
descent datum or effective descent is assumed.
-/
import ZInQKernel.Contrib.CloudR2NOS.Spreadout.GenericSystem

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory
  MonObj
open scoped CategoryTheory.Obj

namespace ZInQ.Contrib.CloudR2NOS.Spreadout

universe u

open ZInQ.Contrib.SpreadOut (stθ pbNat)


/-! ### The assembly over an abstract pair of systems -/

section Abstract

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {D D' : I ⥤ Scheme.{u}}
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
  [∀ i, QuasiSeparatedSpace (D.obj i)] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D'.map f)]
  [∀ i, CompactSpace (D'.obj i)] [∀ i, QuasiSeparatedSpace (D'.obj i)] {c : Cone D} {c' : Cone D'}

/-- The underlying isomorphism of an isomorphism of group objects. -/
def grpIsoX {C : Type*} [Category C] [CartesianMonoidalCategory C] {G H : Grp C} (φ : G ≅ H) :
    G.X ≅ H.X where
  hom := φ.hom.hom.hom
  inv := φ.inv.hom.hom
  hom_inv_id := by rw [← Grp.comp_hom_hom, φ.hom_inv_id, Grp.id_hom_hom]
  inv_hom_id := by rw [← Grp.comp_hom_hom, φ.inv_hom_id, Grp.id_hom_hom]

/-- Base change commutes with a natural family `p : D' ⟶ D`. -/
def bcFstA (p : ∀ j, D'.obj j ⟶ D.obj j)
    (hp : ∀ {j j' : I} (b : j' ⟶ j), D'.map b ≫ p j = p j' ≫ D.map b)
    {k k' : I} (b : k' ⟶ k) (X : Over (D.obj k)) :
    (Over.pullback (D'.map b)).obj ((Over.pullback (p k)).obj X) ≅
      (Over.pullback (p k')).obj ((Over.pullback (D.map b)).obj X) :=
  (pbNat (D'.map b) (p k) (p k' ≫ D.map b) (hp b)).app X ≪≫
    ((pbNat (p k') (D.map b) (p k' ≫ D.map b) rfl).app X).symm

theorem isMonHom_bcFstA (p : ∀ j, D'.obj j ⟶ D.obj j)
    (hp : ∀ {j j' : I} (b : j' ⟶ j), D'.map b ≫ p j = p j' ≫ D.map b)
    {k k' : I} (b : k' ⟶ k) (X : Over (D.obj k)) [MonObj X] :
    IsMonHom (M := (Over.pullback (D'.map b)).obj ((Over.pullback (p k)).obj X))
      (N := (Over.pullback (p k')).obj ((Over.pullback (D.map b)).obj X)) (bcFstA p hp b X).hom :=
  isMonHom_comp' (isMonHom_app_comp (pbNat (D'.map b) (p k) (p k' ≫ D.map b) (hp b)).hom X)
    (isMonHom_app_to_comp (pbNat (p k') (D.map b) (p k' ≫ D.map b) rfl).inv X)

/-- Base change commutes with a cone `q : D' ⟶ T`. -/
def bcSndA {T : Scheme.{u}} (q : ∀ j, D'.obj j ⟶ T) (hq : ∀ {j j' : I} (b : j' ⟶ j), D'.map b ≫ q j = q j')
    {k k' : I} (b : k' ⟶ k) (Y : Over T) :
    (Over.pullback (D'.map b)).obj ((Over.pullback (q k)).obj Y) ≅ (Over.pullback (q k')).obj Y :=
  (pbNat (D'.map b) (q k) (q k') (hq b)).app Y

theorem isMonHom_bcSndA {T : Scheme.{u}} (q : ∀ j, D'.obj j ⟶ T)
    (hq : ∀ {j j' : I} (b : j' ⟶ j), D'.map b ≫ q j = q j') {k k' : I} (b : k' ⟶ k) (Y : Over T)
    [MonObj Y] :
    IsMonHom (M := (Over.pullback (D'.map b)).obj ((Over.pullback (q k)).obj Y))
      (N := (Over.pullback (q k')).obj Y) (bcSndA q hq b Y).hom :=
  isMonHom_app_comp (pbNat (D'.map b) (q k) (q k') (hq b)).hom Y

/-- **Spreading a smooth proper group model with a generic group isomorphism, abstract form.**
`D'` is a second system (the generic one) with a natural map `p : D' ⟶ D` and a cone `q : D' ⟶ T`,
compatible with limit maps `pLim`, `qLim`. -/
theorem exists_spread_stage_abstract (hc : IsLimit c) (hc' : IsLimit c')
    (hpr : ProperDescendsFor D c)
    (p : ∀ j, D'.obj j ⟶ D.obj j) (hp : ∀ {j j' : I} (b : j' ⟶ j), D'.map b ≫ p j = p j' ≫ D.map b)
    (pLim : c'.pt ⟶ c.pt) (hpLim : ∀ j, c'.π.app j ≫ p j = pLim ≫ c.π.app j)
    {T : Scheme.{u}} (q : ∀ j, D'.obj j ⟶ T) (hq : ∀ {j j' : I} (b : j' ⟶ j), D'.map b ≫ q j = q j')
    (qLim : c'.pt ⟶ T) (hqLim : ∀ j, c'.π.app j ≫ q j = qLim)
    (N : Grp (Over c.pt)) [Smooth N.X.hom] [IsProper N.X.hom]
    (A : Grp (Over T)) [LocallyOfFinitePresentation A.X.hom] [QuasiCompact A.X.hom]
    [QuasiSeparated A.X.hom]
    (φ : (Over.pullback pLim).mapGrp.obj N ≅ (Over.pullback qLim).mapGrp.obj A) :
    ∃ (j : I) (G : Grp (Over (D.obj j))), Smooth G.X.hom ∧ IsProper G.X.hom ∧
      Nonempty ((Over.pullback (c.π.app j)).mapGrp.obj G ≅ N) ∧
      Nonempty ((Over.pullback (p j)).mapGrp.obj G ≅ (Over.pullback (q j)).mapGrp.obj A) := by
  -- 1. a smooth proper group stage for `N`
  obtain ⟨t, hG, hsm, hpro, hmon⟩ := exists_grpObj_proper_smooth_stage hc hpr N.X
  -- 2. the generic objects at the stage and their identifications over the generic limit
  let MG := (Over.pullback (p t.k)).obj t.M
  let MA := (Over.pullback (q t.k)).obj A.X
  let eG : (Over.pullback (c'.π.app t.k)).obj MG ≅ (Over.pullback pLim).obj N.X :=
    (pbNat (c'.π.app t.k) (p t.k) (pLim ≫ c.π.app t.k) (hpLim t.k)).app t.M ≪≫
      ((pbNat pLim (c.π.app t.k) (pLim ≫ c.π.app t.k) rfl).app t.M).symm ≪≫
      (Over.pullback pLim).mapIso t.e
  let eA : (Over.pullback (c'.π.app t.k)).obj MA ≅ (Over.pullback qLim).obj A.X :=
    (pbNat (c'.π.app t.k) (q t.k) qLim (hqLim t.k)).app A.X
  let f : (Over.pullback pLim).obj N.X ≅ (Over.pullback qLim).obj A.X := grpIsoX φ
  have heG : IsMonHom (M := (Over.pullback (c'.π.app t.k)).obj MG) eG.hom :=
    isMonHom_comp' (isMonHom_app_comp (pbNat (c'.π.app t.k) (p t.k) (pLim ≫ c.π.app t.k)
        (hpLim t.k)).hom t.M)
      (isMonHom_comp' (isMonHom_app_to_comp (pbNat pLim (c.π.app t.k) (pLim ≫ c.π.app t.k)
          rfl).inv t.M)
        (isMonHom_map' (Over.pullback pLim) hmon))
  have heA : IsMonHom (M := (Over.pullback (c'.π.app t.k)).obj MA) eA.hom :=
    isMonHom_app_comp (pbNat (c'.π.app t.k) (q t.k) qLim (hqLim t.k)).hom A.X
  have hf : IsMonHom f.hom := inferInstanceAs (IsMonHom φ.hom.hom.hom)
  -- 3. spread the generic isomorphism to the generic system
  obtain ⟨k₁, b₁, k₂, b₂, k₃, b₃, ψ₀, hψ₀⟩ := exists_iso_compatMap hc' MG MA eG eA f
  let MG₁ := (Over.pullback (D'.map b₁)).obj MG
  let MG₂ := (Over.pullback (D'.map b₂)).obj MG₁
  let MG₃ := (Over.pullback (D'.map b₃)).obj MG₂
  let MA₁ := (Over.pullback (D'.map b₁)).obj MA
  let MA₂ := (Over.pullback (D'.map b₂)).obj MA₁
  let MA₃ := (Over.pullback (D'.map b₃)).obj MA₂
  have he₁ := isMonHom_next (D := D') (c := c') (M := MG) b₁ heG
  have he₂ := isMonHom_next (D := D') (c := c') (M := MG₁) b₂ he₁
  have he₃ := isMonHom_next (D := D') (c := c') (M := MG₂) b₃ he₂
  have he₁' := isMonHom_next (D := D') (c := c') (M := MA) b₁ heA
  have he₂' := isMonHom_next (D := D') (c := c') (M := MA₁) b₂ he₁'
  have he₃' := isMonHom_next (D := D') (c := c') (M := MA₂) b₃ he₂'
  -- 4. the spread isomorphism is a morphism of group objects one stage further
  obtain ⟨k₄, b₄, hmon₄⟩ := exists_isMonHom_next (D := D') (c := c') (M := MG₃) (M' := MA₃)
    hc' he₃ he₃' hf hψ₀
  -- 5. the final stage model and its identifications
  let X₁ := (Over.pullback (D.map b₁)).obj t.M
  let X₂ := (Over.pullback (D.map b₂)).obj X₁
  let X₃ := (Over.pullback (D.map b₃)).obj X₂
  let X₄ := (Over.pullback (D.map b₄)).obj X₃
  let eUp : (Over.pullback (c.π.app k₄)).obj X₄ ≅ N.X :=
    stθIso D c b₄ X₃ ≪≫ stθIso D c b₃ X₂ ≪≫ stθIso D c b₂ X₁ ≪≫ stθIso D c b₁ t.M ≪≫ t.e
  have hu₁ := isMonHom_next (D := D) (c := c) (M := t.M) b₁ hmon
  have hu₂ := isMonHom_next (D := D) (c := c) (M := X₁) b₂ hu₁
  have hu₃ := isMonHom_next (D := D) (c := c) (M := X₂) b₃ hu₂
  have heUp := isMonHom_next (D := D) (c := c) (M := X₃) b₄ hu₃
  let ΦG₁ := bcFstA p hp b₁ t.M
  let ΦG₂ := (Over.pullback (D'.map b₂)).mapIso ΦG₁ ≪≫ bcFstA p hp b₂ X₁
  let ΦG₃ := (Over.pullback (D'.map b₃)).mapIso ΦG₂ ≪≫ bcFstA p hp b₃ X₂
  let ΦG₄ := (Over.pullback (D'.map b₄)).mapIso ΦG₃ ≪≫ bcFstA p hp b₄ X₃
  let ΦA₁ := bcSndA q hq b₁ A.X
  let ΦA₂ := (Over.pullback (D'.map b₂)).mapIso ΦA₁ ≪≫ bcSndA q hq b₂ A.X
  let ΦA₃ := (Over.pullback (D'.map b₃)).mapIso ΦA₂ ≪≫ bcSndA q hq b₃ A.X
  let ΦA₄ := (Over.pullback (D'.map b₄)).mapIso ΦA₃ ≪≫ bcSndA q hq b₄ A.X
  have hΦG₁ := isMonHom_bcFstA p hp b₁ t.M
  have hΦG₂ := isMonHom_comp' (isMonHom_map' (Over.pullback (D'.map b₂)) hΦG₁)
    (isMonHom_bcFstA p hp b₂ X₁)
  have hΦG₃ := isMonHom_comp' (isMonHom_map' (Over.pullback (D'.map b₃)) hΦG₂)
    (isMonHom_bcFstA p hp b₃ X₂)
  have hΦG₄ := isMonHom_comp' (isMonHom_map' (Over.pullback (D'.map b₄)) hΦG₃)
    (isMonHom_bcFstA p hp b₄ X₃)
  have hΦA₁ := isMonHom_bcSndA q hq b₁ A.X
  have hΦA₂ := isMonHom_comp' (isMonHom_map' (Over.pullback (D'.map b₂)) hΦA₁)
    (isMonHom_bcSndA q hq b₂ A.X)
  have hΦA₃ := isMonHom_comp' (isMonHom_map' (Over.pullback (D'.map b₃)) hΦA₂)
    (isMonHom_bcSndA q hq b₃ A.X)
  have hΦA₄ := isMonHom_comp' (isMonHom_map' (Over.pullback (D'.map b₄)) hΦA₃)
    (isMonHom_bcSndA q hq b₄ A.X)
  have h1 := isMonHom_inv' ΦG₄ hΦG₄
  have h2 := isMonHom_comp' hmon₄ hΦA₄
  have hψ := isMonHom_comp' h1 h2
  let ψ : (Over.pullback (p k₄)).obj X₄ ≅ (Over.pullback (q k₄)).obj A.X :=
    ΦG₄.symm ≪≫ (Over.pullback (D'.map b₄)).mapIso ψ₀ ≪≫ ΦA₄
  -- 6. conclusion
  refine ⟨k₄, Grp.mk X₄, ?_, ?_, ⟨@Grp.mkIso' _ _ _ _ _ eUp _ _ heUp⟩,
    ⟨@Grp.mkIso' _ _ _ _ _ ψ _ _ hψ⟩⟩
  · exact prop_pb (@Smooth) (D.map b₄) X₃ (prop_pb (@Smooth) (D.map b₃) X₂
      (prop_pb (@Smooth) (D.map b₂) X₁ (prop_pb (@Smooth) (D.map b₁) t.M hsm)))
  · exact prop_pb (@IsProper) (D.map b₄) X₃ (prop_pb (@IsProper) (D.map b₃) X₂
      (prop_pb (@IsProper) (D.map b₂) X₁ (prop_pb (@IsProper) (D.map b₁) t.M hpro)))

end Abstract

/-! ### The ind-presented base -/

section Presentation

variable {R : Type u} [CommRing R] {S : CommAlgCat.{u} R} {J : Type u} [SmallCategory J]
  (pres : ColimitPresentation J S) (K : Type u) [CommRing K] [Algebra R K]

/-- **Spreading a proper smooth group model, with its generic group isomorphism, to a finite
stage of an ind-presented base.** -/
theorem exists_spread_stage [IsFiltered J]
    (hpr : ProperDescendsFor (specDiagram pres) (specCone pres))
    (N : Grp (Over (specCone pres).pt)) [Smooth N.X.hom] [IsProper N.X.hom]
    (A : Grp (Over (Spec (CommRingCat.of K)))) [LocallyOfFinitePresentation A.X.hom]
    [QuasiCompact A.X.hom] [QuasiSeparated A.X.hom]
    (φ : (Over.pullback (genFstLim pres K)).mapGrp.obj N ≅
      (Over.pullback (genSndLim pres K)).mapGrp.obj A) :
    ∃ (j : Jᵒᵖ) (G : Grp (Over ((specDiagram pres).obj j))),
      Smooth G.X.hom ∧ IsProper G.X.hom ∧
      Nonempty ((Over.pullback ((specCone pres).π.app j)).mapGrp.obj G ≅ N) ∧
      Nonempty ((Over.pullback (genFst pres K j)).mapGrp.obj G ≅
        (Over.pullback (genSnd pres K j)).mapGrp.obj A) :=
  exists_spread_stage_abstract (isLimit_specCone pres) (isLimit_genCone pres K) hpr
    (genFst pres K) (fun b => genDiagram_map_fst pres K b) (genFstLim pres K)
    (genCone_π_fst pres K) (genSnd pres K) (fun b => genDiagram_map_snd pres K b)
    (genSndLim pres K) (genCone_π_snd pres K) N A φ

/-- **The fibre of a stage model at an augmentation point is the fibre of the limit model.**  For a
stage object `G` over `Spec Bⱼ` with `(Spec S → Spec Bⱼ)^* G ≅ N` and an augmentation
`ψ : S →ₐ[R] k`, the fibre of `G` over the stage point `stagePoint pres ψ j` is the fibre of `N`
over `Spec ψ`. (For the ordinary henselization and `k = κ(O)` this identifies the special fibre of
the stage model at its rational point with the special fibre of the upstairs model.) -/
def stagePointFibreIso (j : J) (G : Over ((specDiagram pres).obj (op j)))
    (N : Over (specCone pres).pt) (e : (Over.pullback ((specCone pres).π.app (op j))).obj G ≅ N)
    {k : Type u} [CommRing k] [Algebra R k] (ψ : S →ₐ[R] k) :
    (Over.pullback (stagePoint pres ψ j)).obj G ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom ψ.toRingHom))).obj N :=
  ((pbNat (Spec.map (CommRingCat.ofHom ψ.toRingHom)) ((specCone pres).π.app (op j))
      (stagePoint pres ψ j) (stagePoint_eq pres ψ j).symm).app G).symm ≪≫
    (Over.pullback (Spec.map (CommRingCat.ofHom ψ.toRingHom))).mapIso e

end Presentation

end ZInQ.Contrib.CloudR2NOS.Spreadout

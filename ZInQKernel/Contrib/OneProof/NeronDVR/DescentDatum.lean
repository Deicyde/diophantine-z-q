import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.CategoryTheory.Comma.Over.DescentDatum

/-!
# Descent data for Néron models

For a smooth cover, the mapping property extends the generic descent isomorphism over
the overlap. Its unit and cocycle laws follow from uniqueness over the smooth double
and triple overlaps (Bosch–Lütkebohmert–Raynaud, *Néron Models*, §6.5, proof of
Corollary 3).
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace NeronDVR

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {S S' T : Scheme.{0}} (j : T ⟶ S) (p : S' ⟶ S) (N : Over S')

section Transport

private theorem over_comp {Y Z : Over S'} (f : Y ⟶ Z) :
    f.left ≫ (Z.hom ≫ p) = Y.hom ≫ p := by
  rw [← Category.assoc, Over.w f]

private def restrictHom {Y Z : Scheme.{0}} {y : Y ⟶ S} {z : Z ⟶ S}
    (f : Y ⟶ Z) (h : f ≫ z = y) : pullback y j ⟶ pullback z j :=
  pullback.lift (pullback.fst y j ≫ f) (pullback.snd y j)
    (by rw [Category.assoc, h, pullback.condition])

private theorem restrictHom_comp {Y Z W : Scheme.{0}} {y : Y ⟶ S} {z : Z ⟶ S} {w : W ⟶ S}
    (f : Y ⟶ Z) (g : Z ⟶ W) (hf : f ≫ z = y) (hg : g ≫ w = z) :
    restrictHom j (f ≫ g) (by rw [Category.assoc, hg, hf]) =
      restrictHom j f hf ≫ restrictHom j g hg := by
  apply pullback.hom_ext <;> simp [restrictHom, Category.assoc]

private theorem restrictHom_congr {Y Z : Scheme.{0}} {y : Y ⟶ S} {z : Z ⟶ S}
    (f g : Y ⟶ Z) (hf : f ≫ z = y) (hg : g ≫ z = y) (h : f = g) :
    restrictHom j f hf = restrictHom j g hg := by
  subst g
  rfl

private abbrev overlap : Scheme.{0} := pullback (N.hom ≫ p) p

private abbrev second : Over S' := Over.mk (pullback.snd (N.hom ≫ p) p)

private def firstMap : (Over.map p).obj (second p N) ⟶ (Over.map p).obj N :=
  Over.homMk (pullback.fst (N.hom ≫ p) p) pullback.condition

variable {A : Over T} (r : (Over.map p ⋙ Over.pullback j).obj N ⟶ A)
  (extend : ∀ (Y : Over S') [Smooth Y.hom],
    Function.Bijective (fun f : Y ⟶ N => (Over.map p ⋙ Over.pullback j).map f ≫ r))
  [Smooth N.hom] [Smooth p]

private instance : Smooth (second p N).hom :=
  show Smooth (pullback.snd (N.hom ≫ p) p) from inferInstance

private def action : second p N ⟶ N :=
  (extend (second p N)).surjective ((Over.pullback j).map (firstMap p N) ≫ r) |>.choose

private theorem action_restrict :
    restrictHom j (action j p N r extend).left
        (over_comp p _) ≫ r.left =
      restrictHom j (pullback.fst (N.hom ≫ p) p) pullback.condition ≫ r.left := by
  exact congrArg CommaMorphism.left
    ((extend (second p N)).surjective ((Over.pullback j).map (firstMap p N) ≫ r)).choose_spec

private def move {Y : Scheme.{0}} (a b : Y ⟶ S') (hab : a ≫ p = b ≫ p)
    (x : Over.mk a ⟶ N) : Over.mk b ⟶ N :=
  Over.homMk
    (pullback.lift x.left b ((over_comp p x).trans hab) ≫
      (action j p N r extend).left)
    (by
      rw [Category.assoc, Over.w (action j p N r extend)]
      exact pullback.lift_snd _ _ _)

private theorem move_comp {Y Z : Scheme.{0}} (k : Z ⟶ Y)
    (a b : Y ⟶ S') (hab : a ≫ p = b ≫ p) (x : Over.mk a ⟶ N) :
    move j p N r extend (k ≫ a) (k ≫ b) (by simp [Category.assoc, hab])
        ((Over.homMk k : Over.mk (k ≫ a) ⟶ Over.mk a) ≫ x) =
      (Over.homMk k : Over.mk (k ≫ b) ⟶ Over.mk b) ≫ move j p N r extend a b hab x := by
  ext1
  change pullback.lift (k ≫ x.left) (k ≫ b) _ ≫ (action j p N r extend).left =
    k ≫ pullback.lift x.left b _ ≫ (action j p N r extend).left
  refine (congrArg (fun f => f ≫ (action j p N r extend).left) ?_).trans
    (Category.assoc _ _ _)
  apply pullback.hom_ext <;> simp

private theorem move_restrict {Y : Scheme.{0}} (a b : Y ⟶ S')
    (hab : a ≫ p = b ≫ p) (x : Over.mk a ⟶ N) :
    restrictHom j (move j p N r extend a b hab x).left
        (over_comp p _) ≫ r.left =
      restrictHom j x.left ((over_comp p x).trans hab) ≫ r.left := by
  let l : Y ⟶ overlap p N :=
    pullback.lift x.left b ((over_comp p x).trans hab)
  have hl : l ≫ pullback.snd (N.hom ≫ p) p ≫ p = b ≫ p :=
    pullback.lift_snd_assoc _ _ _ _
  have ha : (action j p N r extend).left ≫ (N.hom ≫ p) =
      pullback.snd (N.hom ≫ p) p ≫ p := over_comp p _
  have hf : pullback.fst (N.hom ≫ p) p ≫ (N.hom ≫ p) =
      pullback.snd (N.hom ≫ p) p ≫ p := pullback.condition
  change restrictHom j (l ≫ (action j p N r extend).left) _ ≫ r.left = _
  rw [restrictHom_comp j l (action j p N r extend).left hl ha, Category.assoc,
    action_restrict, ← Category.assoc, ← restrictHom_comp j _ _ hl hf]
  exact congrArg (fun f => f ≫ r.left)
    (restrictHom_congr j _ _ _ _ (pullback.lift_fst _ _ _))

private theorem move_restrict_at {Y : Scheme.{0}} (a b : Y ⟶ S')
    (hab : a ≫ p = b ≫ p) (x : Over.mk a ⟶ N) (base : Y ⟶ S) (hb : b ≫ p = base) :
    restrictHom j (move j p N r extend a b hab x).left
        ((over_comp p _).trans hb) ≫ r.left =
      restrictHom j x.left ((over_comp p x).trans (hab.trans hb)) ≫ r.left := by
  subst base
  exact move_restrict j p N r extend a b hab x

omit [Smooth N.hom] [Smooth p] in
include extend in
private theorem extension_injective {Y : Over S'} [Smooth Y.hom] {f g : Y ⟶ N}
    (h : restrictHom j f.left (over_comp p f) ≫ r.left =
      restrictHom j g.left (over_comp p g) ≫ r.left) : f = g := by
  apply (extend Y).injective
  ext1
  exact h

private theorem move_unit :
    move j p N r extend N.hom N.hom rfl (Over.homMk (𝟙 N.left) (Category.id_comp _)) =
      Over.homMk (𝟙 N.left) (Category.id_comp _) := by
  let : Smooth (Over.mk N.hom).hom := ‹Smooth N.hom›
  apply extension_injective j p N r extend
  exact move_restrict j p N r extend _ _ rfl _

private theorem move_left_congr {Y : Scheme.{0}} {a b a' b' : Y ⟶ S'}
    (hab : a ≫ p = b ≫ p) (hab' : a' ≫ p = b' ≫ p)
    (x : Over.mk a ⟶ N) (x' : Over.mk a' ⟶ N)
    (ha : a = a') (hb : b = b') (hx : x.left = x'.left) :
    (move j p N r extend a b hab x).left = (move j p N r extend a' b' hab' x').left := by
  subst ha hb
  obtain rfl : x = x' := Over.OverMorphism.ext hx
  rfl

private theorem move_self {Y : Scheme.{0}} (a : Y ⟶ S') (x : Over.mk a ⟶ N) :
    move j p N r extend a a rfl x = x := by
  let idN : Over.mk N.hom ⟶ N := Over.homMk (𝟙 N.left) (Category.id_comp _)
  let x₀ : Over.mk (x.left ≫ N.hom) ⟶ Over.mk N.hom := Over.homMk x.left
  have h := move_comp j p N r extend x.left N.hom N.hom rfl
    idN
  change move j p N r extend _ _ _ (x₀ ≫ idN) =
    x₀ ≫ move j p N r extend _ _ _ idN at h
  have hu : move j p N r extend N.hom N.hom rfl idN = idN :=
    move_unit j p N r extend
  rw [hu] at h
  have hx : (x₀ ≫ idN).left = x.left := Category.comp_id _
  ext1
  exact (move_left_congr j p N r extend _ rfl (x₀ ≫ idN) x (Over.w x) (Over.w x) hx).symm.trans
    ((congrArg CommaMorphism.left h).trans hx)

private abbrev thirdScheme : Scheme.{0} :=
  pullback (pullback.snd (N.hom ≫ p) p ≫ p) p

private abbrev third : Over S' := Over.mk
  (pullback.snd (pullback.snd (N.hom ≫ p) p ≫ p) p)

private instance : Smooth (third p N).hom :=
  show Smooth (pullback.snd (pullback.snd (N.hom ≫ p) p ≫ p) p) from inferInstance

private abbrev firstThird : thirdScheme p N ⟶ N.left :=
  pullback.fst (pullback.snd (N.hom ≫ p) p ≫ p) p ≫ pullback.fst (N.hom ≫ p) p

private abbrev secondThird : thirdScheme p N ⟶ S' :=
  pullback.fst (pullback.snd (N.hom ≫ p) p ≫ p) p ≫ pullback.snd (N.hom ≫ p) p

omit [Smooth N.hom] [Smooth p] in
private theorem firstThird_eq : (firstThird p N ≫ N.hom) ≫ p = secondThird p N ≫ p := by
  simp only [firstThird, secondThird, Category.assoc, pullback.condition]

omit [Smooth N.hom] [Smooth p] in
private theorem secondThird_eq : secondThird p N ≫ p = (third p N).hom ≫ p := by
  rw [secondThird, Category.assoc]
  exact pullback.condition

private theorem move_triple :
    move j p N r extend (secondThird p N) (third p N).hom (secondThird_eq p N)
      (move j p N r extend (firstThird p N ≫ N.hom) (secondThird p N) (firstThird_eq p N)
        (Over.homMk (firstThird p N) rfl)) =
    move j p N r extend (firstThird p N ≫ N.hom) (third p N).hom
      ((firstThird_eq p N).trans (secondThird_eq p N)) (Over.homMk (firstThird p N) rfl) := by
  let : Smooth (Over.mk (third p N).hom).hom :=
    show Smooth (pullback.snd (pullback.snd (N.hom ≫ p) p ≫ p) p) from inferInstance
  apply extension_injective j p N r extend
  rw [move_restrict j p N r extend (secondThird p N) (third p N).hom,
    move_restrict j p N r extend (firstThird p N ≫ N.hom) (third p N).hom]
  exact move_restrict_at j p N r extend (firstThird p N ≫ N.hom) (secondThird p N)
    (firstThird_eq p N) (Over.homMk (firstThird p N) rfl) _ (secondThird_eq p N)

private theorem move_cocycle {Y : Scheme.{0}} (a b c : Y ⟶ S')
    (hab : a ≫ p = b ≫ p) (hbc : b ≫ p = c ≫ p) (x : Over.mk a ⟶ N) :
    move j p N r extend b c hbc (move j p N r extend a b hab x) =
      move j p N r extend a c (hab.trans hbc) x := by
  let l₂ : Y ⟶ overlap p N := pullback.lift x.left b
    ((over_comp p x).trans hab)
  let l₃ : Y ⟶ thirdScheme p N := pullback.lift l₂ c
    (by simp [l₂, hbc])
  have hl₁ : l₃ ≫ (firstThird p N ≫ N.hom) = a := by
    simp [l₃, l₂, firstThird, Category.assoc]
  have hl₂ : l₃ ≫ secondThird p N = b := by simp [l₃, l₂, secondThird]
  have hl₃ : l₃ ≫ (third p N).hom = c := by simp [l₃]
  have hlx : l₃ ≫ firstThird p N = x.left := by simp [l₃, l₂, firstThird]
  have pullMove {u v : thirdScheme p N ⟶ S'} {u' v' : Y ⟶ S'}
      (huv : u ≫ p = v ≫ p) (huv' : u' ≫ p = v' ≫ p)
      (P : Over.mk u ⟶ N) (P' : Over.mk u' ⟶ N)
      (hu : l₃ ≫ u = u') (hv : l₃ ≫ v = v') (hP : l₃ ≫ P.left = P'.left) :
      l₃ ≫ (move j p N r extend u v huv P).left =
        (move j p N r extend u' v' huv' P').left :=
    (congrArg CommaMorphism.left (move_comp j p N r extend l₃ u v huv P)).symm.trans
      (move_left_congr j p N r extend _ huv' _ P' hu hv hP)
  let x₀ : Over.mk (firstThird p N ≫ N.hom) ⟶ N := Over.homMk (firstThird p N) rfl
  have h₁₂ := pullMove (firstThird_eq p N) hab x₀ x hl₁ hl₂ hlx
  have h₂₃ := pullMove (secondThird_eq p N) hbc _ _ hl₂ hl₃ h₁₂
  have h₁₃ := pullMove ((firstThird_eq p N).trans (secondThird_eq p N))
    (hab.trans hbc) x₀ x hl₁ hl₃ hlx
  ext1
  exact h₂₃.symm.trans ((congrArg (fun f => l₃ ≫ f.left)
    (move_triple j p N r extend)).trans h₁₃)

/-- The unique compatible extensions of the generic-fibre transport give the descent datum. -/
def descentDatum : Over.DescentDatum p N where
  transport := move j p N r extend
  transport_homMk_comp := move_comp j p N r extend
  transport_self := move_self j p N r extend
  transport_transport := move_cocycle j p N r extend

private theorem transportAtGenericPoint {Y : Scheme.{0}} (a b : Y ⟶ S')
    (hab : a ≫ p = b ≫ p) (x : Over.mk a ⟶ N) (u : Y ⟶ T) (hu : b ≫ p = u ≫ j) :
    pullback.lift (f := N.hom ≫ p) (g := j) (move j p N r extend a b hab x).left u
        ((over_comp p _).trans hu) ≫ r.left =
      pullback.lift (f := N.hom ≫ p) (g := j) x.left u
        ((over_comp p x).trans (hab.trans hu)) ≫ r.left := by
  let i : Y ⟶ pullback (b ≫ p) j := pullback.lift (𝟙 Y) u (by simpa using hu)
  have hi {f : Y ⟶ N.left} (hf : f ≫ (N.hom ≫ p) = b ≫ p) :
      i ≫ restrictHom j f hf = pullback.lift f u (hf.trans hu) := by
    apply pullback.hom_ext <;> simp [i, restrictHom]
  simpa only [← Category.assoc, hi] using
    congrArg (fun g => i ≫ g) (move_restrict j p N r extend a b hab x)

end Transport

section Cartesian

variable {T' : Scheme.{0}} (j' : T' ⟶ S') (t : T' ⟶ T)
  (hpb : IsPullback j' t p j)

include hpb in
private theorem pastedGenericSquare (Y : Over S') :
    IsPullback (pullback.fst Y.hom j') (pullback.snd Y.hom j' ≫ t) (Y.hom ≫ p) j :=
  (IsPullback.of_hasPullback Y.hom j').paste_vert hpb

/-- Comparing restriction over the two sides of the Cartesian square on the generic loci. -/
def genericFibreComparison : Over.pullback j' ⋙ Over.map t ≅ Over.map p ⋙ Over.pullback j :=
  NatIso.ofComponents
    (fun Y => Over.isoMk (pastedGenericSquare j p j' t hpb Y).isoPullback
      (pastedGenericSquare j p j' t hpb Y).isoPullback_hom_snd)
    (by
      intro Y Z f
      ext1
      apply pullback.hom_ext
      · simp [Over.pullback_map_left, Over.map_map_left, Category.assoc]
      · simp [Over.pullback_map_left, Over.map_map_left, Category.assoc])

variable {A : Over T} (e : (Over.pullback j').obj N ≅ (Over.pullback t).obj A)

/-- The generic identification, viewed over the lower generic locus. -/
def restrictionToGeneric : (Over.map p ⋙ Over.pullback j).obj N ⟶ A :=
  (genericFibreComparison j p j' t hpb).inv.app N ≫
    ((Over.mapPullbackAdj t).homEquiv ((Over.pullback j').obj N) A).symm e.hom

private theorem restrictionToGeneric_bijective
    (hex : ∀ (Y : Over S') [Smooth Y.hom],
      Function.Bijective (fun f : Y ⟶ N => (Over.pullback j').map f))
    (Y : Over S') [Smooth Y.hom] :
    Function.Bijective (fun f : Y ⟶ N =>
      (Over.map p ⋙ Over.pullback j).map f ≫ restrictionToGeneric j p N j' t hpb e) := by
  let comparison := genericFibreComparison j p j' t hpb
  let E := (e.homToEquiv (Z := (Over.pullback j').obj Y)).trans
    ((Over.mapPullbackAdj t).homEquiv ((Over.pullback j').obj Y) A).symm
  let F := (comparison.app Y).homFromEquiv (Z := A)
  have h := F.bijective.comp (E.bijective.comp (hex Y))
  convert h using 1
  funext f
  change (Over.map p ⋙ Over.pullback j).map f ≫
    comparison.inv.app N ≫ _ = comparison.inv.app Y ≫
    ((Over.mapPullbackAdj t).homEquiv ((Over.pullback j').obj Y) A).symm
      ((Over.pullback j').map f ≫ e.hom)
  rw [(Over.mapPullbackAdj t).homEquiv_naturality_left_symm, ← Category.assoc,
    comparison.inv.naturality]
  exact Category.assoc _ _ _

/-- The descent datum determined by the Néron mapping property and the generic-fibre
identification across a smooth cover. -/
def neronDescentDatum [Smooth N.hom] [Smooth p]
    (hex : ∀ (Y : Over S') [Smooth Y.hom],
      Function.Bijective (fun f : Y ⟶ N => (Over.pullback j').map f)) :
    Over.DescentDatum p N :=
  descentDatum j p N (restrictionToGeneric j p N j' t hpb e)
    (restrictionToGeneric_bijective j p N j' t hpb e hex)

/-- Transport preserves the common generic restriction map on tests over the
generic locus of the base. -/
theorem neronDescentDatum_transportAtGenericPoint [Smooth N.hom] [Smooth p]
    (hex : ∀ (Y : Over S') [Smooth Y.hom],
      Function.Bijective (fun f : Y ⟶ N => (Over.pullback j').map f))
    {Y : Scheme.{0}} (a b : Y ⟶ S') (hab : a ≫ p = b ≫ p) (x : Over.mk a ⟶ N)
    (u : Y ⟶ T) (hu : b ≫ p = u ≫ j) :
    let y := (neronDescentDatum j p N j' t hpb e hex).transport a b hab x
    pullback.lift (f := N.hom ≫ p) (g := j) y.left u
        ((over_comp p y).trans hu) ≫ (restrictionToGeneric j p N j' t hpb e).left =
      pullback.lift (f := N.hom ≫ p) (g := j) x.left u
        ((over_comp p x).trans (hab.trans hu)) ≫ (restrictionToGeneric j p N j' t hpb e).left :=
  transportAtGenericPoint j p N (restrictionToGeneric j p N j' t hpb e)
    (restrictionToGeneric_bijective j p N j' t hpb e hex) a b hab x u hu

private theorem restrictionToGeneric_lift {Y : Scheme.{0}} (x : Y ⟶ N.left)
    (v : Y ⟶ T') (hv : x ≫ N.hom = v ≫ j') (u : Y ⟶ T) (hu : v ≫ t = u)
    (h : x ≫ (N.hom ≫ p) = u ≫ j) :
    pullback.lift (f := N.hom ≫ p) (g := j) x u h ≫
      (restrictionToGeneric j p N j' t hpb e).left =
    pullback.lift x v hv ≫ e.hom.left ≫ pullback.fst A.hom t := by
  let c := (genericFibreComparison j p j' t hpb).app N
  let G := ((Over.mapPullbackAdj t).homEquiv ((Over.pullback j').obj N) A).symm e.hom
  have hG : G.left = e.hom.left ≫ pullback.fst A.hom t := by
    simp [G, Adjunction.homEquiv_counit, Over.mapPullbackAdj_counit_app]
  have hl : pullback.lift x v hv ≫ c.hom.left =
      pullback.lift (f := N.hom ≫ p) (g := j) x u h := by
    apply pullback.hom_ext <;> simp [c, genericFibreComparison, hu, Category.assoc]
  calc
    _ = (pullback.lift x v hv ≫ c.hom.left) ≫ c.inv.left ≫ G.left := by rw [hl]; rfl
    _ = _ := by simp [Category.assoc, hG]

/-- Transport on the generic fibre preserves the map to the prescribed generic
scheme, even when the chosen points of the covering base differ. -/
theorem neronDescentDatum_transport_generic_point [Smooth N.hom] [Smooth p]
    (hex : ∀ (Y : Over S') [Smooth Y.hom],
      Function.Bijective (fun f : Y ⟶ N => (Over.pullback j').map f))
    {Y : Scheme.{0}} (a b : Y ⟶ S') (hab : a ≫ p = b ≫ p) (x : Over.mk a ⟶ N)
    (v₁ v₂ : Y ⟶ T') (hv₁ : a = v₁ ≫ j') (hv₂ : b = v₂ ≫ j')
    (hu : v₁ ≫ t = v₂ ≫ t) :
    let y := (neronDescentDatum j p N j' t hpb e hex).transport a b hab x
    pullback.lift y.left v₂ ((Over.w y).trans hv₂) ≫ e.hom.left ≫ pullback.fst A.hom t =
      pullback.lift x.left v₁ ((Over.w x).trans hv₁) ≫ e.hom.left ≫ pullback.fst A.hom t := by
  let r := restrictionToGeneric j p N j' t hpb e
  let extend := restrictionToGeneric_bijective j p N j' t hpb e hex
  let y := (neronDescentDatum j p N j' t hpb e hex).transport a b hab x
  let u := v₂ ≫ t
  have hb : b ≫ p = u ≫ j := by rw [hv₂, Category.assoc, hpb.w, ← Category.assoc]
  have hg := transportAtGenericPoint j p N r extend a b hab x u hb
  have hl := restrictionToGeneric_lift j p N j' t hpb e y.left v₂
    ((Over.w y).trans hv₂) u rfl ((over_comp p y).trans hb)
  have hr := restrictionToGeneric_lift j p N j' t hpb e x.left v₁
    ((Over.w x).trans hv₁) u hu ((over_comp p x).trans (hab.trans hb))
  exact hl.symm.trans (hg.trans hr)

section Effective

variable [Smooth N.hom] [Smooth p] [Flat t] [Surjective t] [QuasiCompact t]
  (hex : ∀ (Y : Over S') [Smooth Y.hom],
    Function.Bijective (fun f : Y ⟶ N => (Over.pullback j').map f))

/-- Effectivity of the Néron descent datum descends the model together with its
prescribed generic fibre. -/
theorem exists_model_with_generic_fibre
    (heff : (neronDescentDatum j p N j' t hpb e hex).IsEffective) :
    ∃ (X : Over S) (k : N.left ⟶ X.left),
      IsPullback k N.hom X.hom p ∧ Nonempty ((Over.pullback j).obj X ≅ A) := by
  obtain ⟨X, k, hk, hinv⟩ := heff
  let Xη := (Over.pullback j).obj X
  let Nη := (Over.pullback j').obj N
  let c := (genericFibreComparison j p j' t hpb).hom.app N
  let kOver : (Over.map p).obj N ⟶ X := Over.homMk k hk.w
  let q : (Over.map t).obj Nη ⟶ Xη := c ≫ (Over.pullback j).map kOver
  have hq₁ : q.left ≫ pullback.fst X.hom j = pullback.fst N.hom j' ≫ k := by
    simp [q, c, kOver, genericFibreComparison, Over.pullback_map_left, Category.assoc]
  have hq₂ : q.left ≫ Xη.hom = Nη.hom ≫ t := Over.w q
  have hq : IsPullback q.left Nη.hom Xη.hom t := by
    refine IsPullback.of_right ?_ hq₂ (IsPullback.of_hasPullback X.hom j)
    rw [hq₁, ← hpb.w]
    exact (IsPullback.of_hasPullback N.hom j').paste_horiz hk
  have : Flat q.left := MorphismProperty.of_isPullback hq.flip inferInstance
  have : Surjective q.left := MorphismProperty.of_isPullback hq.flip inferInstance
  have : QuasiCompact q.left := MorphismProperty.of_isPullback hq.flip inferInstance
  let r := restrictionToGeneric j p N j' t hpb e
  let r' : (Over.map t).obj Nη ⟶ A := c ≫ r
  have hr' : r'.left = e.hom.left ≫ pullback.fst A.hom t := by
    have hr : r' = ((Over.mapPullbackAdj t).homEquiv Nη A).symm e.hom := by
      simp [r', r, c, restrictionToGeneric, Nη]
    rw [hr, Adjunction.homEquiv_counit]
    simp [Over.mapPullbackAdj_counit_app]
  have hinvariant {Y : Scheme.{0}} (a b : Y ⟶ Nη.left) (hab : a ≫ q.left = b ≫ q.left) :
      a ≫ r'.left = b ≫ r'.left := by
    let a₀ := a ≫ pullback.fst N.hom j'
    let b₀ := b ≫ pullback.fst N.hom j'
    let u := a ≫ Nη.hom ≫ t
    have hu : b ≫ Nη.hom ≫ t = u := by
      simpa only [u, Category.assoc, hq₂] using
        congrArg (fun m => m ≫ Xη.hom) hab.symm
    have hk₀ : a₀ ≫ k = b₀ ≫ k := by
      simpa only [a₀, b₀, Category.assoc, hq₁] using
        congrArg (fun m => m ≫ pullback.fst X.hom j) hab
    let α := a₀ ≫ N.hom
    let β := b₀ ≫ N.hom
    have hα : α ≫ p = u ≫ j := by
      simp only [α, a₀, u, Category.assoc, pullback.condition, hpb.w]
      rfl
    have hβ : β ≫ p = u ≫ j := by
      simp only [β, b₀, Category.assoc, pullback.condition, hpb.w]
      exact congrArg (fun m => m ≫ j) hu |>.trans (Category.assoc _ _ _)
    have hαβ := hα.trans hβ.symm
    let x : Over.mk α ⟶ N := Over.homMk a₀ rfl
    let d := neronDescentDatum j p N j' t hpb e hex
    let y := d.transport α β hαβ x
    have hy : y.left = b₀ :=
      hk.hom_ext ((hinv α β hαβ x).trans hk₀) (Over.w y)
    have aLift : a ≫ c.left = pullback.lift a₀ u
        ((over_comp p x).trans hα) := by
      apply pullback.hom_ext <;> simp [c, a₀, u, Nη, genericFibreComparison, Category.assoc]
    have bLift : b ≫ c.left = pullback.lift y.left u
        ((over_comp p y).trans hβ) := by
      apply pullback.hom_ext <;>
        simp [c, hy, b₀, genericFibreComparison, Category.assoc]
      exact hu
    have hg := transportAtGenericPoint j p N r
      (restrictionToGeneric_bijective j p N j' t hpb e hex) α β hαβ x u hβ
    change a ≫ c.left ≫ r.left = b ≫ c.left ≫ r.left
    rw [← Category.assoc, ← Category.assoc, aLift, bLift]
    exact hg.symm
  let g := EffectiveEpi.desc q.left r'.left hinvariant
  have hg : q.left ≫ g = r'.left := EffectiveEpi.fac q.left r'.left hinvariant
  have hgw : g ≫ A.hom = Xη.hom := by
    rw [← cancel_epi q.left, ← Category.assoc, hg, Over.w r', hq₂]
    rfl
  have hcart : IsPullback e.hom.left q.left (pullback.fst A.hom t) g := by
    refine IsPullback.of_right ?_ (hr'.symm.trans hg.symm) (IsPullback.of_hasPullback A.hom t).flip
    rw [hgw]
    change IsPullback (e.hom.left ≫ (Over.pullback t |>.obj A).hom) q.left t Xη.hom
    rw [Over.w e.hom]
    exact hq.flip
  have hgIso : IsIso g := MorphismProperty.of_isPullback_of_descendsAlong
    (P := MorphismProperty.isomorphisms Scheme.{0}) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    hcart ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ (by
      change IsIso ((Over.forget T').map e.hom)
      infer_instance)
  exact ⟨X, k, hk, ⟨Over.isoMk (asIso g) hgw⟩⟩

end Effective

end Cartesian

end

end NeronDVR

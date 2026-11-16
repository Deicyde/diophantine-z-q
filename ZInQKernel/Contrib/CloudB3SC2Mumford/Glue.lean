import ZInQKernel.Contrib.CloudB3SC2Mumford.Fibres
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

/-!
# Gluing the unique affine Mumford group laws

We glue morphisms over a locally directed affine cover, and compare them as scheme morphisms.
The resulting group structures are on morphisms from arbitrary schemes, including schemes
with nilpotents. Representability then gives the group object on the original family.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace ZInQ.Contrib.CloudB3SC2Mumford
namespace AffineGlue

variable {S : Scheme.{0}} (F : Over S)

/-- Project a point of an affine base change to the original family. -/
def toGlobal {R : Type} [CommRing R] (a : Spec (CommRingCat.of R) ⟶ S)
    {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver t (pullback.snd F.hom a)) : T ⟶ F.left :=
  x.1 ≫ pullback.fst F.hom a

theorem toGlobal_over {R : Type} [CommRing R] (a : Spec (CommRingCat.of R) ⟶ S)
    {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver t (pullback.snd F.hom a)) :
    toGlobal F a x ≫ F.hom = t ≫ a := by
  change (x.1 ≫ pullback.fst F.hom a) ≫ F.hom = t ≫ a
  rw [Category.assoc, pullback.condition, ← Category.assoc, x.2]

/-- Lift a morphism, with its structural equality, into the affine pullback. -/
def fromGlobal {R : Type} [CommRing R] (a : Spec (CommRingCat.of R) ⟶ S)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (x : T ⟶ F.left)
    (hx : x ≫ F.hom = t ≫ a) : SchemeHomOver t (pullback.snd F.hom a) :=
  ⟨pullback.lift x t hx, pullback.lift_snd _ _ _⟩

@[simp] theorem toGlobal_fromGlobal {R : Type} [CommRing R]
    (a : Spec (CommRingCat.of R) ⟶ S) {T : Scheme.{0}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x : T ⟶ F.left)
    (hx : x ≫ F.hom = t ≫ a) : toGlobal F a (fromGlobal F a t x hx) = x :=
  pullback.lift_fst _ _ _

theorem toGlobal_injective {R : Type} [CommRing R] (a : Spec (CommRingCat.of R) ⟶ S)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) :
    Function.Injective (toGlobal F a (t := t)) := by
  intro x y h
  apply Subtype.ext
  apply pullback.hom_ext
  · exact h
  · exact x.2.trans y.2.symm

@[simp] theorem toGlobal_comp {R : Type} [CommRing R] (a : Spec (CommRingCat.of R) ⟶ S)
    {T T' : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (x : SchemeHomOver t (pullback.snd F.hom a)) :
    toGlobal F a (schemeHomOverComp ψ hψ x) = ψ ≫ toGlobal F a x :=
  Category.assoc _ _ _

section Rebase

variable {R R' : Type} [CommRing R] [CommRing R']
    (a : Spec (CommRingCat.of R) ⟶ S) (a' : Spec (CommRingCat.of R') ⟶ S)
    (ρ : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R')) (ha : ρ ≫ a' = a)

/-- Move a point to a larger affine chart through the equality of structural maps. -/
def up {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver t (pullback.snd F.hom a)) :
    SchemeHomOver (t ≫ ρ) (pullback.snd F.hom a') :=
  fromGlobal F a' (t ≫ ρ) (toGlobal F a x) (by
    rw [toGlobal_over, Category.assoc, ha])

/-- Move back to the smaller affine chart. -/
def down {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver (t ≫ ρ) (pullback.snd F.hom a')) :
    SchemeHomOver t (pullback.snd F.hom a) :=
  fromGlobal F a t (toGlobal F a' x) (by rw [toGlobal_over, Category.assoc, ha])

@[simp] theorem toGlobal_up {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver t (pullback.snd F.hom a)) :
    toGlobal F a' (up F a a' ρ ha t x) = toGlobal F a x := by
  simp only [up, toGlobal_fromGlobal]

@[simp] theorem toGlobal_down {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver (t ≫ ρ) (pullback.snd F.hom a')) :
    toGlobal F a (down F a a' ρ ha t x) = toGlobal F a' x := by
  simp only [down, toGlobal_fromGlobal]

@[simp] theorem up_down {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver (t ≫ ρ) (pullback.snd F.hom a')) :
    up F a a' ρ ha t (down F a a' ρ ha t x) = x := by
  apply toGlobal_injective F a' (t ≫ ρ)
  simp only [toGlobal_up, toGlobal_down]

@[simp] theorem down_up {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver t (pullback.snd F.hom a)) :
    down F a a' ρ ha t (up F a a' ρ ha t x) = x := by
  apply toGlobal_injective F a t
  simp only [toGlobal_up, toGlobal_down]

theorem up_injective {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) :
    Function.Injective (up F a a' ρ ha t) := by
  intro x y h
  have h' := congrArg (down F a a' ρ ha t) h
  simpa only [down_up] using h'

theorem up_comp {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (x : SchemeHomOver t (pullback.snd F.hom a)) :
    up F a a' ρ ha t' (schemeHomOverComp ψ hψ x) =
      schemeHomOverComp ψ (by rw [← Category.assoc, hψ]) (up F a a' ρ ha t x) := by
  apply toGlobal_injective F a' (t' ≫ ρ)
  simp only [toGlobal_up, toGlobal_comp]

/-- Pull back a law from one affine chart to another, without choosing any point-level
identifications of schemes. -/
def rebaseLaw (L : RelativeGroupLaw R' (pullback.snd F.hom a')) :
    RelativeGroupLaw R (pullback.snd F.hom a) where
  mul t x y := down F a a' ρ ha t
    (L.mul (t ≫ ρ) (up F a a' ρ ha t x) (up F a a' ρ ha t y))
  one t := down F a a' ρ ha t (L.one (t ≫ ρ))
  inv t x := down F a a' ρ ha t (L.inv (t ≫ ρ) (up F a a' ρ ha t x))
  mul_assoc t x y z := by
    apply up_injective F a a' ρ ha t
    simp only [up_down]
    exact L.mul_assoc _ _ _ _
  one_mul t x := by
    apply up_injective F a a' ρ ha t
    simp only [up_down]
    exact L.one_mul _ _
  mul_one t x := by
    apply up_injective F a a' ρ ha t
    simp only [up_down]
    exact L.mul_one _ _
  inv_mul_cancel t x := by
    apply up_injective F a a' ρ ha t
    simp only [up_down]
    exact L.inv_mul_cancel _ _
  mul_natural t t' ψ hψ x y := by
    apply up_injective F a a' ρ ha t'
    rw [up_comp]
    simp only [up_down]
    rw [L.mul_natural]
    rw [up_comp, up_comp]

end Rebase

/-- The identity of a local law at an arbitrary test scheme is the pullback of the given
section. This is a scheme-morphism equality. -/
theorem toGlobal_one {R : Type} [CommRing R] (a : Spec (CommRingCat.of R) ⟶ S)
    (e : S ⟶ F.left) (he : e ≫ F.hom = 𝟙 S)
    (L : RelativeGroupLaw R (pullback.snd F.hom a))
    (hL : L.one (𝟙 _) = affineSection F e he a)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) :
    toGlobal F a (L.one t) = t ≫ a ≫ e := by
  rw [← L.one_natural (𝟙 _) t t (Category.comp_id t), toGlobal_comp, hL]
  simp only [toGlobal, affineSection, pullback.lift_fst, Category.assoc]

/-- Rebased laws retain exactly the original section. -/
theorem rebaseLaw_one {R R' : Type} [CommRing R] [CommRing R']
    (a : Spec (CommRingCat.of R) ⟶ S) (a' : Spec (CommRingCat.of R') ⟶ S)
    (ρ : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R')) (ha : ρ ≫ a' = a)
    (e : S ⟶ F.left) (he : e ≫ F.hom = 𝟙 S)
    (L : RelativeGroupLaw R' (pullback.snd F.hom a'))
    (hL : L.one (𝟙 _) = affineSection F e he a') :
    (rebaseLaw F a a' ρ ha L).one (𝟙 _) = affineSection F e he a := by
  apply toGlobal_injective F a (𝟙 _)
  change toGlobal F a (down F a a' ρ ha (𝟙 _) (L.one (𝟙 _ ≫ ρ))) = _
  rw [toGlobal_down, toGlobal_one F a' e he L hL]
  simp only [Category.id_comp, toGlobal, affineSection, pullback.lift_fst]
  exact (Category.assoc ρ a' e).symm.trans (congrArg (· ≫ e) ha)

/-- Naturality of inverses follows from the group axioms and multiplication naturality. -/
theorem inv_natural {R : Type} [CommRing R] {A : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (x : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (L.inv t x) = L.inv t' (schemeHomOverComp ψ hψ x) := by
  letI := L.pointGroup t
  letI := L.pointGroup t'
  let φ : SchemeHomOver t f →* SchemeHomOver t' f :=
    { toFun := schemeHomOverComp ψ hψ
      map_one' := L.one_natural t t' ψ hψ
      map_mul' := L.mul_natural t t' ψ hψ }
  exact map_inv φ x

/-- A family of unique local laws, used only as internal proof data. -/
structure LawSystem (e : S ⟶ F.left) (he : e ≫ F.hom = 𝟙 S) where
  law : ∀ {R : Type} [CommRing R] [IsNoetherianRing R]
    (a : Spec (CommRingCat.of R) ⟶ S), RelativeGroupLaw R (pullback.snd F.hom a)
  unit : ∀ {R : Type} [CommRing R] [IsNoetherianRing R]
    (a : Spec (CommRingCat.of R) ⟶ S), (law a).one (𝟙 _) = affineSection F e he a
  unique : ∀ {R : Type} [CommRing R] [IsNoetherianRing R]
    (a : Spec (CommRingCat.of R) ⟶ S) (L : RelativeGroupLaw R (pullback.snd F.hom a)),
    L.one (𝟙 _) = affineSection F e he a → L = law a

variable {F} {e : S ⟶ F.left} {he : e ≫ F.hom = 𝟙 S}

/-- Construct the internal local-law family from the affine theorem. -/
def lawSystem (h : AffineGroupLaw.{0}) (F : Over S) (e : S ⟶ F.left)
    (he : e ≫ F.hom = 𝟙 S)
    [Smooth F.hom] [IsProper F.hom] [GeometricallyConnected F.hom]
    (hfib : ∀ (k : Type) [Field k] (s : Spec (CommRingCat.of k) ⟶ S),
      ∃ (A : PkgI3.AbVar k) (g : A.X.left ⟶ F.left),
        LeafQM.AV.R1UnivRigid.IsAbVarFibre F e s A g) : LawSystem F e he where
  law a := (exists_unique_affineLaw h F e he hfib a).choose
  unit a := (exists_unique_affineLaw h F e he hfib a).choose_spec.1
  unique a := (exists_unique_affineLaw h F e he hfib a).choose_spec.2.2

variable (D : LawSystem F e he)

theorem law_rebase {R R' : Type} [CommRing R] [CommRing R']
    [IsNoetherianRing R] [IsNoetherianRing R']
    (a : Spec (CommRingCat.of R) ⟶ S) (a' : Spec (CommRingCat.of R') ⟶ S)
    (ρ : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R')) (ha : ρ ≫ a' = a) :
    D.law a = rebaseLaw F a a' ρ ha (D.law a') :=
  (D.unique a _ (rebaseLaw_one F a a' ρ ha e he _ (D.unit a'))).symm

section Global

variable [IsLocallyNoetherian S]

/-- The affine base map for one member of the directed cover. -/
def base (U : S.affineOpens) : Spec Γ(S, U.1) ⟶ S := U.2.isoSpec.inv ≫ U.1.ι

instance ring_noetherian (U : S.affineOpens) : IsNoetherianRing Γ(S, U.1) :=
  affineOpen_noetherian U

/-- The locally directed cover on an arbitrary test scheme. -/
def cover (T : Over S) : T.left.OpenCover := S.directedAffineCover.pullback₁ T.hom

/-- The structural map of a cover piece to the affine coordinate spectrum. -/
def tau (T : Over S) (U : S.affineOpens) : (cover T).X U ⟶ Spec Γ(S, U.1) :=
  pullback.snd T.hom U.1.ι ≫ U.2.isoSpec.hom

theorem tau_base (T : Over S) (U : S.affineOpens) :
    tau T U ≫ base U = (cover T).f U ≫ T.hom := by
  simp only [tau, base, Category.assoc, Iso.hom_inv_id_assoc]
  exact pullback.condition.symm

/-- The affine transition map associated with an inclusion. -/
def rho {U V : S.affineOpens} (hUV : U ≤ V) : Spec Γ(S, U.1) ⟶ Spec Γ(S, V.1) :=
  U.2.isoSpec.inv ≫ S.homOfLE hUV ≫ V.2.isoSpec.hom

theorem rho_base {U V : S.affineOpens} (hUV : U ≤ V) :
    rho hUV ≫ base V = base U := by
  simp only [rho, base, Category.assoc, Iso.hom_inv_id_assoc, Scheme.homOfLE_ι]

theorem tau_trans (T : Over S) {U V : S.affineOpens} (hUV : U ≤ V) :
    (cover T).trans (homOfLE hUV) ≫ tau T V = tau T U ≫ rho hUV := by
  haveI : IsOpenImmersion (base V) := by dsimp [base]; infer_instance
  apply (cancel_mono (base V)).mp
  calc
    ((cover T).trans (homOfLE hUV) ≫ tau T V) ≫ base V =
        (cover T).trans (homOfLE hUV) ≫ ((cover T).f V ≫ T.hom) := by
          rw [Category.assoc, tau_base]
    _ = (cover T).f U ≫ T.hom := by
      rw [← Category.assoc, Scheme.Cover.trans_map]
    _ = tau T U ≫ base U := (tau_base T U).symm
    _ = (tau T U ≫ rho hUV) ≫ base V := by rw [Category.assoc, rho_base]

/-- The pullback of a global family-valued morphism to a cover piece. -/
def point {T : Over S} (x : T ⟶ F) (U : S.affineOpens) :
    SchemeHomOver (tau T U) (pullback.snd F.hom (base U)) :=
  fromGlobal F (base U) (tau T U) ((cover T).f U ≫ x.left) (by
    rw [Category.assoc, Over.w x, tau_base])

@[simp] theorem point_global {T : Over S} (x : T ⟶ F) (U : S.affineOpens) :
    toGlobal F (base U) (point x U) = (cover T).f U ≫ x.left := by
  simp only [point, toGlobal_fromGlobal]

/-- Scheme morphisms agree if their restrictions to the directed cover agree. -/
theorem point_ext {T : Over S} {x y : T ⟶ F}
    (h : ∀ U : S.affineOpens, point x U = point y U) : x = y := by
  apply Over.OverMorphism.ext
  apply (cover T).hom_ext
  intro U
  have h' := congrArg (toGlobal F (base U)) (h U)
  simpa only [point_global] using h'

/-- Restrictions of global morphisms coincide with affine transition of their local points. -/
theorem point_up {T : Over S} (x : T ⟶ F) {U V : S.affineOpens} (hUV : U ≤ V) :
    up F (base U) (base V) (rho hUV) (rho_base hUV) (tau T U) (point x U) =
      schemeHomOverComp ((cover T).trans (homOfLE hUV)) (tau_trans T hUV) (point x V) := by
  apply toGlobal_injective F (base V) (tau T U ≫ rho hUV)
  simp only [toGlobal_up, point_global, toGlobal_comp, ← Category.assoc,
    Scheme.Cover.trans_map]

/-- Local multiplication, projected back into the original family. -/
def mulLocal {T : Over S} (x y : T ⟶ F) (U : S.affineOpens) : (cover T).X U ⟶ F.left :=
  toGlobal F (base U) ((D.law (base U)).mul (tau T U) (point x U) (point y U))

/-- Uniqueness with the prescribed unit supplies multiplication compatibility on inclusions. -/
theorem mulLocal_compat {T : Over S} (x y : T ⟶ F) {U V : S.affineOpens} (hUV : U ≤ V) :
    (cover T).trans (homOfLE hUV) ≫ mulLocal D x y V = mulLocal D x y U := by
  rw [mulLocal, mulLocal, D.law_rebase (base U) (base V) (rho hUV) (rho_base hUV)]
  change _ = toGlobal F (base U) (down F (base U) (base V) (rho hUV)
    (rho_base hUV) (tau T U) _)
  rw [toGlobal_down, point_up, point_up]
  simpa only [toGlobal_comp] using congrArg (toGlobal F (base V))
    ((D.law (base V)).mul_natural (tau T V) (tau T U ≫ rho hUV)
      ((cover T).trans (homOfLE hUV)) (tau_trans T hUV) (point x V) (point y V))

/-- Global multiplication from scheme-morphism gluing. -/
def mul {T : Over S} (x y : T ⟶ F) : T ⟶ F :=
  (cover T).glueMorphismsOverOfLocallyDirected (mulLocal D x y)
    (fun hij => mulLocal_compat D x y (leOfHom hij))
    (fun U => by rw [mulLocal, toGlobal_over, tau_base])

@[simp] theorem point_mul {T : Over S} (x y : T ⟶ F) (U : S.affineOpens) :
    point (mul D x y) U = (D.law (base U)).mul (tau T U) (point x U) (point y U) := by
  apply toGlobal_injective F (base U) (tau T U)
  rw [point_global]
  exact (cover T).map_glueMorphismsOverOfLocallyDirected_left _ _ _ U

/-- Local inverse. -/
def invLocal {T : Over S} (x : T ⟶ F) (U : S.affineOpens) : (cover T).X U ⟶ F.left :=
  toGlobal F (base U) ((D.law (base U)).inv (tau T U) (point x U))

theorem invLocal_compat {T : Over S} (x : T ⟶ F) {U V : S.affineOpens} (hUV : U ≤ V) :
    (cover T).trans (homOfLE hUV) ≫ invLocal D x V = invLocal D x U := by
  rw [invLocal, invLocal, D.law_rebase (base U) (base V) (rho hUV) (rho_base hUV)]
  change _ = toGlobal F (base U) (down F (base U) (base V) (rho hUV)
    (rho_base hUV) (tau T U) _)
  rw [toGlobal_down, point_up]
  simpa only [toGlobal_comp] using congrArg (toGlobal F (base V))
    (inv_natural (D.law (base V)) (tau T V) (tau T U ≫ rho hUV)
      ((cover T).trans (homOfLE hUV)) (tau_trans T hUV) (point x V))

/-- Global inverse from scheme-morphism gluing. -/
def inv {T : Over S} (x : T ⟶ F) : T ⟶ F :=
  (cover T).glueMorphismsOverOfLocallyDirected (invLocal D x)
    (fun hij => invLocal_compat D x (leOfHom hij))
    (fun U => by rw [invLocal, toGlobal_over, tau_base])

@[simp] theorem point_inv {T : Over S} (x : T ⟶ F) (U : S.affineOpens) :
    point (inv D x) U = (D.law (base U)).inv (tau T U) (point x U) := by
  apply toGlobal_injective F (base U) (tau T U)
  rw [point_global]
  exact (cover T).map_glueMorphismsOverOfLocallyDirected_left _ _ _ U

/-- The global unit is the original section. -/
def one (T : Over S) : T ⟶ F := Over.homMk (T.hom ≫ e) (by
  rw [Category.assoc, he, Category.comp_id])

@[simp] theorem point_one (T : Over S) (U : S.affineOpens) :
    point (one T (e := e) (he := he)) U = (D.law (base U)).one (tau T U) := by
  apply toGlobal_injective F (base U) (tau T U)
  rw [point_global, toGlobal_one F (base U) e he _ (D.unit (base U))]
  simp only [one, Over.homMk_left, Category.assoc, tau_base]

/-- The local affine laws make all global morphism sets into groups. -/
def pointGroup (T : Over S) : Group (T ⟶ F) where
  mul := mul D
  one := one T
  inv := inv D
  mul_assoc x y z := by
    apply point_ext
    intro U
    simp only [point_mul]
    exact (D.law (base U)).mul_assoc _ _ _ _
  one_mul x := by
    apply point_ext
    intro U
    simp only [point_mul, point_one]
    exact (D.law (base U)).one_mul _ _
  mul_one x := by
    apply point_ext
    intro U
    simp only [point_mul, point_one]
    exact (D.law (base U)).mul_one _ _
  inv_mul_cancel x := by
    apply point_ext
    intro U
    simp only [point_mul, point_inv, point_one]
    exact (D.law (base U)).inv_mul_cancel _ _

/-- The induced morphism of affine cover pieces for a morphism of test schemes. -/
def pieceMap {T T' : Over S} (ψ : T' ⟶ T) (U : S.affineOpens) :
    (cover T').X U ⟶ (cover T).X U :=
  pullback.map T'.hom U.1.ι T.hom U.1.ι ψ.left (𝟙 _) (𝟙 _)
    (by simpa using Over.w ψ) (by simp)

@[simp] theorem pieceMap_f {T T' : Over S} (ψ : T' ⟶ T) (U : S.affineOpens) :
    pieceMap ψ U ≫ (cover T).f U = (cover T').f U ≫ ψ.left := by
  simp only [pieceMap, cover, Scheme.directedAffineCover_f, pullback.lift_fst]

theorem pieceMap_tau {T T' : Over S} (ψ : T' ⟶ T) (U : S.affineOpens) :
    pieceMap ψ U ≫ tau T U = tau T' U := by
  haveI : IsOpenImmersion (base U) := by dsimp [base]; infer_instance
  apply (cancel_mono (base U)).mp
  rw [Category.assoc, tau_base, ← Category.assoc, pieceMap_f,
    Category.assoc, Over.w ψ, tau_base]

theorem point_precomp {T T' : Over S} (ψ : T' ⟶ T) (x : T ⟶ F) (U : S.affineOpens) :
    point (ψ ≫ x) U = schemeHomOverComp (pieceMap ψ U) (pieceMap_tau ψ U) (point x U) := by
  apply toGlobal_injective F (base U) (tau T' U)
  simp only [point_global, Over.comp_left, toGlobal_comp, ← Category.assoc, pieceMap_f]

/-- Global multiplication is natural on ALL scheme-valued points. -/
theorem mul_natural {T T' : Over S} (ψ : T' ⟶ T) (x y : T ⟶ F) :
    ψ ≫ mul D x y = mul D (ψ ≫ x) (ψ ≫ y) := by
  apply point_ext
  intro U
  rw [point_precomp, point_mul, point_mul, point_precomp, point_precomp]
  exact (D.law (base U)).mul_natural _ _ _ (pieceMap_tau ψ U) _ _

/-- The presheaf of global family-valued points, equipped with the glued group laws. -/
def groupPresheaf : (Over S)ᵒᵖ ⥤ GrpCat.{0} where
  obj T := @GrpCat.of (T.unop ⟶ F) (pointGroup D T.unop)
  map {T T'} ψ :=
    letI := pointGroup D T.unop
    letI := pointGroup D T'.unop
    GrpCat.ofHom
      { toFun := fun x => ψ.unop ≫ x
        map_one' := by
          apply Over.OverMorphism.ext
          simp only [one, Over.comp_left, Over.homMk_left, Category.assoc, Over.w]
        map_mul' := mul_natural D ψ.unop }
  map_id T := by
    letI := pointGroup D T.unop
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    exact Category.id_comp x
  map_comp ψ ψ' := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    exact (Category.assoc _ _ _).symm

/-- The forgetful presheaf is represented by the ORIGINAL object F. -/
def represents : (groupPresheaf D ⋙ forget GrpCat).RepresentableBy F where
  homEquiv := Equiv.refl _
  homEquiv_comp _ _ := rfl

/-- Scheme-level gluing followed by Yoneda supplies a group object, with the given section. -/
theorem exists_grpObj : ∃ _G : GrpObj F, η[F].left = e := by
  letI G : GrpObj F := GrpObj.ofRepresentableBy F (groupPresheaf D) (represents D)
  refine ⟨G, ?_⟩
  change (𝟙 S ≫ e) = e
  exact Category.id_comp e

end Global
end AffineGlue

/-- The affine theorem implies the exact, arbitrary-locally-noetherian-base Mumford statement. -/
theorem mumfordGroupLaw_of_affine (h : AffineGroupLaw.{0}) :
    ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw := by
  intro S F e hN hP hS hC he hfib
  letI := hN
  letI := hP
  letI := hS
  letI := hC
  exact AffineGlue.exists_grpObj (AffineGlue.lawSystem h F e he hfib)

end ZInQ.Contrib.CloudB3SC2Mumford

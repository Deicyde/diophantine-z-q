import ZInQKernel.HDecomp.Objects
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Properties

/-!
# The generic-fibre map on `w`-sections of a Néron model

Let `O` be a valuation subring of a field `K`, `Ω ⊇ K` a field and `w` a valuation subring of `Ω`
lying over `O`. For an abelian variety `A / K` and an `O`-scheme `N` with an identification
`e : N_K ≅ A`, an `O`-morphism `s : Spec w ⟶ N` has a generic fibre `Φ s ∈ A(Ω)`: restrict `s_K`
to the generic geometric point `Spec Ω ⟶ (Spec w)_K` and compose with `e`.

* `genericFibre_injective`: if `N` is separated over `O`, then `Φ` is injective (`Spec w` is
  reduced and its generic point is dense).
* `genericFibreHom`: if `N` is a group scheme over `O` and `e` is a homomorphism for the induced
  group structure on `N_K`, then `Φ` is a group homomorphism into the group `A(Ω)`.
* `pow_eq_one_iff_genericFibre`: consequently a `w`-section is `m`-torsion if and only if its
  generic fibre is.

The data `(N, e)` and the hypotheses are exactly the fields of a smooth separated group model with
its generic-fibre isomorphism; nothing about inertia, torsion levels or Néron mapping is assumed.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Limits IsLocalRing MonoidalCategory
  CartesianMonoidalCategory MonObj

namespace NeronInvariantTorsion

variable {K : Type} [Field K]

/-- `Spec K → Spec O`. -/
abbrev jO (O : ValuationSubring K) : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of O) :=
  Spec.map (CommRingCat.ofHom (algebraMap O K))

section Ring

variable {Ω : Type} [Field Ω] [Algebra K Ω]
variable (O : ValuationSubring K) (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O)

include hw in
theorem mem_w_of_mem (a : O) : algebraMap K Ω (a : K) ∈ w := by
  have h : (a : K) ∈ w.comap (algebraMap K Ω) := by rw [hw]; exact a.2
  exact h

/-- The structure map `O → w`. -/
def ιOw : O →+* w :=
  ((algebraMap K Ω).comp O.subtype).codRestrict w (fun a => mem_w_of_mem O w hw a)

theorem ιOw_coe (a : O) : ((ιOw O w hw a : w) : Ω) = algebraMap K Ω (a : K) := rfl

/-- A valuation subring is the ring of integers of its valuation. -/
theorem integers_valuation : w.valuation.Integers w where
  hom_inj := Subtype.val_injective
  map_le_one x := w.valuation_le_one x
  exists_of_le_one {r} h := ⟨⟨r, (w.valuation_le_one_iff r).mp h⟩, rfl⟩

end Ring

section Generic

variable {Ω : Type} [Field Ω] [Algebra K Ω]
variable (O : ValuationSubring K) (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O)

/-- `Spec w` as an `O`-scheme. -/
def specW : Over (Spec (CommRingCat.of O)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (ιOw O w hw)))

theorem genPt_comm :
    Spec.map (CommRingCat.ofHom (algebraMap w Ω)) ≫ (specW O w hw).hom =
      Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ jO O := by
  simp only [specW, Over.mk_hom, jO, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

/-- The generic geometric point `Spec Ω ⟶ (Spec w)_K`, a `K`-morphism. -/
def genPt : PkgI3.AbVar.ptObj (K := K) Ω ⟶ (Over.pullback (jO O)).obj (specW O w hw) :=
  Over.homMk (pullback.lift _ _ (genPt_comm O w hw)) (pullback.lift_snd _ _ _)

theorem genPt_left_fst :
    (genPt O w hw).left ≫ pullback.fst (specW O w hw).hom (jO O) =
      Spec.map (CommRingCat.ofHom (algebraMap w Ω)) :=
  pullback.lift_fst _ _ _

/-- `Spec Ω → Spec w` is dominant. -/
theorem isDominant_specMap : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap w Ω))) := by
  apply isDominant_of_of_appTop_injective
  intro a b hab
  have hnat : ∀ c, (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom
      ((Spec.map (CommRingCat.ofHom (algebraMap w Ω))).appTop c) =
        algebraMap w Ω ((Scheme.ΓSpecIso (CommRingCat.of w)).hom c) := fun c => by
    have h := ConcreteCategory.congr_hom
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap w Ω))) c
    exact h
  have h2 := congrArg (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom) hab
  rw [hnat, hnat] at h2
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of w)).hom).1
    (Subtype.val_injective h2)

variable {A : PkgI3.AbVar K} {N : Over (Spec (CommRingCat.of O))}
  (e : (Over.pullback (jO O)).obj N ≅ A.X)

/-- **The generic-fibre map** `Φ : N(w) → A(Ω)`, `s ↦ e ∘ s_K ∘ (generic geometric point)`. -/
def genericFibre (s : specW O w hw ⟶ N) : A.Pt Ω :=
  genPt O w hw ≫ (Over.pullback (jO O)).map s ≫ e.hom

/-- The generic fibre of `s`, read in `N`, is `s` restricted to `Spec Ω`. -/
theorem genericFibre_left_fst (s : specW O w hw ⟶ N) :
    ((genericFibre O w hw e s) ≫ e.inv).left ≫ pullback.fst N.hom (jO O) =
      Spec.map (CommRingCat.ofHom (algebraMap w Ω)) ≫ s.left := by
  simp only [genericFibre, Category.assoc, Iso.hom_inv_id, Category.comp_id, Over.comp_left,
    Over.pullback_map_left, pullback.lift_fst]
  rw [← Category.assoc, genPt_left_fst]
  rfl

/-- **Uniqueness (separatedness).** If `N` is separated over `O`, a `w`-section of `N` is
determined by its generic fibre. -/
theorem genericFibre_injective [IsSeparated N.hom] :
    Function.Injective (genericFibre O w hw e) := by
  intro s s' h
  have h2 : Spec.map (CommRingCat.ofHom (algebraMap w Ω)) ≫ s.left =
      Spec.map (CommRingCat.ofHom (algebraMap w Ω)) ≫ s'.left := by
    rw [← genericFibre_left_fst, ← genericFibre_left_fst, h]
  have hred : AlgebraicGeometry.IsReduced (specW O w hw).left :=
    (inferInstance : AlgebraicGeometry.IsReduced (Spec (CommRingCat.of w)))
  apply Over.OverMorphism.ext
  exact @ext_of_isDominant_of_isSeparated _ _ _ _ hred s.left s'.left N.hom _
    (by rw [Over.w s, Over.w s']) (Spec.map (CommRingCat.ofHom (algebraMap w Ω)))
    (isDominant_specMap w) h2

open scoped Obj in
/-- **Multiplicativity.** If `N` is a group scheme over `O` and `e` is a homomorphism for the
induced group structure on `N_K`, then `Φ` preserves products. -/
theorem genericFibre_mul [GrpObj N]
    (hgen : letI : GrpObj ((Over.pullback (jO O)).obj N) := Functor.grpObjObj
      IsMonHom e.hom)
    (s s' : specW O w hw ⟶ N) :
    genericFibre O w hw e (s * s') = genericFibre O w hw e s * genericFibre O w hw e s' := by
  unfold genericFibre
  rw [Functor.map_mul, MonObj.mul_comp, MonObj.comp_mul]

open scoped Obj in
theorem genericFibre_one [GrpObj N]
    (hgen : letI : GrpObj ((Over.pullback (jO O)).obj N) := Functor.grpObjObj
      IsMonHom e.hom) :
    genericFibre O w hw e (1 : specW O w hw ⟶ N) = 1 := by
  unfold genericFibre
  rw [Functor.map_one, MonObj.one_comp, MonObj.comp_one]

open scoped Obj in
/-- `Φ` as a monoid homomorphism `N(w) →* A(Ω)`. -/
def genericFibreHom [GrpObj N]
    (hgen : letI : GrpObj ((Over.pullback (jO O)).obj N) := Functor.grpObjObj
      IsMonHom e.hom) :
    (specW O w hw ⟶ N) →* A.Pt Ω where
  toFun := genericFibre O w hw e
  map_one' := genericFibre_one O w hw e hgen
  map_mul' := genericFibre_mul O w hw e hgen

open scoped Obj in
/-- **Torsion.** For a separated group model, a `w`-section is `m`-torsion if and only if its
generic fibre is. -/
theorem pow_eq_one_iff_genericFibre [GrpObj N] [IsSeparated N.hom]
    (hgen : letI : GrpObj ((Over.pullback (jO O)).obj N) := Functor.grpObjObj
      IsMonHom e.hom)
    (s : specW O w hw ⟶ N) (m : ℕ) :
    s ^ m = 1 ↔ genericFibre O w hw e s ^ m = 1 := by
  have hpow : genericFibre O w hw e (s ^ m) = genericFibre O w hw e s ^ m :=
    map_pow (genericFibreHom O w hw e hgen) s m
  constructor
  · intro h
    rw [← hpow, h]
    exact genericFibre_one O w hw e hgen
  · intro h
    apply genericFibre_injective O w hw e
    rw [hpow, h, genericFibre_one O w hw e hgen]

end Generic

end NeronInvariantTorsion

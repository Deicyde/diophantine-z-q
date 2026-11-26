import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Continuous

set_option autoImplicit false

/-!
# Constant-sheaf transport along a continuous site equivalence

Source-only candidate for Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.
Both directions of the underlying equivalence are continuous. No terminal object or comparison
premise is used.
-/

open CategoryTheory

namespace ConstantSheafTransport

universe uC vC uD vD uA vA

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
variable (e : C ≌ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable (A : Type uA) [Category.{vA} A] [HasWeakSheafify J A] [HasWeakSheafify K A]
variable [e.functor.IsContinuous J K]

local notation "R" => e.functor.sheafPushforwardContinuous A J K
private abbrev restrictPresheaf : (Dᵒᵖ ⥤ A) ⥤ Cᵒᵖ ⥤ A :=
  (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj e.functor.op
local notation "PJ" => Functor.const Cᵒᵖ
local notation "PK" => Functor.const Dᵒᵖ
local notation "CJ" => constantSheaf J A
local notation "CK" => constantSheaf K A

private theorem constantHom_ext (M : A) {B : Sheaf J A} {f g : (CJ).obj M ⟶ B}
    (h : toSheafify J ((PJ).obj M) ≫ f.hom = toSheafify J ((PJ).obj M) ≫ g.hom) :
    f = g := by
  apply Sheaf.hom_ext
  exact sheafify_hom_ext J f.hom g.hom B.property h

private noncomputable def kHom (M : A) : (CJ).obj M ⟶ (R).obj ((CK).obj M) :=
  ⟨sheafifyLift J (Functor.whiskerLeft e.functor.op (toSheafify K ((PK).obj M)))
    ((R).obj ((CK).obj M)).property⟩

private theorem kHom_unit (M : A) :
    toSheafify J ((PJ).obj M) ≫ (kHom e J K A M).hom =
      Functor.whiskerLeft e.functor.op (toSheafify K ((PK).obj M)) :=
  toSheafify_sheafifyLift J _ _

private theorem precomp_unit (M : A) {B : Sheaf K A} (g : (CK).obj M ⟶ B) :
    toSheafify J ((PJ).obj M) ≫ (kHom e J K A M ≫ (R).map g).hom =
      (restrictPresheaf e A).map (toSheafify K ((PK).obj M) ≫ g.hom) := by
  let Q := restrictPresheaf e A
  let η := toSheafify K ((PK).obj M)
  let hB := ((R).obj ((CK).obj M)).property
  let l := sheafifyLift J (Q.map η) hB
  let ψ := toSheafify J ((PJ).obj M)
  change ψ ≫ (l ≫ Q.map g.hom) = Q.map (η ≫ g.hom)
  calc
    _ = (ψ ≫ l) ≫ Q.map g.hom := (Category.assoc ψ l (Q.map g.hom)).symm
    _ = Q.map η ≫ Q.map g.hom := congrArg (fun h => h ≫ Q.map g.hom)
      (toSheafify_sheafifyLift J (Q.map η) hB)
    _ = _ := (Q.map_comp η g.hom).symm

variable [hInv : e.inverse.IsContinuous K J]
include hInv

/-- An equivalence with precisely the restriction functor as its forward functor. -/
private noncomputable def restrictionEquivalence : Sheaf K A ≌ Sheaf J A := by
  letI : (𝟭 C : C ⥤ C).IsContinuous J J := inferInstance
  letI : (𝟭 D : D ⥤ D).IsContinuous K K := inferInstance
  refine CategoryTheory.Equivalence.mk R (e.inverse.sheafPushforwardContinuous A K J) ?_ ?_
  · exact (Functor.sheafPushforwardContinuousComp' e.counitIso A K J K ≪≫
      Functor.sheafPushforwardContinuousId A K).symm
  · exact Functor.sheafPushforwardContinuousComp' e.unitIso.symm A J K J ≪≫
      Functor.sheafPushforwardContinuousId A J

/-- Test precomposition against objects in the image of the exact restriction. -/
private theorem precomp_bijective (M : A) (B : Sheaf K A) :
    Function.Bijective (fun f : (R).obj ((CK).obj M) ⟶ (R).obj B => kHom e J K A M ≫ f) := by
  let hR : (R).FullyFaithful := (restrictionEquivalence (e := e) (J := J) (K := K) (A := A)).fullyFaithfulFunctor
  let hW : (restrictPresheaf e A).FullyFaithful := (e.op.congrLeft (E := A)).fullyFaithfulInverse
  constructor
  · intro f f' h
    obtain ⟨g, hg⟩ := hR.map_surjective f
    obtain ⟨g', hg'⟩ := hR.map_surjective f'
    subst f
    subst f'
    have hs := congrArg
      (fun q : (CJ).obj M ⟶ (R).obj B => toSheafify J ((PJ).obj M) ≫ q.hom) h
    change toSheafify J ((PJ).obj M) ≫ (kHom e J K A M ≫ (R).map g).hom =
      toSheafify J ((PJ).obj M) ≫ (kHom e J K A M ≫ (R).map g').hom at hs
    rw [precomp_unit e J K A M g, precomp_unit e J K A M g'] at hs
    have hgg : g = g' := constantHom_ext K A M (hW.map_injective hs)
    exact congrArg (fun q : (CK).obj M ⟶ B => (R).map q) hgg
  · intro f
    obtain ⟨η, hη⟩ := hW.map_surjective (X := (PK).obj M) (Y := B.obj)
      (toSheafify J ((PJ).obj M) ≫ f.hom)
    let g : (CK).obj M ⟶ B := ⟨sheafifyLift K η B.property⟩
    refine ⟨(R).map g, constantHom_ext J A M ?_⟩
    rw [precomp_unit e J K A M g]
    change (restrictPresheaf e A).map (toSheafify K ((PK).obj M) ≫ sheafifyLift K η B.property) = _
    rw [toSheafify_sheafifyLift]
    exact hη

private theorem kHom_isIso (M : A) : IsIso (kHom e J K A M) := by
  let s := restrictionEquivalence (e := e) (J := J) (K := K) (A := A)
  let B := s.inverse.obj ((CJ).obj M)
  let t : (R).obj B ≅ (CJ).obj M := s.counitIso.app ((CJ).obj M)
  obtain ⟨r, hr⟩ := (precomp_bijective e J K A M B).2 t.inv
  change kHom e J K A M ≫ r = t.inv at hr
  let i := r ≫ t.hom
  have hi : kHom e J K A M ≫ i = 𝟙 ((CJ).obj M) := by
    change kHom e J K A M ≫ (r ≫ t.hom) = _
    rw [← Category.assoc, hr, t.inv_hom_id]
  refine ⟨⟨i, hi, ?_⟩⟩
  apply (precomp_bijective e J K A M ((CK).obj M)).1
  change kHom e J K A M ≫ (i ≫ kHom e J K A M) = kHom e J K A M ≫ 𝟙 _
  rw [← Category.assoc, hi, Category.id_comp, Category.comp_id]

/-- The constant sheaf comparison, oriented from the source site to the restricted sheaf. -/
noncomputable def k : CJ ≅ CK ⋙ R :=
  NatIso.ofComponents (fun M => by
    letI := kHom_isIso e J K A M
    exact asIso (kHom e J K A M)) (by
      intro M N f
      apply constantHom_ext J A M
      let Q := restrictPresheaf e A
      let cJ := (PJ).map f
      let cK := (PK).map f
      let ηM := toSheafify K ((PK).obj M)
      let ηN := toSheafify K ((PK).obj N)
      let γM := toSheafify J ((PJ).obj M)
      let γN := toSheafify J ((PJ).obj N)
      let hM := ((R).obj ((CK).obj M)).property
      let hN := ((R).obj ((CK).obj N)).property
      let lM := sheafifyLift J (Q.map ηM) hM
      let lN := sheafifyLift J (Q.map ηN) hN
      let sJ := sheafifyMap J cJ
      let sK := sheafifyMap K cK
      change γM ≫ (sJ ≫ lN) = γM ≫ (lM ≫ Q.map sK)
      have hJ : cJ ≫ γN = γM ≫ sJ := toSheafify_naturality J cJ
      have hK : cK ≫ ηN = ηM ≫ sK := toSheafify_naturality K cK
      have hc : Q.map cK = cJ := rfl
      have hlM : γM ≫ lM = Q.map ηM := toSheafify_sheafifyLift J (Q.map ηM) hM
      have hlN : γN ≫ lN = Q.map ηN := toSheafify_sheafifyLift J (Q.map ηN) hN
      calc
        _ = (γM ≫ sJ) ≫ lN := (Category.assoc γM sJ lN).symm
        _ = (cJ ≫ γN) ≫ lN := congrArg (fun h => h ≫ lN) hJ.symm
        _ = cJ ≫ (γN ≫ lN) := Category.assoc cJ γN lN
        _ = Q.map cK ≫ Q.map ηN := congrArg₂ (fun a b => a ≫ b) hc.symm hlN
        _ = Q.map (cK ≫ ηN) := (Q.map_comp cK ηN).symm
        _ = Q.map (ηM ≫ sK) := congrArg (fun h => Q.map h) hK
        _ = Q.map ηM ≫ Q.map sK := Q.map_comp ηM sK
        _ = (γM ≫ lM) ≫ Q.map sK := congrArg (fun h => h ≫ Q.map sK) hlM.symm
        _ = _ := Category.assoc γM lM (Q.map sK))

/-- The unit equation uses the literal restriction of the constant presheaf. -/
theorem k_toSheafify (M : A) :
    toSheafify J ((PJ).obj M) ≫ ((k e J K A).hom.app M).hom =
      Functor.whiskerLeft e.functor.op (toSheafify K ((PK).obj M)) :=
  kHom_unit e J K A M

/-- The unit equation characterizes the underlying comparison morphism. -/
theorem k_hom_unique (M : A) (f : (CJ).obj M ⟶ (R).obj ((CK).obj M))
    (hf : toSheafify J ((PJ).obj M) ≫ f.hom =
      Functor.whiskerLeft e.functor.op (toSheafify K ((PK).obj M))) :
    f = (k e J K A).hom.app M :=
  constantHom_ext J A M (hf.trans (k_toSheafify e J K A M).symm)

end ConstantSheafTransport


import HenselDivision.SmoothCommMulEtaleV001
import HenselDivision.StrictTowerV001
import HenselDivision.GenericCommutativityV004

/-!
# Torsion specialization on smooth commutative group schemes, with `[n]` étale derived

Over a henselian local ring `R` and for a smooth commutative group scheme `G` over `Spec R` with
`n` invertible in `R`, multiplication by `n` is étale (`multiplication_etale_of_smooth_comm`), so
all torsion statements of this development hold with no étaleness hypothesis:
* integral and residual `n`-torsion agree, as groups;
* over a strictly henselian `R`, integral and geometric `n`-torsion of the closed fibre agree;
* compatible residual or geometric `ℓ`-power towers lift uniquely to integral towers.
For a smooth Néron-type model (morphisms from smooth schemes determined by the generic fibre,
generic fibre a commutative group scheme) commutativity itself is derived, so only smoothness,
the mapping-property uniqueness and the generic identification remain as inputs; the generic
identification may be given with the group structure `Functor.grpObjObj` (reconciled by `rfl`).
-/

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
  IsLocalRing
open scoped MonObj

namespace HenselDivision

section General

variable {R : Type} [CommRing R]

/-- `[n]` is étale on a smooth commutative group scheme over `Spec R` when `n` is a unit. -/
theorem etale_powHom_of_smooth_comm (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    [Smooth G.hom] [IsCommMonObj G] (n : ℕ) (hn : IsUnit (n : R)) : Etale (powHom G n).left :=
  SmoothCommMulEtale.multiplication_etale_of_smooth_comm (Grp.mk G) n hn

variable [HenselianLocalRing R]

/-- Integral and residual `n`-torsion of a smooth commutative group scheme agree (`n` a unit). -/
theorem torsion_restrict_bijective_of_smooth_comm (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G] [Smooth G.hom] [IsCommMonObj G] (n : ℕ) (hn : IsUnit (n : R)) :
    Function.Bijective (fun f : {f : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G // f ^ n = 1} =>
      (⟨toUnit (closedObj R) ≫ f.1, by rw [← MonObj.comp_pow, f.2, MonObj.comp_one]⟩ :
        {f : closedObj R ⟶ G // f ^ n = 1})) :=
  torsion_restrict_bijective G n (etale_powHom_of_smooth_comm G n hn)

/-- The specialization isomorphism `G(S)[n] ≃* G(s)[n]` for a smooth commutative group scheme. -/
noncomputable def torsionRestrictEquivOfSmoothComm (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G] [Smooth G.hom] [IsCommMonObj G] (n : ℕ) (hn : IsUnit (n : R)) :
    torsionPts G (𝟙_ (Over (Spec (CommRingCat.of R)))) n ≃* torsionPts G (closedObj R) n :=
  torsionRestrictEquiv G n (etale_powHom_of_smooth_comm G n hn)

/-- Integral and geometric `n`-torsion agree over a strictly henselian base. -/
theorem torsion_integral_geom_bijective_of_smooth_comm [IsSepClosed (ResidueField R)]
    {Ω : Type} [Field Ω] [Algebra (ResidueField R) Ω] (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G] [Smooth G.hom] [IsCommMonObj G] (n : ℕ) (hn : IsUnit (n : R)) :
    Function.Bijective (fun f : {f : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G // f ^ n = 1} =>
      (⟨toUnit (geomObj R Ω) ≫ f.1, by rw [← MonObj.comp_pow, f.2, MonObj.comp_one]⟩ :
        {f : geomObj R Ω ⟶ G // f ^ n = 1})) :=
  torsion_integral_geom_bijective G n
    (etale_torsionKer_hom G n (etale_powHom_of_smooth_comm G n hn))

/-- Compatible geometric `ℓ`-power towers lift uniquely to integral towers (`ℓ` a unit). -/
theorem compatible_geom_lift_existsUnique_of_smooth_comm [IsSepClosed (ResidueField R)]
    {Ω : Type} [Field Ω] [Algebra (ResidueField R) Ω] (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G] [Smooth G.hom] [IsCommMonObj G] (ℓ : ℕ) (hℓ : IsUnit (ℓ : R))
    (x : ℕ → (geomObj R Ω ⟶ G)) (hx0 : x 0 = 1) (hx : ∀ n, x (n + 1) ^ ℓ = x n) :
    ∃! f : ℕ → (𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G),
      f 0 = 1 ∧ (∀ n, f (n + 1) ^ ℓ = f n) ∧ ∀ n, toUnit (geomObj R Ω) ≫ f n = x n :=
  compatible_geom_lift_existsUnique G ℓ (etale_powHom_of_smooth_comm G ℓ hℓ) x hx0 hx

end General

section Neron

/-- The homomorphism property of a generic identification, stated for `Functor.grpObjObj`, is
the one for `Functor.monObjObj` (the two monoid structures coincide definitionally). -/
theorem isMonHom_monObjObj_of_grpObjObj {S S' : Scheme.{0}} (j : S' ⟶ S) (G : Over S)
    [GrpObj G] (A : Over S') [GrpObj A] (e : (Over.pullback j).obj G ≅ A)
    (he : letI : GrpObj ((Over.pullback j).obj G) := Functor.grpObjObj
      IsMonHom e.hom) :
    letI : MonObj ((Over.pullback j).obj G) := Functor.monObjObj G
    IsMonHom e.hom :=
  he

/-- **Néron-type models: commutativity and étale `[n]` derived.** `G` smooth over `Spec R`, `n` a
unit in `R`, `e` an isomorphism of group schemes from the generic fibre (along `j`) onto a
commutative group scheme, and morphisms from smooth `Spec R`-schemes into `G` determined by
their generic fibres. Then `G` is commutative and `[n]` is étale on `G`. -/
theorem etale_powHom_of_generic_injective {R : Type} [CommRing R] {S' : Scheme.{0}}
    (j : S' ⟶ Spec (CommRingCat.of R)) (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    [Smooth G.hom] (A : Over S') [GrpObj A] [IsCommMonObj A]
    (e : (Over.pullback j).obj G ≅ A)
    (he : letI : GrpObj ((Over.pullback j).obj G) := Functor.grpObjObj
      IsMonHom e.hom)
    (hN : ∀ (Y : Over (Spec (CommRingCat.of R))) [Smooth Y.hom],
      Function.Injective fun f : Y ⟶ G => (Over.pullback j).map f ≫ e.hom)
    (n : ℕ) (hn : IsUnit (n : R)) :
    ∃ _ : IsCommMonObj G, Etale (powHom G n).left := by
  letI : MonObj ((Over.pullback j).obj G) := Functor.monObjObj G
  have : IsMonHom e.hom := isMonHom_monObjObj_of_grpObjObj j G A e he
  have hc : IsCommMonObj G := isCommMonObj_of_generic_injective j G A e hN
  exact ⟨hc, etale_powHom_of_smooth_comm G n hn⟩

end Neron

end HenselDivision

#check @HenselDivision.etale_powHom_of_smooth_comm
#check @HenselDivision.torsionRestrictEquivOfSmoothComm
#check @HenselDivision.etale_powHom_of_generic_injective
#print axioms HenselDivision.etale_powHom_of_smooth_comm
#print axioms HenselDivision.torsion_restrict_bijective_of_smooth_comm
#print axioms HenselDivision.torsionRestrictEquivOfSmoothComm
#print axioms HenselDivision.torsion_integral_geom_bijective_of_smooth_comm
#print axioms HenselDivision.compatible_geom_lift_existsUnique_of_smooth_comm
#print axioms HenselDivision.isMonHom_monObjObj_of_grpObjObj
#print axioms HenselDivision.etale_powHom_of_generic_injective

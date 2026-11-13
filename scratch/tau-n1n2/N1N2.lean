import ZInQKernel.HDecomp.Faltings.H5BaseChange

/-! # tau-n1n2: the Néron leaves N1 and N2 of `scratch/h5-neron/`

* §1 copies N1 (`NeronModelExists`) and N2 (`SemistableNeronIdentityComponent`) verbatim, with the
  two definitions N2 depends on, and checks (`Iff.rfl`) that they are the declarations of the
  build (`ZInQKernel/HDecomp/Faltings/H5Neron.lean`, adopted from `scratch/h5-neron/`).
* §2 reduces N1 to its literal published form `NeronModelExistsSelf` (BLR §1.4 Thm 3 for
  `R = 𝓞_L`, `K = L`, `A_K = B` an abelian variety over `L` itself): **proved**
  (`neronModelExists_of_self`). The base change `A ↦ A_L` is absorbed by the canonical isomorphism
  `(B_L)_L ≅ B_L` (pullback along `Spec.map id`), a group isomorphism.
* §3 splits `NeronModelExistsSelf` into a **local leaf** `LocalNeronModelExists` (Néron models over
  the discrete valuation rings `O ⊂ L`, i.e. the localizations `𝓞_{L,𝔭}`; BLR §1.4 Thm 3 for a DVR)
  and **glue** `NeronLocalToGlobal` (spreading out to an abelian scheme over a dense open of
  `Spec 𝓞_L`, BLR 1.2/8 there, and gluing the finitely many local Néron models; BLR §1.4 proof
  of Thm 3, Prop 1.2/4). The reduction is **proved** (`neronModelExistsSelf_of_local`,
  `neronModelExists_of_local`).
* §4 sanity: the local leaf holds for the zero abelian variety (so the new statements are not
  vacuous in their hypotheses and the definitions are inhabited).
-/

namespace ZInQ.TauN1N2

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings
open PkgI3 (AbVar)
open ZInQ.H5Neron (jL NeronProp)
open scoped Obj

/-! ## §1. Verbatim copies (from `scratch/h5-neron/Reduction.lean`, = the build's `H5Neron`) -/

section Copies

variable {K : Type} [Field K] {A : AbVar K}

/-- (verbatim) `𝒢'` (over `𝓞_{L'}`) is the base change of `𝒢` (over `𝓞_L`) along `𝓞_L → 𝓞_{L'}`,
as a group scheme: an isomorphism of group objects `𝒢' ≅ 𝒢 ×_{𝓞_L} 𝓞_{L'}`. (The identifications
with `A_{L'}` are not compared; the height does not use them.) -/
def IsBaseChangeOf {L L' : Type} [Field L] [NumberField L] [Algebra K L] [Field L']
    [NumberField L'] [Algebra K L'] [Algebra L L'] (𝒢' : GroupModel A L') (𝒢 : GroupModel A L) :
    Prop :=
  letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L'))))).obj
    𝒢.G) := Functor.grpObjObj
  ∃ e : 𝒢'.G ≅ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L'))))).obj 𝒢.G,
    IsMonHom e.hom

/-- (verbatim) `𝒰 → 𝒢` is an open immersion of group schemes over `𝓞_L`. -/
def IsOpenSubgroupModel {L : Type} [Field L] [NumberField L] [Algebra K L]
    (𝒰 𝒢 : GroupModel A L) : Prop :=
  ∃ f : 𝒰.G ⟶ 𝒢.G, IsOpenImmersion f.left ∧ IsMonHom f

end Copies

/-- (verbatim) **Leaf N1 (Néron).** Every abelian variety over a number field `L` has a Néron
model over `𝓞_L`: a smooth separated group scheme of finite type with generic fibre `A_L` and the
Néron mapping property. BLR, *Néron Models*, §1.4 Thm 3 (UNVERIFIED locator). -/
def NeronModelExists : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L],
    ∃ 𝒩 : GroupModel A L, 𝒩.IsNeronModel

/-- (verbatim) **Leaf N2 (semistable reduction and base change of the identity component).** For
`A` over a number field `K` there are a finite extension `L₀/K` and a Néron model `𝒩₀` over
`𝓞_{L₀}` such that for every finite extension `L'/L₀` and every Néron model `𝒩'` over `𝓞_{L'}`,
there is a group model `𝒰` (the identity component `𝒩'⁰`) that is an open subgroup both of `𝒩'`
and of a base change `𝒱` of `𝒩₀` (namely `𝒱 = 𝒩₀ ×_{𝓞_{L₀}} 𝓞_{L'}`, with
`𝒰 = 𝒩₀⁰ ×_{𝓞_{L₀}} 𝓞_{L'}`). Consequence of SGA 7 IX Thm 3.6 (Grothendieck's semistable
reduction theorem: `A_{L₀}` is semistable for some finite `L₀`) and SGA 7 IX Prop./Cor. 3.3 (in
the semistable case `(𝒩_{L'})⁰ = (𝒩⁰)_{L'}`), with the openness of the identity component
(SGA 3 VI_B 3.10) and the compatibility of Néron models with localization (BLR §1.2); all
locators UNVERIFIED. -/
def SemistableNeronIdentityComponent : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : AbVar K),
    ∃ (L₀ : Type) (_ : Field L₀) (_ : NumberField L₀) (_ : Algebra K L₀) (𝒩₀ : GroupModel A L₀),
      𝒩₀.IsNeronModel ∧
      ∀ (L' : Type) [Field L'] [NumberField L'] [Algebra K L'] [Algebra L₀ L']
        [IsScalarTower K L₀ L'] (𝒩' : GroupModel A L'), 𝒩'.IsNeronModel →
        ∃ 𝒰 𝒱 : GroupModel A L', IsBaseChangeOf 𝒱 𝒩₀ ∧ IsOpenSubgroupModel 𝒰 𝒩' ∧
          IsOpenSubgroupModel 𝒰 𝒱

theorem neronModelExists_iff : NeronModelExists ↔ ZInQ.H5Neron.NeronModelExists := Iff.rfl

theorem semistableNeronIdentityComponent_iff :
    SemistableNeronIdentityComponent ↔ ZInQ.H5Neron.SemistableNeronIdentityComponent := Iff.rfl

/-! ## §2. Néron models over a base ring; N1 from its literal published form -/

/-- A **Néron model of `B` over a base ring `R → L`** (`R` a subring of `L` with fraction field
`L` in the uses below): a smooth, separated, quasi-compact group scheme over `Spec R` with a group
isomorphism of its generic fibre with `B`, and the Néron mapping property for all smooth
`R`-schemes (BLR §1.2 Def. 1). For `R = 𝓞_L` and `B = A_L` the fields are literally those of
`GroupModel A L` and `GroupModel.IsNeronModel` (`NeronModelOver.toGroupModel`). -/
structure NeronModelOver (R : Type) [CommRing R] (L : Type) [Field L] [Algebra R L]
    (B : AbVar L) where
  /-- the model -/
  G : Over (Spec (CommRingCat.of R))
  [grp : GrpObj G]
  [smooth : Smooth G.hom]
  [separated : IsSeparated G.hom]
  [qc : QuasiCompact G.hom]
  /-- the identification of the generic fibre with `B` -/
  gen : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj G ≅ B.X
  /-- ... as group schemes -/
  gen_hom : letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj G) :=
    Functor.grpObjObj
    IsMonHom gen.hom
  /-- the Néron mapping property -/
  neron : ∀ (Y : Over (Spec (CommRingCat.of R))) [Smooth Y.hom],
    Function.Bijective fun f : Y ⟶ G =>
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).map f ≫ gen.hom

attribute [instance] NeronModelOver.grp NeronModelOver.smooth NeronModelOver.separated
  NeronModelOver.qc

/-- **Leaf N1-self (BLR §1.4 Thm 3, literal form for `R = 𝓞_L`).** Every abelian variety `B` over
a number field `L` has a Néron model over `𝓞_L`. Bosch–Lütkebohmert–Raynaud, *Néron Models*,
§1.4 Thm 3 ("an abelian variety over the field of fractions of a Dedekind domain `R` has a Néron
model over `R`"), UNVERIFIED locator; the group structure of the Néron model is the one induced
by the mapping property (BLR §1.2), and "finite type" gives `QuasiCompact`. -/
def NeronModelExistsSelf : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (B : AbVar L), Nonempty (NeronModelOver (𝓞 L) L B)

/-- A Néron model of `A_L` over `𝓞_L` (as `NeronModelOver`) is a Néron `GroupModel` of `A` over
`L`: the fields coincide (`genericFibre L G` is by definition the pullback along `𝓞_L → L`). -/
noncomputable def NeronModelOver.toGroupModel {K : Type} [Field K] {A : AbVar K} {L : Type}
    [Field L] [NumberField L] [Algebra K L] (𝒩 : NeronModelOver (𝓞 L) L (A.baseChange L)) :
    GroupModel A L where
  G := 𝒩.G
  gen := 𝒩.gen
  gen_hom := 𝒩.gen_hom

theorem NeronModelOver.toGroupModel_isNeronModel {K : Type} [Field K] {A : AbVar K} {L : Type}
    [Field L] [NumberField L] [Algebra K L] (𝒩 : NeronModelOver (𝓞 L) L (A.baseChange L)) :
    𝒩.toGroupModel.IsNeronModel :=
  fun Y _ => 𝒩.neron Y

/-- **N1 from N1-self (proved):** apply the literal published statement to `B = A_L`. -/
theorem neronModelExists_of_self (h : NeronModelExistsSelf) : NeronModelExists := by
  intro K _ A L _ _ _
  obtain ⟨𝒩⟩ := h L (A.baseChange L)
  exact ⟨𝒩.toGroupModel, 𝒩.toGroupModel_isNeronModel⟩

/-! ## §3. N1-self from a local leaf and a local-to-global glue statement -/

/-- **Leaf N1-loc (Néron models over a discrete valuation ring).** For an abelian variety `B` over
a number field `L` and a discrete valuation ring `O ⊂ L` with fraction field `L` (a valuation
subring that is a DVR; these are the localizations `𝓞_{L,𝔭}` at the nonzero primes), `B` has a
Néron model over `O`. BLR, *Néron Models*, §1.4 Thm 3 for the Dedekind domain `R = O` (in BLR the
local case is §1.3 Cor. 2 (strictly henselian `R`) with étale descent §6.2; UNVERIFIED locators).
A special case of the published theorem (only number fields, only DVRs). -/
def LocalNeronModelExists : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (O : ValuationSubring L) [IsDiscreteValuationRing O]
    (B : AbVar L), Nonempty (NeronModelOver O L B)

/-- **Glue N1-glue (local to global).** If an abelian variety `B` over a number field `L` has a
Néron model over every discrete valuation ring `O ⊂ L`, it has one over `𝓞_L`. Proof (STANDARD,
not in Mathlib): `B` spreads out to an abelian scheme `𝒜` over a dense open `U ⊂ Spec 𝓞_L` (EGA IV
§8, limits of schemes and of properties of morphisms; UNVERIFIED locators), which is the Néron
model over `U` (BLR §1.2 Prop. 8); each of the finitely many local Néron models at the closed
points outside `U` is of finite type, so spreads out to a neighbourhood where it agrees with `𝒜`
(Néron mapping property); gluing gives a smooth separated group scheme of finite type over
`𝓞_L`, and the Néron property is local on the Dedekind base (BLR §1.2 Prop. 4) (BLR §1.4, proof
of Thm 3; UNVERIFIED locators). Glue: algebraic geometry to be formalized by the project. -/
def NeronLocalToGlobal : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (B : AbVar L),
    (∀ (O : ValuationSubring L) [IsDiscreteValuationRing O], Nonempty (NeronModelOver O L B)) →
      Nonempty (NeronModelOver (𝓞 L) L B)

/-- **N1-self from the local leaf and the glue (proved).** -/
theorem neronModelExistsSelf_of_local (hloc : LocalNeronModelExists) (hglue : NeronLocalToGlobal) :
    NeronModelExistsSelf :=
  fun L _ _ B => hglue L B (fun O _ => hloc L O B)

/-- **N1 from the local leaf and the glue (proved).** -/
theorem neronModelExists_of_local (hloc : LocalNeronModelExists) (hglue : NeronLocalToGlobal) :
    NeronModelExists :=
  neronModelExists_of_self (neronModelExistsSelf_of_local hloc hglue)

/-! ## §4. Sanity: the zero abelian variety -/

/-- The trivial Néron model `Spec R` of the zero abelian variety `Spec L`, over any `R → L`. -/
noncomputable def trivNeronOver (R : Type) [CommRing R] (L : Type) [Field L] [Algebra R L] :
    NeronModelOver R L (AbVar.zero L) where
  G := 𝟙_ _
  smooth := by dsimp; infer_instance
  separated := by dsimp; infer_instance
  qc := by dsimp; infer_instance
  gen := (Functor.Monoidal.εIso (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L))))).symm
  gen_hom := by
    letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj
      (𝟙_ (Over (Spec (CommRingCat.of R))))) := Functor.grpObjObj
    exact ⟨ZInQ.H5Neron.hom_ext_of_iso_unit (Iso.refl _) _ _,
      ZInQ.H5Neron.hom_ext_of_iso_unit (Iso.refl _) _ _⟩
  neron Y _ := ⟨fun f g _ => toUnit_unique _ _,
    fun g => ⟨toUnit Y, ZInQ.H5Neron.hom_ext_of_iso_unit (Iso.refl _) _ _⟩⟩

/-- The local leaf holds for the zero abelian variety. -/
theorem localNeronModelExists_zero (L : Type) [Field L] [NumberField L] (O : ValuationSubring L)
    [IsDiscreteValuationRing O] : Nonempty (NeronModelOver O L (AbVar.zero L)) :=
  ⟨trivNeronOver O L⟩

/-- The glue holds for the zero abelian variety (its conclusion does). -/
theorem neronLocalToGlobal_zero (L : Type) [Field L] [NumberField L] :
    Nonempty (NeronModelOver (𝓞 L) L (AbVar.zero L)) :=
  ⟨trivNeronOver (𝓞 L) L⟩

end ZInQ.TauN1N2

#print axioms ZInQ.TauN1N2.neronModelExists_iff
#print axioms ZInQ.TauN1N2.semistableNeronIdentityComponent_iff
#print axioms ZInQ.TauN1N2.neronModelExists_of_self
#print axioms ZInQ.TauN1N2.neronModelExistsSelf_of_local
#print axioms ZInQ.TauN1N2.neronModelExists_of_local
#print axioms ZInQ.TauN1N2.localNeronModelExists_zero
#print axioms ZInQ.TauN1N2.neronLocalToGlobal_zero

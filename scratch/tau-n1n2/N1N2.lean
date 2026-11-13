import ZInQKernel.HDecomp.Faltings.H5BaseChange

/-! # tau-n1n2: the Néron leaves N1 and N2 of `scratch/h5-neron/`

* §1 copies N1 (`NeronModelExists`) and N2 (`SemistableNeronIdentityComponent`) verbatim, with the
  two definitions N2 depends on, and checks (`Iff.rfl`) that they are the declarations of the
  build (`ZInQKernel/HDecomp/Faltings/H5Neron.lean`, adopted from `scratch/h5-neron/`).
* §2 defines `NeronModelOver R L B` (a Néron model of `B : AbVar L` over a ring `R → L`, BLR §1.2
  Def. 1) and proves N1 equivalent to its literal published form `NeronModelExistsSelf` (BLR §1.4
  Thm 3 for `R = 𝓞_L` and an abelian variety over `L` itself): `neronModelExistsSelf_iff`.
* §3 splits `NeronModelExistsSelf` into two **leaves**, `LocalNeronModelExists` (Néron models over
  the discrete valuation rings `O ⊂ L`, i.e. the `𝓞_{L,𝔭}`; BLR §1.4 Thm 3 for a DVR) and
  `AbelianSchemeIsNeron` (BLR §1.2 Prop. 8), and one **glue** statement `NeronLocalToGlobal`
  (spreading out and gluing; BLR §1.4, proof of Thm 3). The reduction is **proved**
  (`neronModelExistsSelf_of_local`, `neronModelExists_of_local`).
* §4 sanity: the local leaf's conclusion holds for the zero abelian variety.
* §5 N2 needs only **one** Néron model over each `L'` (`semistableNeronIdentityComponent_of_some`),
  via `isMonHom_of_neron` (an isomorphism of Néron models compatible with `gen` is a group
  isomorphism).
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

/-! ### The converse: N1 implies N1-self (so the two are equivalent) -/

theorem spec_algebraMap_self (L : Type) [Field L] :
    Spec.map (CommRingCat.ofHom (algebraMap L L)) = 𝟙 _ := by
  rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]

/-- The components of `Over.pullbackId` are monoid morphisms. -/
theorem isMonHom_pullbackId {S : Scheme.{0}} (G : Over S) [MonObj G] :
    IsMonHom ((Over.pullbackId (X := S)).hom.app G) := by
  have h := ((Functor.mapMonNatIso (Over.pullbackId (X := S))).hom.app (Mon.mk G) ≫
    (Functor.mapMonIdIso).hom.app (Mon.mk G)).isMonHom_hom
  have e : (Over.pullbackId (X := S)).hom.app G = (Over.pullbackId (X := S)).hom.app G ≫ 𝟙 _ :=
    (Category.comp_id _).symm
  rw [e]
  exact h

/-- `X ×_L L ≅ X` (pullback along `Spec.map (algebraMap L L) = 𝟙`). An `irreducible_def`: if the
kernel may unfold it (through `eqToIso`), checking `selfGen` below times out. -/
noncomputable irreducible_def selfIso {L : Type} [Field L] (X : Over (Spec (CommRingCat.of L))) :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap L L)))).obj X ≅ X :=
  ZInQ.H5Neron.pbEqIso (spec_algebraMap_self L) X ≪≫ (Over.pullbackId).app X

theorem isMonHom_selfIso {L : Type} [Field L] (X : Over (Spec (CommRingCat.of L))) [MonObj X] :
    IsMonHom (selfIso X).hom := by
  have h1 := ZInQ.H5Neron.isMonHom_pbEq (spec_algebraMap_self L) X
  have h2 := isMonHom_pullbackId X
  rw [selfIso_def]
  show IsMonHom (ZInQ.H5Neron.pbEq (spec_algebraMap_self L) X ≫ (Over.pullbackId).hom.app X)
  infer_instance

/-- The generic-fibre identification of a group model of `B_L` (`B` over `L`), followed by
`B_L ≅ B`. Built from `H5Neron.genIso` so that all types are syntactic. -/
noncomputable def selfGen {L : Type} [Field L] [NumberField L] {B : AbVar L}
    (𝒩 : GroupModel B L) :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L)))).obj 𝒩.G ≅ B.X :=
  ZInQ.H5Neron.genIso 𝒩 ≪≫ selfIso B.X

/-- (Stated through `Iso.trans_hom`: a bare `rfl` here makes the kernel time out.) -/
theorem selfGen_hom {L : Type} [Field L] [NumberField L] {B : AbVar L} (𝒩 : GroupModel B L) :
    (selfGen 𝒩).hom = (ZInQ.H5Neron.genIso 𝒩).hom ≫ (selfIso B.X).hom :=
  Iso.trans_hom _ _

theorem selfGen_isMonHom {L : Type} [Field L] [NumberField L] {B : AbVar L}
    (𝒩 : GroupModel B L) :
    letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L)))).obj 𝒩.G) :=
      Functor.grpObjObj
    IsMonHom (selfGen 𝒩).hom := by
  have h1 : IsMonHom (ZInQ.H5Neron.genIso 𝒩).hom := ZInQ.H5Neron.genIso_isMonHom 𝒩
  have h2 : IsMonHom (selfIso B.X).hom := isMonHom_selfIso B.X
  rw [selfGen_hom]
  exact instIsMonHomComp (ZInQ.H5Neron.genIso 𝒩).hom (selfIso B.X).hom

theorem genIso_neron {L : Type} [Field L] [NumberField L] {B : AbVar L} (𝒩 : GroupModel B L)
    (h : 𝒩.IsNeronModel) : NeronProp (jL L) (fun Y => Smooth Y.hom) 𝒩.G
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap L L)))).obj B.X)
      (ZInQ.H5Neron.genIso 𝒩) := fun Y hY => @h Y hY

theorem selfGen_neron {L : Type} [Field L] [NumberField L] {B : AbVar L} (𝒩 : GroupModel B L)
    (h : 𝒩.IsNeronModel) : NeronProp (jL L) (fun Y => Smooth Y.hom) 𝒩.G B.X (selfGen 𝒩) := by
  refine (genIso_neron 𝒩 h).of_iso (Iso.refl _) (selfIso B.X) (selfGen 𝒩) ?_
  rw [Iso.refl_hom, (Over.pullback (jL L)).map_id, Category.id_comp, selfGen_hom]

/-- **N1 implies N1-self (proved)**, so `NeronModelExistsSelf ↔ NeronModelExists`. -/
theorem neronModelExistsSelf_of (h : NeronModelExists) : NeronModelExistsSelf := by
  intro L _ _ B
  obtain ⟨𝒩, h𝒩⟩ := h L B L
  exact ⟨⟨𝒩.G, selfGen 𝒩, selfGen_isMonHom 𝒩, fun Y hY => selfGen_neron 𝒩 h𝒩 Y hY⟩⟩

theorem neronModelExistsSelf_iff : NeronModelExistsSelf ↔ NeronModelExists :=
  ⟨neronModelExists_of_self, neronModelExistsSelf_of⟩

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

/-- **Leaf N1-ab (an abelian scheme is the Néron model of its generic fibre).** Let `R` be a
Dedekind domain with fraction field a number field `L` (e.g. `𝓞_L[1/f]`), and `𝒜` a smooth proper
group scheme over `R` (an abelian scheme) whose generic fibre is identified, as a group scheme,
with `B`. Then `𝒜` has the Néron mapping property. BLR, *Néron Models*, §1.2 Prop. 8 (stated
there for a discrete valuation ring; the Dedekind case follows by the locality of the mapping
property, BLR §1.2; UNVERIFIED locators). `TextbookLeaves.t3` (`NeronMappingAbelianScheme`) is the
special case where the test scheme `Y` is itself an abelian scheme over a DVR, which is not enough
here. -/
def AbelianSchemeIsNeron : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (R : Type) [CommRing R] [IsDomain R] [IsDedekindDomain R]
    [Algebra R L] [IsFractionRing R L] (B : AbVar L) (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G] [Smooth G.hom] [IsProper G.hom]
    (gen : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj G ≅ B.X),
    (letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj G) :=
      Functor.grpObjObj
     IsMonHom gen.hom) →
    ∀ (Y : Over (Spec (CommRingCat.of R))) [Smooth Y.hom],
      Function.Bijective fun f : Y ⟶ G =>
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).map f ≫ gen.hom

/-- **Glue N1-glue (local to global).** Given leaf N1-ab: if an abelian variety `B` over a number
field `L` has a Néron model over every discrete valuation ring `O ⊂ L`, it has one over `𝓞_L`.
Proof (STANDARD, not in Mathlib): `B` spreads out to an abelian scheme `𝒜` over a dense open
`U = Spec 𝓞_L[1/f]` (EGA IV §8: limits of schemes, of morphisms and of the properties smooth,
proper, group law; UNVERIFIED locators), which is the Néron model over `U` by N1-ab; each of the
finitely many local Néron models at the closed points outside `U` is of finite type, so spreads
out to a neighbourhood, where (after shrinking) it agrees with `𝒜` because the isomorphism of
generic fibres spreads out (EGA IV 8.8.2); the group law is induced by the Néron property; gluing
gives a smooth
separated group scheme of finite type over `𝓞_L`, and the Néron property is local on the
Dedekind base (BLR §1.2) (this is BLR §1.4, proof of Thm 3; UNVERIFIED locators). Glue: algebraic
geometry (spreading out, gluing) to be formalized by the project. -/
def NeronLocalToGlobal : Prop :=
  AbelianSchemeIsNeron →
  ∀ (L : Type) [Field L] [NumberField L] (B : AbVar L),
    (∀ (O : ValuationSubring L) [IsDiscreteValuationRing O], Nonempty (NeronModelOver O L B)) →
      Nonempty (NeronModelOver (𝓞 L) L B)

/-- **N1-self from the local leaf and the glue (proved).** -/
theorem neronModelExistsSelf_of_local (hloc : LocalNeronModelExists) (hab : AbelianSchemeIsNeron)
    (hglue : NeronLocalToGlobal) : NeronModelExistsSelf :=
  fun L _ _ B => hglue hab L B (fun O _ => hloc L O B)

/-- **N1 from the local leaf and the glue (proved).** -/
theorem neronModelExists_of_local (hloc : LocalNeronModelExists) (hab : AbelianSchemeIsNeron)
    (hglue : NeronLocalToGlobal) : NeronModelExists :=
  neronModelExists_of_self (neronModelExistsSelf_of_local hloc hab hglue)

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

/-! ## §5. N2 needs only one Néron model over each `L'`

By uniqueness of Néron models (`NeronProp.uniqueIso`), and because an isomorphism of Néron models
compatible with the identifications of the generic fibres is a group isomorphism
(`isMonHom_of_reflect`), the clause "for every Néron model `𝒩'` over `𝓞_{L'}`" of N2 may be
replaced by "for some Néron model `𝒩'` over `𝓞_{L'}`" (`SemistableNeronIdentityComponentSome`). -/

section Reflect

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
  (F : C ⥤ D) [F.Monoidal]

/-- A morphism `φ : M → N` of monoid objects is a monoid morphism if, after a monoidal functor
`F`, it is compatible with monoid morphisms `g_M : F M → A`, `g_N : F N → A`
(`F φ ≫ g_N = g_M`) and maps `T → N` (`T = 𝟙`, `T = M ⊗ M`) are determined by `F (-) ≫ g_N`. -/
theorem isMonHom_of_reflect {M N : C} [MonObj M] [MonObj N] {A : D} [MonObj A]
    (φ : M ⟶ N) (gM : F.obj M ⟶ A) (gN : F.obj N ⟶ A) [IsMonHom gM] [IsMonHom gN]
    (hφ : F.map φ ≫ gN = gM)
    (inj1 : ∀ a b : 𝟙_ C ⟶ N, F.map a ≫ gN = F.map b ≫ gN → a = b)
    (inj2 : ∀ a b : M ⊗ M ⟶ N, F.map a ≫ gN = F.map b ≫ gN → a = b) : IsMonHom φ := by
  constructor
  · apply inj1
    rw [F.map_comp, Category.assoc, hφ]
    have h1 : Functor.LaxMonoidal.ε F ≫ F.map η[M] ≫ gM = η[A] := by
      rw [← Category.assoc]; exact IsMonHom.one_hom gM
    have h2 : Functor.LaxMonoidal.ε F ≫ F.map η[N] ≫ gN = η[A] := by
      rw [← Category.assoc]; exact IsMonHom.one_hom gN
    exact (cancel_epi (Functor.LaxMonoidal.ε F)).mp (h1.trans h2.symm)
  · apply inj2
    rw [F.map_comp, Category.assoc, hφ, F.map_comp, Category.assoc]
    have h1 : Functor.LaxMonoidal.μ F M M ≫ F.map μ[M] ≫ gM = (gM ⊗ₘ gM) ≫ μ[A] := by
      rw [← Category.assoc]; exact IsMonHom.mul_hom gM
    have h2 : Functor.LaxMonoidal.μ F N N ≫ F.map μ[N] ≫ gN = (gN ⊗ₘ gN) ≫ μ[A] := by
      rw [← Category.assoc]; exact IsMonHom.mul_hom gN
    apply (cancel_epi (Functor.LaxMonoidal.μ F M M)).mp
    rw [h1, ← Category.assoc, ← Functor.LaxMonoidal.μ_natural, Category.assoc, h2,
      ← Category.assoc, tensorHom_comp_tensorHom, hφ]

end Reflect

section NeronIso

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- An isomorphism of Néron group models compatible with `gen` is a monoid morphism. -/
theorem isMonHom_of_neron {𝒩 𝒩' : GroupModel A L} (h' : 𝒩'.IsNeronModel) (φ : 𝒩.G ⟶ 𝒩'.G)
    (hφ : (Over.pullback (jL L)).map φ ≫ 𝒩'.gen.hom = 𝒩.gen.hom) : IsMonHom φ := by
  let F := Over.pullback (jL L)
  let g : F.obj 𝒩.G ⟶ (A.baseChange L).X := 𝒩.gen.hom
  let g' : F.obj 𝒩'.G ⟶ (A.baseChange L).X := 𝒩'.gen.hom
  have hg : IsMonHom g := 𝒩.gen_hom
  have hg' : IsMonHom g' := 𝒩'.gen_hom
  haveI : Smooth (𝟙_ (Over (Spec (CommRingCat.of (𝓞 L))))).hom := by dsimp; infer_instance
  haveI : Smooth (𝒩.G ⊗ 𝒩.G).hom := by
    show Smooth (pullback.fst 𝒩.G.hom 𝒩.G.hom ≫ 𝒩.G.hom); infer_instance
  exact isMonHom_of_reflect F φ g g' hφ (fun a b hab => (h' _).1 hab) (fun a b hab => (h' _).1 hab)

/-- Open subgroups transport along a compatible isomorphism of Néron models. -/
theorem isOpenSubgroupModel_of_neron {𝒰 𝒩 𝒩' : GroupModel A L} (h : 𝒩.IsNeronModel)
    (h' : 𝒩'.IsNeronModel) (hU : IsOpenSubgroupModel 𝒰 𝒩) : IsOpenSubgroupModel 𝒰 𝒩' := by
  obtain ⟨φ, hφ⟩ := ZInQ.H5Neron.GroupModel.IsNeronModel.uniqueIso h h'
  obtain ⟨f, hf1, hf2⟩ := hU
  have hφm : IsMonHom φ.hom := isMonHom_of_neron h' φ.hom hφ
  refine ⟨f ≫ φ.hom, ?_, inferInstance⟩
  rw [Over.comp_left]
  haveI : IsIso φ.hom.left := inferInstance
  infer_instance

end NeronIso

/-- **N2 with one Néron model over each `L'`** (same leaf content as N2: SGA 7 IX 3.6 and 3.3). -/
def SemistableNeronIdentityComponentSome : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : AbVar K),
    ∃ (L₀ : Type) (_ : Field L₀) (_ : NumberField L₀) (_ : Algebra K L₀) (𝒩₀ : GroupModel A L₀),
      𝒩₀.IsNeronModel ∧
      ∀ (L' : Type) [Field L'] [NumberField L'] [Algebra K L'] [Algebra L₀ L']
        [IsScalarTower K L₀ L'], ∃ 𝒩' : GroupModel A L', 𝒩'.IsNeronModel ∧
        ∃ 𝒰 𝒱 : GroupModel A L', IsBaseChangeOf 𝒱 𝒩₀ ∧ IsOpenSubgroupModel 𝒰 𝒩' ∧
          IsOpenSubgroupModel 𝒰 𝒱

/-- **N2 from its "some Néron model" form (proved).** -/
theorem semistableNeronIdentityComponent_of_some (h : SemistableNeronIdentityComponentSome) :
    SemistableNeronIdentityComponent := by
  intro K _ _ A
  obtain ⟨L₀, i1, i2, i3, 𝒩₀, h𝒩₀, hL⟩ := h K A
  refine ⟨L₀, i1, i2, i3, 𝒩₀, h𝒩₀, ?_⟩
  intro L' _ _ _ _ _ 𝒩'' h𝒩''
  obtain ⟨𝒩', h𝒩', 𝒰, 𝒱, hV, hU𝒩, hU𝒱⟩ := hL L'
  exact ⟨𝒰, 𝒱, hV, isOpenSubgroupModel_of_neron h𝒩' h𝒩'' hU𝒩, hU𝒱⟩

/-- Conversely N2 with N1 gives the "some" form (so the two are equivalent given N1). -/
theorem some_of_semistableNeronIdentityComponent (hN1 : NeronModelExists)
    (h : SemistableNeronIdentityComponent) : SemistableNeronIdentityComponentSome := by
  intro K _ _ A
  obtain ⟨L₀, i1, i2, i3, 𝒩₀, h𝒩₀, hL⟩ := h K A
  refine ⟨L₀, i1, i2, i3, 𝒩₀, h𝒩₀, ?_⟩
  intro L' _ _ _ _ _
  obtain ⟨𝒩', h𝒩'⟩ := hN1 K A L'
  exact ⟨𝒩', h𝒩', hL L' 𝒩' h𝒩'⟩

/-! ## §6. N2 split into a local leaf (SGA 7 IX 3.6 + 3.3 over DVRs) and glue

The local leaf is stated canonically: the open immersions `i : U → 𝒩'` and `j : U → 𝒱` agree on
the generic fibre after the natural maps to `𝒩₀` (`ιU ≫ j ≫ p = (i_{L'}) ≫ gen' ≫ π ≫ gen₀⁻¹ ≫ ι₀`).
Without this compatibility, local data at different primes could not be glued by glue alone. -/

/-- The ring map `O → w` for a valuation subring `w` of `L` lying over `O` (copied from
`HDecomp`'s `toW`). -/
def resHom {K L : Type} [Field K] [Field L] [Algebra K L] (O : ValuationSubring K)
    (w : ValuationSubring L) (hw : w.comap (algebraMap K L) = O) : O →+* w :=
  ((algebraMap K L).comp O.subtype).codRestrict w.toSubring (fun x => by
    have : (x : K) ∈ w.comap (algebraMap K L) := by rw [hw]; exact x.2
    exact this)

/-- The base-change projection `A_{L'} → A_{L₀}` of schemes, for `K ⊆ L₀ ⊆ L'`. -/
noncomputable def bcProj {K : Type} [Field K] (A : AbVar K) (L₀ L' : Type) [Field L₀] [Field L']
    [Algebra K L₀] [Algebra K L'] [Algebra L₀ L'] [IsScalarTower K L₀ L'] :
    (A.baseChange L').X.left ⟶ (A.baseChange L₀).X.left :=
  pullback.map A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap K L'))) A.X.hom
    (Spec.map (CommRingCat.ofHom (algebraMap K L₀))) (𝟙 _)
    (Spec.map (CommRingCat.ofHom (algebraMap L₀ L'))) (𝟙 _) (by simp) (by
      rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← IsScalarTower.algebraMap_eq])

/-- **The local semistability statement at a DVR `O ⊂ K`** (the conclusion of leaf N2-loc): there
is a finite extension `L₀/K` such that for every DVR `O₀ ⊂ L₀` over `O`, every Néron model `𝒩₀`
of `A_{L₀}` over `O₀`, every finite extension `L'/L₀`, every DVR `O' ⊂ L'` over `O₀` and every
Néron model `𝒩'` of `A_{L'}` over `O'`, some group scheme `U` over `O'` (the identity component
`𝒩'⁰`) is an open subgroup of `𝒩'` and of `𝒱 = 𝒩₀ ×_{O₀} O'`, the two embeddings agreeing on the
generic fibre after the natural maps to `𝒩₀`. -/
def LocalSemistableAt {K : Type} [Field K] (A : AbVar K) (O : ValuationSubring K) : Prop :=
  ∃ (L₀ : Type) (_ : Field L₀) (_ : NumberField L₀) (_ : Algebra K L₀),
    ∀ (O₀ : ValuationSubring L₀) [IsDiscreteValuationRing O₀], O₀.comap (algebraMap K L₀) = O →
    ∀ (𝒩₀ : NeronModelOver O₀ L₀ (A.baseChange L₀)) (L' : Type) [Field L'] [NumberField L']
      [Algebra K L'] [Algebra L₀ L'] [IsScalarTower K L₀ L'] (O' : ValuationSubring L')
      [IsDiscreteValuationRing O'] (hO' : O'.comap (algebraMap L₀ L') = O₀)
      (𝒩' : NeronModelOver O' L' (A.baseChange L')),
      letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (resHom O₀ O' hO')))).obj 𝒩₀.G) :=
        Functor.grpObjObj
      ∃ (U : Over (Spec (CommRingCat.of O'))) (_ : GrpObj U) (i : U ⟶ 𝒩'.G)
        (j : U ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom (resHom O₀ O' hO')))).obj 𝒩₀.G),
        IsOpenImmersion i.left ∧ IsMonHom i ∧ IsOpenImmersion j.left ∧ IsMonHom j ∧
        pullback.fst U.hom (Spec.map (CommRingCat.ofHom (algebraMap O' L'))) ≫ j.left ≫
            pullback.fst 𝒩₀.G.hom (Spec.map (CommRingCat.ofHom (resHom O₀ O' hO'))) =
          ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O' L')))).map i).left ≫
            𝒩'.gen.hom.left ≫ bcProj A L₀ L' ≫ 𝒩₀.gen.inv.left ≫
            pullback.fst 𝒩₀.G.hom (Spec.map (CommRingCat.ofHom (algebraMap O₀ L₀)))

/-- **Leaf N2-loc (semistable reduction and the identity component, local form).** For an
abelian variety `A` over a number field `K` and every DVR `O ⊂ K`, `LocalSemistableAt A O`.
Consequence of SGA 7 I, Exp. IX, Thm 3.6 (Grothendieck: `A` acquires semistable reduction at all
places over `O` after a finite extension `L₀`; e.g. `L₀ = K(A[m])`, `m ≥ 3` prime to the residue
characteristic, by Exp. IX Prop. 4.7) and Exp. IX Prop./Cor. 3.3 (for semistable reduction the
canonical morphism `(𝒩₀⁰)_{O'} → 𝒩'⁰` is an isomorphism, for any extension of DVRs), with the
openness of the identity component of a smooth group scheme (SGA 3 VI_B 3.10). All locators
UNVERIFIED. -/
def LocalSemistableIdentityComponent : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : AbVar K) (O : ValuationSubring K)
    [IsDiscreteValuationRing O], LocalSemistableAt A O

/-- N2's conclusion for one abelian variety (the body of `SemistableNeronIdentityComponent`). -/
def SemistableNeronAt (K : Type) [Field K] [NumberField K] (A : AbVar K) : Prop :=
  ∃ (L₀ : Type) (_ : Field L₀) (_ : NumberField L₀) (_ : Algebra K L₀) (𝒩₀ : GroupModel A L₀),
    𝒩₀.IsNeronModel ∧
    ∀ (L' : Type) [Field L'] [NumberField L'] [Algebra K L'] [Algebra L₀ L']
      [IsScalarTower K L₀ L'] (𝒩' : GroupModel A L'), 𝒩'.IsNeronModel →
      ∃ 𝒰 𝒱 : GroupModel A L', IsBaseChangeOf 𝒱 𝒩₀ ∧ IsOpenSubgroupModel 𝒰 𝒩' ∧
        IsOpenSubgroupModel 𝒰 𝒱

/-- **Glue N2-glue (local to global).** Given N1 and N1-ab: if `LocalSemistableAt A O` holds at
every DVR `O ⊂ K`, then N2's conclusion holds for `A`. Proof (STANDARD, not in Mathlib): `A`
has good reduction outside a finite set `S` of places (spreading out to an abelian scheme over a
dense open, EGA IV §8; UNVERIFIED); outside `S` the Néron model is that abelian scheme (N1-ab),
which commutes with base change, so no extension is needed there; take for `L₀` the compositum
(`H5Neron.compositum`) of the local fields `L₀(𝔭)`, `𝔭 ∈ S`; the local open immersions are
compatible on generic fibres, hence (schematic density of the generic fibre of the flat `U`,
separatedness of the targets) they are restrictions of the canonical morphism
`𝒩₀ ×_{𝓞_{L₀}} 𝓞_{L'} → 𝒩'` and glue to the identity component `𝒩'⁰` over `𝓞_{L'}` (open by
SGA 3 VI_B 3.10, quasi-compact over the noetherian base); the passage from `L₀(𝔭)` to the
compositum `L₀` applies the local statement's "every `L'`" clause twice (to `L₀` and to `L'`) and
composes, using that the identity component of an algebraic group is geometrically connected
(SGA 3 VI_A 2.4, EGA IV 4.5.13); Néron models are compatible with localization (BLR §1.2), and a
morphism that is an isomorphism over every local ring of the base is an isomorphism. Locators
UNVERIFIED.
Glue: algebraic geometry to be formalized by the project. -/
def SemistableLocalToGlobal : Prop :=
  NeronModelExists → AbelianSchemeIsNeron →
  ∀ (K : Type) [Field K] [NumberField K] (A : AbVar K),
    (∀ (O : ValuationSubring K) [IsDiscreteValuationRing O], LocalSemistableAt A O) →
      SemistableNeronAt K A

/-- **N2 from the local leaf N2-loc, the leaves N1 and N1-ab, and the glue (proved).** -/
theorem semistableNeronIdentityComponent_of_local (hN1 : NeronModelExists)
    (hab : AbelianSchemeIsNeron) (hloc : LocalSemistableIdentityComponent)
    (hglue : SemistableLocalToGlobal) : SemistableNeronIdentityComponent :=
  fun K _ _ A => hglue hN1 hab K A (fun O _ => hloc K A O)

/-- **N1 and N2 from the three leaves N1-loc, N1-ab, N2-loc and the two glue statements
(proved).** -/
theorem n1_n2_of_leaves (hloc1 : LocalNeronModelExists) (hab : AbelianSchemeIsNeron)
    (hloc2 : LocalSemistableIdentityComponent) (hg1 : NeronLocalToGlobal)
    (hg2 : SemistableLocalToGlobal) :
    NeronModelExists ∧ SemistableNeronIdentityComponent :=
  ⟨neronModelExists_of_local hloc1 hab hg1,
    semistableNeronIdentityComponent_of_local (neronModelExists_of_local hloc1 hab hg1) hab hloc2
      hg2⟩

end ZInQ.TauN1N2

#print axioms ZInQ.TauN1N2.neronModelExists_iff
#print axioms ZInQ.TauN1N2.semistableNeronIdentityComponent_iff
#print axioms ZInQ.TauN1N2.neronModelExists_of_self
#print axioms ZInQ.TauN1N2.neronModelExistsSelf_of_local
#print axioms ZInQ.TauN1N2.neronModelExists_of_local
#print axioms ZInQ.TauN1N2.localNeronModelExists_zero
#print axioms ZInQ.TauN1N2.neronLocalToGlobal_zero
#print axioms ZInQ.TauN1N2.isMonHom_of_reflect
#print axioms ZInQ.TauN1N2.isMonHom_of_neron
#print axioms ZInQ.TauN1N2.semistableNeronIdentityComponent_of_some
#print axioms ZInQ.TauN1N2.some_of_semistableNeronIdentityComponent
#print axioms ZInQ.TauN1N2.semistableNeronIdentityComponent_of_local
#print axioms ZInQ.TauN1N2.n1_n2_of_leaves
#print axioms ZInQ.TauN1N2.neronModelExistsSelf_iff

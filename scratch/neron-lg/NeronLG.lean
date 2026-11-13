import ZInQKernel.HDecomp.Faltings.H5BaseChange

/-! # neron-lg: the glue `NeronLocalToGlobal` and `SemistableLocalToGlobal` of `scratch/tau-n1n2/`

§1 copies the two glue Props verbatim from `scratch/tau-n1n2/N1N2.lean`, with every definition
they depend on (also verbatim). Later sections reduce them to smaller named Props. -/

namespace ZInQ.NeronLG

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings
open PkgI3 (AbVar)
open ZInQ.H5Neron (jL NeronProp)
open scoped Obj

/-! ## §1. Verbatim copies from `scratch/tau-n1n2/N1N2.lean` -/

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

/-! ## §2. Shared notions and one new leaf (BLR §1.2 Prop. 4: the Néron property is local) -/

/-- The discrete valuation ring `𝓞_{L,v}` of a nonzero prime `v` of `𝓞_L`, as a valuation subring
of `L` (the ring of the `v`-adic valuation). -/
noncomputable def dvrAt {L : Type} [Field L] [NumberField L]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) : ValuationSubring L :=
  (v.valuation L).valuationSubring

instance {L : Type} [Field L] [NumberField L] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) :
    IsDiscreteValuationRing (dvrAt v) := by
  unfold dvrAt; infer_instance

/-- The Néron mapping property of a model `G` over `Spec R` of `B` (along `Spec L → Spec R`, with
the identification `gen` of the generic fibre): the `neron` field of `NeronModelOver`. -/
def IsNeronOver (R : Type) [CommRing R] (L : Type) [Field L] [Algebra R L] (B : AbVar L)
    (G : Over (Spec (CommRingCat.of R)))
    (gen : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj G ≅ B.X) : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of R))) [Smooth Y.hom],
    Function.Bijective fun f : Y ⟶ G =>
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).map f ≫ gen.hom

theorem spec_square {R L : Type} [CommRing R] [Field L] [Algebra R L] (O : ValuationSubring L)
    (φ : R →+* O) (hφ : (algebraMap O L).comp φ = algebraMap R L) :
    Spec.map (CommRingCat.ofHom (algebraMap O L)) ≫ Spec.map (CommRingCat.ofHom φ) =
      Spec.map (CommRingCat.ofHom (algebraMap R L)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]

/-- For `R → O ⊂ L` (compatible with the maps to `L`), the identification of the generic fibre of
the base change `G ×_R O` with `B`: `(G ×_R O) ×_O L ≅ G ×_R L ≅ B`. -/
noncomputable def bcGenO {R L : Type} [CommRing R] [Field L] [Algebra R L] {B : AbVar L}
    (G : Over (Spec (CommRingCat.of R)))
    (gen : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj G ≅ B.X)
    (O : ValuationSubring L) (φ : R →+* O) (hφ : (algebraMap O L).comp φ = algebraMap R L) :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O L)))).obj
      ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj G) ≅ B.X :=
  (ZInQ.H5Neron.pbCompIso _ _ G).symm ≪≫ ZInQ.H5Neron.pbEqIso (spec_square O φ hφ) G ≪≫ gen

/-- **Leaf NL (the Néron property is local on a Dedekind base).** Let `R` be a Dedekind domain with
fraction field a number field `L`, `B` an abelian variety over `L`, and `G` a smooth, separated,
quasi-compact `R`-scheme with an identification `gen` of its generic fibre with `B`. Then `G` has
the Néron mapping property over `R` if and only if, for every discrete valuation ring `O ⊂ L`
containing `R` (these are the localizations `R_𝔪` at the maximal ideals), the base change
`G ×_R O` has the Néron mapping property over `O`. Bosch–Lütkebohmert–Raynaud, *Néron Models*,
§1.2 Prop. 4 (UNVERIFIED locator; there the model `X_K` is any smooth separated `K`-scheme of
finite type and `X` any smooth separated `R`-model of finite type, so this is a special case).
Proof idea (not needed here): spreading out of smooth schemes and morphisms of finite
presentation from `R_𝔪` to a neighbourhood (EGA IV §8), and the uniqueness of extensions
(separatedness and schematic density of the generic fibre). -/
def NeronLocalOnBase : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (R : Type) [CommRing R] [IsDomain R] [IsDedekindDomain R]
    [Algebra R L] [IsFractionRing R L] (B : AbVar L) (G : Over (Spec (CommRingCat.of R)))
    [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom]
    (gen : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj G ≅ B.X),
    IsNeronOver R L B G gen ↔
      ∀ (O : ValuationSubring L) [IsDiscreteValuationRing O] (φ : R →+* O)
        (hφ : (algebraMap O L).comp φ = algebraMap R L),
        IsNeronOver O L B ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj G)
          (bcGenO G gen O φ hφ)

/-! ## §3. `NeronLocalToGlobal` reduced to three smaller glue statements and the leaf NL

Write `𝓞_L[1/g]` for the localization away from `g`; the statements quantify over every
presentation `R` of it (an `𝓞_L`-algebra with `IsLocalization.Away g R` and a compatible map to
`L`), which is harmless (all presentations are isomorphic) and keeps the statements free of
choices. -/

/-- `B` has a Néron model over `𝓞_L[1/g]` (over every presentation of that ring). -/
def NeronOverAway (L : Type) [Field L] [NumberField L] (B : AbVar L) (g : 𝓞 L) : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra (𝓞 L) R] [IsLocalization.Away g R] [Algebra R L]
    [IsScalarTower (𝓞 L) R L], Nonempty (NeronModelOver R L B)

/-- `B` extends to an abelian scheme over `𝓞_L[1/f]`: a smooth proper group scheme whose generic
fibre is identified with `B` as a group scheme (over every presentation of `𝓞_L[1/f]`). -/
def HasAbelianSchemeAway (L : Type) [Field L] [NumberField L] (B : AbVar L) (f : 𝓞 L) : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra (𝓞 L) R] [IsLocalization.Away f R] [Algebra R L]
    [IsScalarTower (𝓞 L) R L],
    ∃ (G : Over (Spec (CommRingCat.of R))) (_ : GrpObj G) (_ : Smooth G.hom) (_ : IsProper G.hom)
      (gen : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj G ≅ B.X),
      letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj G) :=
        Functor.grpObjObj
      IsMonHom gen.hom

/-- **Glue N1-g1 (spreading out an abelian variety).** An abelian variety `B` over a number field
`L` extends to an abelian scheme over `𝓞_L[1/f]` for some nonzero `f ∈ 𝓞_L`. Textbook (a
candidate for a textbook leaf): `L = colim 𝓞_L[1/f]`, so `B`, its group law, unit and inverse
and the group axioms (equalities of morphisms) descend to some `𝓞_L[1/f]` (EGA IV₃ 8.8.2), as do
properness (EGA IV₃ 8.10.5 (xii)) and smoothness (EGA IV₄ 17.7.8 (ii)); all locators UNVERIFIED.
Mathlib v4.35 has the descent of morphisms for affine transition maps
(`AlgebraicGeometry/.../AffineTransitionLimit.lean`, EGA IV 8.8.2) but not the descent of schemes
or of properness and smoothness. -/
def AbVarSpreadsOut : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (B : AbVar L), ∃ f : 𝓞 L, f ≠ 0 ∧ HasAbelianSchemeAway L B f

/-- **Glue N1-g2 (a local Néron model spreads out to a neighbourhood).** Given the leaves N1-ab
and NL: if `B` extends to an abelian scheme `𝒜` over `𝓞_L[1/f]` (`f ≠ 0`) and has a Néron model
`𝒩_v` over `𝓞_{L,v}`, then `B` has a Néron model over `𝓞_L[1/g]` for some `g ∉ v`. Proof
(STANDARD, not in Mathlib): `𝒩_v` is of finite presentation over `𝓞_{L,v} = colim_{h ∉ v}
𝓞_L[1/h]`, so it spreads out to a smooth separated group scheme `G` of finite type over some
`𝓞_L[1/h]`, `h ∉ v`, with `G ×_{𝓞_L[1/h]} 𝓞_{L,v} ≅ 𝒩_v` and the generic-fibre identification
spread out (EGA IV₃ 8.8.2, 8.10.5, IV₄ 17.7.8). On `𝓞_L[1/fh]` the canonical morphism `G → 𝒜`
(Néron property of `𝒜`, leaf N1-ab) is an isomorphism on generic fibres, hence over some
`𝓞_L[1/fhh']`, `h' ∉ v` (EGA IV₃ 8.8.2.5); choose `h'' ∉ v` lying in the finitely many other
primes containing `f` (prime avoidance) and put `g = hh'h''`. Over `𝓞_L[1/g]`, `G` is `𝒩_v` at
`v` and the abelian scheme `𝒜` at every other point, so it is Néron at every `𝓞_{L,w}` (N1-ab
for `w ≠ v`) and hence Néron over `𝓞_L[1/g]` (leaf NL). Locators UNVERIFIED. -/
def NeronNearPoint : Prop :=
  AbelianSchemeIsNeron → NeronLocalOnBase →
  ∀ (L : Type) [Field L] [NumberField L] (B : AbVar L) (f : 𝓞 L), f ≠ 0 → HasAbelianSchemeAway L B f →
    ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 L)), Nonempty (NeronModelOver (dvrAt v) L B) →
      ∃ g : 𝓞 L, g ∉ v.asIdeal ∧ NeronOverAway L B g

/-- **Glue N1-g3 (Néron models glue along a Zariski cover).** If `g₁, …, gₙ` generate the unit
ideal of `𝓞_L` and `B` has a Néron model over each `𝓞_L[1/gᵢ]`, then `B` has a Néron model over
`𝓞_L`. Proof (formal, not in Mathlib): the restriction of a Néron model over `𝓞_L[1/gᵢ]` to
`𝓞_L[1/gᵢgⱼ]` is a Néron model there (a smooth `𝓞_L[1/gᵢgⱼ]`-scheme is smooth over
`𝓞_L[1/gᵢ]`); by uniqueness (`NeronProp.uniqueIso`) the restrictions are identified by unique
isomorphisms compatible with `gen`, which satisfy the cocycle condition by uniqueness again; glue
the schemes (`Scheme.GlueData`), the group laws and `gen`; smooth and separated are local on the
base and the glued scheme is quasi-compact over `𝓞_L` (finite cover); the mapping property holds
because morphisms from a smooth `Y` are constructed on the pieces `Y|_{D(gᵢ)}` and glue by
uniqueness. No literature input. -/
def NeronGlueAway : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (B : AbVar L) (s : Finset (𝓞 L)),
    Ideal.span (s : Set (𝓞 L)) = ⊤ → (∀ g ∈ s, NeronOverAway L B g) →
      Nonempty (NeronModelOver (𝓞 L) L B)

/-- **`NeronLocalToGlobal` from the leaf NL and the glue N1-g1, N1-g2, N1-g3 (proved).** The
neighbourhoods given by N1-g2 at all nonzero primes, with `f`, generate the unit ideal (a maximal
ideal containing all of them would be a nonzero prime `v` whose own neighbourhood `g ∉ v` lies in
it), so finitely many do (`Ideal.span_eq_top_iff_finite`). -/
theorem neronLocalToGlobal_of (hsp : AbVarSpreadsOut) (hloc : NeronLocalOnBase)
    (hnear : NeronNearPoint) (hglue : NeronGlueAway) : NeronLocalToGlobal := by
  intro hab L _ _ B hO
  obtain ⟨f, hf0, hf⟩ := hsp L B
  let S : Set (𝓞 L) := {g | NeronOverAway L B g}
  have hS : Ideal.span S = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    have hbot : m ≠ ⊥ :=
      Ring.ne_bot_of_isMaximal_of_not_isField hm (NumberField.RingOfIntegers.not_isField L)
    let v : IsDedekindDomain.HeightOneSpectrum (𝓞 L) := ⟨m, hm.isPrime, hbot⟩
    obtain ⟨g, hgv, hg⟩ := hnear hab hloc L B f hf0 hf v (hO (dvrAt v))
    exact hgv (hle (Ideal.subset_span hg))
  obtain ⟨s, hsS, hs⟩ := (Ideal.span_eq_top_iff_finite S).1 hS
  exact hglue L B s hs (fun g hg => hsS hg)

/-- Sanity (proved): an abelian scheme over `𝓞_L[1/f]`, `f ≠ 0`, is a Néron model there, by
N1-ab (`𝓞_L[1/f]` is a Dedekind domain with fraction field `L`). So N1-g2 is only needed at the
finitely many primes containing `f`. -/
theorem neronOverAway_of_abelian (hab : AbelianSchemeIsNeron) {L : Type} [Field L]
    [NumberField L] {B : AbVar L} {f : 𝓞 L} (hf0 : f ≠ 0) (h : HasAbelianSchemeAway L B f) :
    NeronOverAway L B f := by
  intro R _ _ _ _ _
  obtain ⟨G, _, _, _, gen, hgen⟩ := h R
  have hM : Submonoid.powers f ≤ nonZeroDivisors (𝓞 L) :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hf0
  have : IsDomain R := IsLocalization.isDomain_of_le_nonZeroDivisors R hM
  have : IsDedekindDomain R := IsLocalization.isDedekindDomain (𝓞 L) hM R
  have : IsFractionRing R L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers f) R L
  exact ⟨⟨G, gen, hgen, fun Y _ => hab L R B G gen hgen Y⟩⟩

end ZInQ.NeronLG

#print axioms ZInQ.NeronLG.neronLocalToGlobal_of
#print axioms ZInQ.NeronLG.neronOverAway_of_abelian

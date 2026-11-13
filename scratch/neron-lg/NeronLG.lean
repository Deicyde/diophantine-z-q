import ZInQKernel.HDecomp.Faltings.H5BaseChange

/-! # neron-lg: the glue `NeronLocalToGlobal` and `SemistableLocalToGlobal` of `scratch/tau-n1n2/`

* §1 copies the two glue Props verbatim from `scratch/tau-n1n2/N1N2.lean`, with every definition
  they depend on (also verbatim).
* §2 proves that every DVR valuation subring of a number field is `dvrAt v` for a nonzero prime `v`
  (`dvrAt_center`) and that only finitely many miss `1/f` (`badPlaces_finite`); states the new
  **leaf** NL `NeronLocalOnBase` (BLR §1.2 Prop. 4) and proves from it that Néron models localize
  (`neronModelOver_localize`).
* §3 reduces `NeronLocalToGlobal` to NL and three **glue** statements N1-g1 `AbVarSpreadsOut`,
  N1-g2 `NeronNearPoint`, N1-g3 `NeronGlueAway` (`neronLocalToGlobal_of`, proved).
* §4 reduces `SemistableLocalToGlobal` to NL, N1-g1 and three **glue** statements N2-g1'
  `GoodPlaceAnyField`, N2-g2 `LocalSemistableMono`, N2-g3 `SemistableGlobalOfLocal`
  (`semistableLocalToGlobal_of`, `goodPlacesAnyField_of`, proved; composita `compositumFinset`).
* §5 assembles N1 and N2 from the leaves N1-loc, N1-ab, N2-loc, NL and the six glue statements
  (`n1_n2_of_leaves_and_glue`, proved), and shows N1-loc ⇐ N1-self + NL. -/

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

section Classify

/-! ### Every DVR of a number field is some `dvrAt v` (proved) -/

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [NumberField K]

/-- Every valuation subring of a number field contains `𝓞_K` (it is integrally closed). -/
theorem ringOfIntegers_mem (O : ValuationSubring K) (x : 𝓞 K) : (x : K) ∈ O := by
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1
    (show IsIntegral O (x : K) from x.isIntegral_coe.tower_top)
  exact hy ▸ y.2

/-- The inclusion `𝓞_K → O`. -/
def toO (O : ValuationSubring K) : 𝓞 K →+* O :=
  (algebraMap (𝓞 K) K).codRestrict O.toSubring (ringOfIntegers_mem O)

theorem toO_coe (O : ValuationSubring K) (x : 𝓞 K) : ((toO O x : O) : K) = algebraMap (𝓞 K) K x :=
  rfl

/-- The center of a DVR `O ⊂ K` on `𝓞_K`: a nonzero prime. -/
def center (O : ValuationSubring K) [IsDiscreteValuationRing O] :
    IsDedekindDomain.HeightOneSpectrum (𝓞 K) where
  asIdeal := (IsLocalRing.maximalIdeal O).comap (toO O)
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (IsDiscreteValuationRing.not_a_field O)
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (𝓞 K) (x : K)
    have hb0 : algebraMap (𝓞 K) K b ≠ 0 := by
      rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)]
      exact nonZeroDivisors.ne_zero hb
    have ha : toO O a = x * toO O b := by
      apply Subtype.ext
      rw [toO_coe, Subring.coe_mul, toO_coe, ← hab, div_mul_cancel₀ _ hb0]
    intro hbot
    have hmem : a ∈ (IsLocalRing.maximalIdeal O).comap (toO O) := by
      rw [Ideal.mem_comap, ha]; exact Ideal.mul_mem_right _ _ hx
    rw [hbot, Ideal.mem_bot] at hmem
    apply hx0
    apply Subtype.ext
    rw [← hab, hmem, map_zero, zero_div]; rfl

theorem center_asIdeal (O : ValuationSubring K) [IsDiscreteValuationRing O] (x : 𝓞 K) :
    x ∈ (center O).asIdeal ↔ toO O x ∈ IsLocalRing.maximalIdeal O := Iff.rfl

/-- **Every DVR valuation subring of a number field is `𝓞_{K,v}` for its center `v` (proved).** -/
theorem dvrAt_center (O : ValuationSubring K) [IsDiscreteValuationRing O] :
    dvrAt (center O) = O := by
  apply ValuationSubring.eq_of_le_of_ne_top
  · intro x hx
    obtain ⟨n, d, hnd⟩ :=
      IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer (center O) x hx
    have hd : IsUnit (toO O d) := by
      by_contra h
      exact d.2 ((center_asIdeal O d).2 ((IsLocalRing.mem_maximalIdeal _).2 h))
    have hvd : O.valuation (algebraMap (𝓞 K) K d) = 1 := (O.valuation_eq_one_iff _).1 hd
    apply O.mem_of_valuation_le_one
    have h2 := congrArg O.valuation hnd
    rw [map_mul, hvd, _root_.mul_one] at h2
    rw [h2]
    exact O.valuation_le_one (toO O n)
  · intro htop
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (IsDiscreteValuationRing.not_a_field O)
    have hall : ∀ y : K, y ∈ O := by
      intro y; rw [htop]; exact ValuationSubring.mem_top y
    have hu : IsUnit x := by
      refine isUnit_iff_exists_inv.2 ⟨⟨_, hall ((x : K))⁻¹⟩, Subtype.ext ?_⟩
      rw [Subring.coe_mul]
      exact mul_inv_cancel₀ (fun h => hx0 (Subtype.ext h))
    exact (IsLocalRing.mem_maximalIdeal _).1 hx hu

theorem mem_center_of_inv_notMem (O : ValuationSubring K) [IsDiscreteValuationRing O] (f : 𝓞 K)
    (hf : (algebraMap (𝓞 K) K f)⁻¹ ∉ O) : f ∈ (center O).asIdeal := by
  rw [center_asIdeal]
  by_contra h
  have hu : IsUnit (toO O f) := by
    by_contra h'
    exact h ((IsLocalRing.mem_maximalIdeal _).2 h')
  have hv : O.valuation (algebraMap (𝓞 K) K f) = 1 := (O.valuation_eq_one_iff _).1 hu
  apply hf
  apply O.mem_of_valuation_le_one
  rw [map_inv₀, hv, inv_one]

/-- **Only finitely many DVRs of `K` do not contain `1/f` (proved),** for `f ≠ 0` in `𝓞_K`. -/
theorem badPlaces_finite {f : 𝓞 K} (hf : f ≠ 0) :
    {O : ValuationSubring K | IsDiscreteValuationRing O ∧ (algebraMap (𝓞 K) K f)⁻¹ ∉ O}.Finite := by
  have hI : Ideal.span {f} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hf
  refine ((Ideal.finite_factors hI).image dvrAt).subset ?_
  rintro O ⟨hO, hfO⟩
  exact ⟨center O, Ideal.dvd_span_singleton.2 (mem_center_of_inv_notMem O f hfO), dvrAt_center O⟩

end Classify

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
the base change `G ×_R O` with `B`: `(G ×_R O) ×_O L ≅ G ×_R L ≅ B`. An `irreducible_def`: if the kernel may
unfold it (through the `eqToIso` in `pbEqIso`), checking `isMonHom_bcGenO` times out. -/
noncomputable irreducible_def bcGenO {R L : Type} [CommRing R] [Field L] [Algebra R L] {B : AbVar L}
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

/-! ### Localizing a Néron model at a DVR (proved from NL) -/

section BcGenO

variable {R L : Type} [CommRing R] [Field L] [Algebra R L] {B : AbVar L}
    (G : Over (Spec (CommRingCat.of R)))
    (gen : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj G ≅ B.X)
    (O : ValuationSubring L) (φ : R →+* O) (hφ : (algebraMap O L).comp φ = algebraMap R L)

/-! Separate lemmas: the same chain stated in one term makes the kernel time out. -/

theorem bcGenO_hom₁ : (bcGenO G gen O φ hφ).hom = ((ZInQ.H5Neron.pbCompIso _ _ G).symm ≪≫
    ZInQ.H5Neron.pbEqIso (spec_square O φ hφ) G ≪≫ gen).hom :=
  congrArg Iso.hom (bcGenO_def G gen O φ hφ)

theorem bcGenO_hom₂ : ((ZInQ.H5Neron.pbCompIso _ _ G).symm ≪≫
    ZInQ.H5Neron.pbEqIso (spec_square O φ hφ) G ≪≫ gen).hom =
    (ZInQ.H5Neron.pbCompIso _ _ G).symm.hom ≫
      (ZInQ.H5Neron.pbEqIso (spec_square O φ hφ) G ≪≫ gen).hom :=
  Iso.trans_hom _ _

omit [Algebra R L] in
theorem bcGenO_hom₃ : (ZInQ.H5Neron.pbCompIso (Spec.map (CommRingCat.ofHom (algebraMap O L)))
    (Spec.map (CommRingCat.ofHom φ)) G).symm.hom =
    ZInQ.H5Neron.pbCompInv (Spec.map (CommRingCat.ofHom (algebraMap O L)))
      (Spec.map (CommRingCat.ofHom φ)) G :=
  ZInQ.H5Neron.pbCompIso_symm_hom _ _ _

theorem bcGenO_hom₄ : (ZInQ.H5Neron.pbEqIso (spec_square O φ hφ) G ≪≫ gen).hom =
    ZInQ.H5Neron.pbEq (spec_square O φ hφ) G ≫ gen.hom :=
  (Iso.trans_hom _ _).trans (congrArg₂ (· ≫ ·) (ZInQ.H5Neron.pbEqIso_hom _ _) rfl)

theorem bcGenO_hom : (bcGenO G gen O φ hφ).hom =
      ZInQ.H5Neron.pbCompInv (Spec.map (CommRingCat.ofHom (algebraMap O L)))
        (Spec.map (CommRingCat.ofHom φ)) G ≫ ZInQ.H5Neron.pbEq (spec_square O φ hφ) G ≫ gen.hom :=
  (bcGenO_hom₁ G gen O φ hφ).trans ((bcGenO_hom₂ G gen O φ hφ).trans
    (congrArg₂ (· ≫ ·) (bcGenO_hom₃ G O φ) (bcGenO_hom₄ G gen O φ hφ)))

end BcGenO

theorem isMonHom_bcGenO {R L : Type} [CommRing R] [Field L] [Algebra R L] {B : AbVar L}
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    (gen : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj G ≅ B.X)
    (hgen : letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj G) :=
      Functor.grpObjObj
      IsMonHom gen.hom)
    (O : ValuationSubring L) (φ : R →+* O) (hφ : (algebraMap O L).comp φ = algebraMap R L) :
    letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj G) := Functor.grpObjObj
    letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O L)))).obj
      ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj G)) := Functor.grpObjObj
    IsMonHom (bcGenO G gen O φ hφ).hom := by
  have h1 := ZInQ.H5Neron.isMonHom_pbCompInv (Spec.map (CommRingCat.ofHom (algebraMap O L)))
    (Spec.map (CommRingCat.ofHom φ)) G
  have h2 := ZInQ.H5Neron.isMonHom_pbEq (spec_square O φ hφ) G
  rw [bcGenO_hom]
  infer_instance

/-- **A Néron model over `𝓞_L` localizes to a Néron model over every DVR `O ⊂ L` (proved from
the leaf NL, ⇒).** This is the "localization" step used in the sketches of N2-g2 and N2-g3. -/
theorem neronModelOver_localize (hNL : NeronLocalOnBase) {L : Type} [Field L] [NumberField L]
    {B : AbVar L} (𝒩 : NeronModelOver (𝓞 L) L B) (O : ValuationSubring L)
    [IsDiscreteValuationRing O] : Nonempty (NeronModelOver O L B) := by
  have hφ : (algebraMap O L).comp (toO O) = algebraMap (𝓞 L) L := RingHom.ext fun _ => rfl
  have hN := (hNL L (𝓞 L) B 𝒩.G 𝒩.gen).1 𝒩.neron O (toO O) hφ
  letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (toO O)))).obj 𝒩.G) :=
    Functor.grpObjObj
  haveI : Smooth ((Over.pullback (Spec.map (CommRingCat.ofHom (toO O)))).obj 𝒩.G).hom := by
    dsimp; infer_instance
  haveI : IsSeparated ((Over.pullback (Spec.map (CommRingCat.ofHom (toO O)))).obj 𝒩.G).hom := by
    dsimp; infer_instance
  haveI : QuasiCompact ((Over.pullback (Spec.map (CommRingCat.ofHom (toO O)))).obj 𝒩.G).hom := by
    dsimp; infer_instance
  exact ⟨⟨_, bcGenO 𝒩.G 𝒩.gen O (toO O) hφ, isMonHom_bcGenO 𝒩.G 𝒩.gen 𝒩.gen_hom O (toO O) hφ,
    fun Y _ => hN Y⟩⟩

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
(Néron property of `𝒜`, leaf N1-ab) is an isomorphism on generic fibres, hence over a dense open
of `Spec 𝓞_L[1/fh]` (EGA IV₃ 8.8.2.5), whose complement is a finite set `Z` of closed points. If
`f ∈ v` then `v ∉ D(fh) ⊇ Z`; if `f ∉ v` then `G → 𝒜` is already an isomorphism at `v` (both
sides are Néron over `𝓞_{L,v}`: `𝒩_v`, and `𝒜_{𝓞_{L,v}}` by N1-ab), so `v ∉ Z`. By prime avoidance
choose `h' ∉ v` lying in every point of `Z` and in every other prime containing `f`, and put
`g = hh'`. Over `𝓞_L[1/g]`, `G` is `𝒩_v` at `v` and `≅ 𝒜` near every other point `w`, so
`G ×_{𝓞_L[1/g]} 𝓞_{L,w}` is Néron for every `w` (`𝒩_v` at `v`; for `w ≠ v` an abelian scheme over
`𝓞_{L,w}`, Néron by N1-ab; the Néron property transports along isomorphisms compatible with
`gen`), hence `G` is Néron over `𝓞_L[1/g]` (leaf NL, ⇐). Locators UNVERIFIED. -/
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
uniqueness. No literature input. (Elements `gᵢ = 0` are harmless: `NeronOverAway L B 0` holds
vacuously, since no presentation of the zero ring maps to `L`, and `D(0) = ∅`.) -/
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


/-! ## §4. `SemistableLocalToGlobal` reduced to three smaller glue statements and the leaf NL -/

/-- The body of `LocalSemistableAt A O` for a fixed field `L₀` (`localSemistableAt_iff`). -/
def LocalSemistableWith {K : Type} [Field K] (A : AbVar K) (O : ValuationSubring K) (L₀ : Type)
    [Field L₀] [NumberField L₀] [Algebra K L₀] : Prop :=
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

theorem localSemistableAt_iff {K : Type} [Field K] (A : AbVar K) (O : ValuationSubring K) :
    LocalSemistableAt A O ↔
      ∃ (L₀ : Type) (_ : Field L₀) (_ : NumberField L₀) (_ : Algebra K L₀),
        LocalSemistableWith A O L₀ := Iff.rfl

/-- **Glue N2-g1 (good places need no extension).** Given the leaf N1-ab and the glue N1-g1: for
`A` over a number field `K` there is a finite set `T` of valuation subrings of `K` such that at
every DVR `O ∉ T` the local statement holds for **every** finite extension `L₀`. Proof (STANDARD,
not in Mathlib): by N1-g1, `A` extends to an abelian scheme `𝒜` over `𝓞_K[1/f]`, `f ≠ 0`; let `T`
be the (finitely many) DVRs of `K` in which `f` is not a unit. For `O ∉ T`, every `O₀ ⊂ L₀` over
`O` and `O' ⊂ L'` over `O₀`, the base changes `𝒜_{O₀}`, `𝒜_{O'}` are abelian schemes, hence Néron
models (N1-ab), so `𝒩₀ ≅ 𝒜_{O₀}` and `𝒩' ≅ 𝒜_{O'} = 𝒜_{O₀} ×_{O₀} O'` by group isomorphisms
compatible with `gen` (`NeronModelOver.uniqueIso` of tau-n1n2); take `U = 𝒩'`, `i = 𝟙` and `j`
the composite isomorphism, which satisfies the generic-fibre equation because every isomorphism
used is compatible with `gen`. (Spreading out is the hypothesis N1-g1; no locator is needed.) -/
def GoodPlacesAnyField : Prop :=
  AbelianSchemeIsNeron → AbVarSpreadsOut →
  ∀ (K : Type) [Field K] [NumberField K] (A : AbVar K), ∃ T : Finset (ValuationSubring K),
    ∀ (O : ValuationSubring K) [IsDiscreteValuationRing O], O ∉ T →
      ∀ (L₀ : Type) [Field L₀] [NumberField L₀] [Algebra K L₀], LocalSemistableWith A O L₀

/-- **Glue N2-g1' (a place where `A` has an abelian-scheme model needs no extension).** Given the
leaf N1-ab: if `A` extends to an abelian scheme `𝒜` over `𝓞_K[1/f]` (`f ≠ 0`) and `O ⊂ K` is a DVR
containing `1/f`, the local statement at `O` holds for every finite extension `L₀`. Proof
(STANDARD, not in Mathlib): `𝓞_K[1/f] ⊆ O`, so for `O₀ ⊂ L₀` over `O` and `O' ⊂ L'` over `O₀` the
base changes `𝒜_{O₀}`, `𝒜_{O'} = 𝒜_{O₀} ×_{O₀} O'` are abelian schemes, hence Néron (N1-ab), so
`𝒩₀ ≅ 𝒜_{O₀}` and `𝒩' ≅ 𝒜_{O'}` by group isomorphisms compatible with `gen`
(`NeronModelOver.uniqueIso` of tau-n1n2); take `U = 𝒩'`, `i = 𝟙` and `j` the composite
isomorphism; the generic-fibre equation holds because every isomorphism used is compatible with
`gen`. No further literature input. -/
def GoodPlaceAnyField : Prop :=
  AbelianSchemeIsNeron →
  ∀ (K : Type) [Field K] [NumberField K] (A : AbVar K) (f : 𝓞 K), f ≠ 0 →
    HasAbelianSchemeAway K A f →
    ∀ (O : ValuationSubring K) [IsDiscreteValuationRing O], (algebraMap (𝓞 K) K f)⁻¹ ∈ O →
      ∀ (L₀ : Type) [Field L₀] [NumberField L₀] [Algebra K L₀], LocalSemistableWith A O L₀

/-- **N2-g1 from N2-g1' (proved):** the DVRs not containing `1/f` are finitely many
(`badPlaces_finite`). -/
theorem goodPlacesAnyField_of (h : GoodPlaceAnyField) : GoodPlacesAnyField := by
  intro hab hsp K _ _ A
  obtain ⟨f, hf0, hf⟩ := hsp K A
  classical
  have hfin := badPlaces_finite hf0
  refine ⟨hfin.toFinset, fun O hO hOT L₀ _ _ _ => ?_⟩
  have hinv : (algebraMap (𝓞 K) K f)⁻¹ ∈ O := by
    by_contra hc
    exact hOT (hfin.mem_toFinset.2 ⟨hO, hc⟩)
  exact h hab K A f hf0 hf O hinv L₀

/-- Néron models of `A_{L₀}` over every DVR of every finite extension `L₀` of `K` (a consequence
of N1 and NL: `localNeronModelsOf`). -/
def LocalNeronModelsOf {K : Type} [Field K] (A : AbVar K) : Prop :=
  ∀ (L₀ : Type) [Field L₀] [NumberField L₀] [Algebra K L₀] (O₀ : ValuationSubring L₀)
    [IsDiscreteValuationRing O₀], Nonempty (NeronModelOver O₀ L₀ (A.baseChange L₀))

/-- (proved) N1 and NL give local Néron models of every `A_{L₀}`. -/
theorem localNeronModelsOf (hN1 : NeronModelExists) (hNL : NeronLocalOnBase) {K : Type} [Field K]
    (A : AbVar K) : LocalNeronModelsOf A := by
  intro L₀ _ _ _ O₀ _
  obtain ⟨𝒩, h𝒩⟩ := hN1 K A L₀
  exact neronModelOver_localize hNL ⟨𝒩.G, 𝒩.gen, 𝒩.gen_hom, fun Y _ => h𝒩 Y⟩ O₀

/-- **Glue N2-g2 (the local statement persists in larger fields).** Given local Néron models of
`A` (`LocalNeronModelsOf A`, from N1 and NL): if the local statement at `O` holds for `L₀`, it holds
for every finite extension `L₁ ⊇ L₀`.
Proof (STANDARD, not in Mathlib): given `O₁ ⊂ L₁` over `O`, `𝒩₁`, `L' ⊇ L₁`, `O' ⊂ L'` over `O₁`
and `𝒩'`, put `O₀ = O₁ ∩ L₀` (a DVR over `O`) and let `𝒩₀` be a Néron model over `O₀` (given by
the hypothesis). Apply the `L₀`-statement twice: to
`(O₀, 𝒩₀, L', O', 𝒩')`, giving `U → 𝒩'`, `j : U → 𝒩₀ ×_{O₀} O'`, and to `(O₀, 𝒩₀, L₁, O₁, 𝒩₁)`,
giving `U₁ → 𝒩₁`, `j₁ : U₁ → 𝒩₀ ×_{O₀} O₁`. Base-change the second to `O'` and take for the new
`U` the intersection of the two open subgroups `j(U)` and `(j₁)_{O'}(U₁ ×_{O₁} O')` of
`𝒩₀ ×_{O₀} O'`, with the induced open immersions into `𝒩'` and `𝒩₁ ×_{O₁} O'`. The generic-fibre
equation for the new pair follows from the two old ones: both sides land in `𝒩₁` and factor
uniquely through its generic fibre `≅ A_{L₁}`; two morphisms over `L₁` into `A_{L₁} = A_{L₀} ×_{L₀}
L₁` agree once their composites with `A_{L₁} → A_{L₀}` agree; morphisms over `L₀` into the generic
fibre of `𝒩₀` are determined by their composite to `𝒩₀`; and
`bcProj A L₀ L' = bcProj A L₁ L' ≫ bcProj A L₀ L₁`. No further literature input. -/
def LocalSemistableMono : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : AbVar K), LocalNeronModelsOf A →
  ∀ (O : ValuationSubring K) [IsDiscreteValuationRing O] (L₀ L₁ : Type) [Field L₀]
    [NumberField L₀] [Algebra K L₀] [Field L₁] [NumberField L₁] [Algebra K L₁] [Algebra L₀ L₁]
    [IsScalarTower K L₀ L₁], LocalSemistableWith A O L₀ → LocalSemistableWith A O L₁

/-- **Glue N2-g3 (one field for all places: local identity components glue).** Given the leaf
NL: if the local statement holds for one field `L₀` at every DVR of `K`, then for every Néron
model `𝒩₀` over `𝓞_{L₀}`, every finite `L' ⊇ L₀`, every Néron model `𝒩'` over `𝓞_{L'}` and every
base change `𝒱` of `𝒩₀`, some group model `𝒰` is an open subgroup of `𝒩'` and of `𝒱`. Proof
(STANDARD, not in Mathlib): localize `𝒩₀`, `𝒩'` at the DVRs of `L₀`, `L'` (Néron by NL). At every
prime the local statement gives open immersions `i : U → 𝒩'`, `j : U → 𝒱` compatible on generic
fibres; since `U` is flat its generic fibre is schematically dense and the targets are separated,
so `i = c ∘ j` for the canonical morphism `c : 𝒱 → 𝒩'` (Néron property of `𝒩'`; `𝒱` is smooth;
`c` is built from the isomorphism `e` of `IsBaseChangeOf 𝒱 𝒩₀` and `𝒩₀.gen`, not from `𝒱.gen`,
which `IsBaseChangeOf` does not compare with `e`).
Hence `c` is an open immersion on `j(U)`, an open subgroup containing the identity component of the
fibre, at every prime. Take `𝒰 = 𝒱⁰`, the identity component (open in `𝒱` and quasi-compact over
the noetherian base, SGA 3 VI_B 3.10); `c|_{𝒰}` is an open immersion over every local ring of the
base, hence (finite presentation, EGA IV₃ 8.10.5) an open immersion; `𝒰_{L'} = 𝒱_{L'}` since the
generic fibre is connected, which gives `gen`. Locators UNVERIFIED. -/
def SemistableGlobalOfLocal : Prop :=
  NeronLocalOnBase →
  ∀ (K : Type) [Field K] [NumberField K] (A : AbVar K) (L₀ : Type) [Field L₀] [NumberField L₀]
    [Algebra K L₀],
    (∀ (O : ValuationSubring K) [IsDiscreteValuationRing O], LocalSemistableWith A O L₀) →
    ∀ (𝒩₀ : GroupModel A L₀), 𝒩₀.IsNeronModel →
    ∀ (L' : Type) [Field L'] [NumberField L'] [Algebra K L'] [Algebra L₀ L'] [IsScalarTower K L₀ L']
      (𝒩' : GroupModel A L'), 𝒩'.IsNeronModel → ∀ 𝒱 : GroupModel A L', IsBaseChangeOf 𝒱 𝒩₀ →
        ∃ 𝒰 : GroupModel A L', IsOpenSubgroupModel 𝒰 𝒩' ∧ IsOpenSubgroupModel 𝒰 𝒱

/-- **Finitely many number fields embed in a common one (proved),** by iterating
`H5Neron.compositum`. -/
theorem compositumFinset (K : Type) [Field K] [NumberField K] {I : Type} (F : I → Type)
    [∀ i, Field (F i)] [∀ i, NumberField (F i)] [∀ i, Algebra K (F i)] (s : Finset I) :
    ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : Algebra K M),
      ∀ i ∈ s, ∃ (_ : Algebra (F i) M), IsScalarTower K (F i) M := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨K, inferInstance, inferInstance, inferInstance,
      fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | @insert a s ha ih =>
    obtain ⟨M, iM1, iM2, iM3, hM⟩ := ih
    obtain ⟨M', i1, i2, i3, i4, i5, t1, t2⟩ := ZInQ.H5Neron.compositum K M (F a)
    refine ⟨M', i1, i2, i3, fun i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact ⟨i5, t2⟩
    · obtain ⟨iFM, tFM⟩ := hM i hi
      letI : Algebra (F i) M' := ((algebraMap M M').comp (algebraMap (F i) M)).toAlgebra
      refine ⟨this, IsScalarTower.of_algebraMap_eq fun x => ?_⟩
      show algebraMap K M' x = algebraMap M M' (algebraMap (F i) M (algebraMap K (F i) x))
      rw [← IsScalarTower.algebraMap_apply K (F i) M, ← IsScalarTower.algebraMap_apply K M M']

/-- **One field `L₀` for all places (proved from N2-g1 and N2-g2).** Take the compositum of the
fields given at the finitely many places of `T`. -/
theorem semistableCommonField (h1 : GoodPlacesAnyField) (h2 : LocalSemistableMono)
    (hN1 : NeronModelExists) (hab : AbelianSchemeIsNeron) (hloc : NeronLocalOnBase)
    (hsp : AbVarSpreadsOut) (K : Type) [Field K] [NumberField K] (A : AbVar K)
    (hA : ∀ (O : ValuationSubring K) [IsDiscreteValuationRing O], LocalSemistableAt A O) :
    ∃ (L₀ : Type) (_ : Field L₀) (_ : NumberField L₀) (_ : Algebra K L₀),
      ∀ (O : ValuationSubring K) [IsDiscreteValuationRing O], LocalSemistableWith A O L₀ := by
  classical
  obtain ⟨T, hT⟩ := h1 hab hsp K A
  have hch : ∀ O : ValuationSubring K, ∃ (L₀ : Type) (_ : Field L₀) (_ : NumberField L₀)
      (_ : Algebra K L₀), IsDiscreteValuationRing O → LocalSemistableWith A O L₀ := by
    intro O
    by_cases hO : IsDiscreteValuationRing O
    · obtain ⟨L₀, i1, i2, i3, h⟩ := hA O
      exact ⟨L₀, i1, i2, i3, fun _ => h⟩
    · exact ⟨K, inferInstance, inferInstance, inferInstance, fun h => absurd h hO⟩
  choose F iF1 iF2 iF3 hF using hch
  obtain ⟨M, iM1, iM2, iM3, hM⟩ := compositumFinset K F T
  refine ⟨M, iM1, iM2, iM3, fun O hO => ?_⟩
  by_cases hOT : O ∈ T
  · obtain ⟨iFM, tFM⟩ := hM O hOT
    exact h2 K A (localNeronModelsOf hN1 hloc A) O (F O) M (hF O hO)
  · exact hT O hOT M

/-- **`SemistableLocalToGlobal` from the leaf NL and the glue N1-g1, N2-g1, N2-g2, N2-g3
(proved).** `𝒩₀` comes from N1 and `𝒱` from the proved glue H4b
(`H5Neron.groupModelBaseChangeExists`). -/
theorem semistableLocalToGlobal_of (hloc : NeronLocalOnBase) (hsp : AbVarSpreadsOut)
    (h1 : GoodPlacesAnyField) (h2 : LocalSemistableMono) (h3 : SemistableGlobalOfLocal) :
    SemistableLocalToGlobal := by
  intro hN1 hab K _ _ A hA
  obtain ⟨L₀, i1, i2, i3, hL₀⟩ := semistableCommonField h1 h2 hN1 hab hloc hsp K A hA
  obtain ⟨𝒩₀, h𝒩₀⟩ := hN1 K A L₀
  refine ⟨L₀, i1, i2, i3, 𝒩₀, h𝒩₀, ?_⟩
  intro L' _ _ _ _ _ 𝒩' h𝒩'
  obtain ⟨𝒱, h𝒱⟩ := ZInQ.H5Neron.groupModelBaseChangeExists K A L₀ L' 𝒩₀
  obtain ⟨𝒰, hU1, hU2⟩ := h3 hloc K A L₀ hL₀ 𝒩₀ h𝒩₀ L' 𝒩' h𝒩' 𝒱 h𝒱
  exact ⟨𝒰, 𝒱, h𝒱, hU1, hU2⟩


/-! ## §5. The whole Néron package: N1 and N2 from four leaves and six glue statements

Copied verbatim from `scratch/tau-n1n2/N1N2.lean` (statements and proofs): N2, the leaf N1-self
and its use, the local leaves N1-loc and N2-loc, and the two assembly theorems of tau-n1n2. -/

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

/-- **Leaf N1-loc (Néron models over a discrete valuation ring).** For an abelian variety `B` over
a number field `L` and a discrete valuation ring `O ⊂ L` with fraction field `L` (a valuation
subring that is a DVR; these are the localizations `𝓞_{L,𝔭}` at the nonzero primes), `B` has a
Néron model over `O`. BLR, *Néron Models*, §1.4 Thm 3 for the Dedekind domain `R = O` (in BLR the
local case is §1.3 Cor. 2 (strictly henselian `R`) with étale descent §6.2; UNVERIFIED locators).
A special case of the published theorem (only number fields, only DVRs). -/
def LocalNeronModelExists : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (O : ValuationSubring L) [IsDiscreteValuationRing O]
    (B : AbVar L), Nonempty (NeronModelOver O L B)

/-- **N1-self from the local leaf and the glue (proved).** -/
theorem neronModelExistsSelf_of_local (hloc : LocalNeronModelExists) (hab : AbelianSchemeIsNeron)
    (hglue : NeronLocalToGlobal) : NeronModelExistsSelf :=
  fun L _ _ B => hglue hab L B (fun O _ => hloc L O B)

/-- **N1 from the local leaf and the glue (proved).** -/
theorem neronModelExists_of_local (hloc : LocalNeronModelExists) (hab : AbelianSchemeIsNeron)
    (hglue : NeronLocalToGlobal) : NeronModelExists :=
  neronModelExists_of_self (neronModelExistsSelf_of_local hloc hab hglue)

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

/-- **N2 from the local leaf N2-loc, the leaves N1 and N1-ab, and the glue (proved).** -/
theorem semistableNeronIdentityComponent_of_local (hN1 : NeronModelExists)
    (hab : AbelianSchemeIsNeron) (hloc : LocalSemistableIdentityComponent)
    (hglue : SemistableLocalToGlobal) : SemistableNeronIdentityComponent :=
  fun K _ _ A => hglue hN1 hab K A (fun O _ => hloc K A O)

/-- **The leaf N1-loc is a consequence of N1-self (BLR §1.4 Thm 3) and NL (BLR §1.2 Prop. 4)
(proved).** So N1-loc is not stronger than the published statements. -/
theorem localNeronModelExists_of_self (h : NeronModelExistsSelf) (hNL : NeronLocalOnBase) :
    LocalNeronModelExists := by
  intro L _ _ O _ B
  obtain ⟨𝒩⟩ := h L B
  exact neronModelOver_localize hNL 𝒩 O

/-- **N1 and N2 from the leaves N1-loc, N1-ab, N2-loc, NL and the glue N1-g1, N1-g2, N1-g3,
N2-g1', N2-g2, N2-g3 (proved).** -/
theorem n1_n2_of_leaves_and_glue (hloc1 : LocalNeronModelExists) (hab : AbelianSchemeIsNeron)
    (hloc2 : LocalSemistableIdentityComponent) (hNL : NeronLocalOnBase)
    (g1 : AbVarSpreadsOut) (g2 : NeronNearPoint) (g3 : NeronGlueAway) (g4 : GoodPlaceAnyField)
    (g5 : LocalSemistableMono) (g6 : SemistableGlobalOfLocal) :
    NeronModelExists ∧ SemistableNeronIdentityComponent :=
  have hN1 : NeronModelExists := neronModelExists_of_local hloc1 hab (neronLocalToGlobal_of g1 hNL g2 g3)
  ⟨hN1, semistableNeronIdentityComponent_of_local hN1 hab hloc2
    (semistableLocalToGlobal_of hNL g1 (goodPlacesAnyField_of g4) g5 g6)⟩


/-! ## §6. Proof of the glue N2-g1' (`GoodPlaceAnyField`) from N1-ab

At a DVR `O` containing `1/f`, the abelian scheme `𝒜` over `𝓞_K[1/f]` base-changes to `O₀`; it is
Néron there (N1-ab), so the given `𝒩₀` is proper (`NeronModelOver.uniqueIso`). Hence
`𝒱 = 𝒩₀ ×_{O₀} O'` is smooth and proper, Néron over `O'` (N1-ab again), and the canonical
isomorphism `φ : 𝒩' ≅ 𝒱` (uniqueness) is the required `j`, with `U = 𝒩'` and `i = 𝟙`. The
generic-fibre equation reduces to the compatibility of the canonical identification `gen𝒱` with
the projections (`genV_compat`). -/

/-! Copied from `scratch/tau-n1n2/N1N2.lean` (§5 `isMonHom_of_reflect`, §7 uniqueness). -/

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

/-- `NeronModelOver` satisfies `NeronProp` along `Spec L → Spec R`. -/
theorem NeronModelOver.neronProp {R : Type} [CommRing R] {L : Type} [Field L] [Algebra R L]
    {B : AbVar L} (𝒩 : NeronModelOver R L B) :
    NeronProp (Spec.map (CommRingCat.ofHom (algebraMap R L))) (fun Y => Smooth Y.hom) 𝒩.G B.X
      𝒩.gen :=
  fun Y _ => 𝒩.neron Y

/-- **Uniqueness of Néron models over any base `R`**: two Néron models of `B` over `R` are
isomorphic by a group isomorphism compatible with the identifications of the generic fibres. -/
theorem NeronModelOver.uniqueIso {R : Type} [CommRing R] {L : Type} [Field L] [Algebra R L]
    {B : AbVar L} (𝒩 𝒩' : NeronModelOver R L B) :
    ∃ φ : 𝒩.G ≅ 𝒩'.G, IsMonHom φ.hom ∧
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).map φ.hom ≫ 𝒩'.gen.hom =
        𝒩.gen.hom := by
  obtain ⟨φ, hφ⟩ := 𝒩.neronProp.uniqueIso 𝒩'.neronProp
    (show Smooth 𝒩.G.hom from inferInstance) (show Smooth 𝒩'.G.hom from inferInstance)
  refine ⟨φ, ?_, hφ⟩
  have hg : IsMonHom 𝒩.gen.hom := 𝒩.gen_hom
  have hg' : IsMonHom 𝒩'.gen.hom := 𝒩'.gen_hom
  haveI : Smooth (𝟙_ (Over (Spec (CommRingCat.of R)))).hom := by dsimp; infer_instance
  haveI : Smooth (𝒩.G ⊗ 𝒩.G).hom := by
    show Smooth (pullback.fst 𝒩.G.hom 𝒩.G.hom ≫ 𝒩.G.hom); infer_instance
  exact isMonHom_of_reflect (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L))))
    φ.hom 𝒩.gen.hom 𝒩'.gen.hom hφ (fun a b hab => (𝒩'.neron _).1 hab)
    (fun a b hab => (𝒩'.neron _).1 hab)

section Pasting

open ZInQ.H5Neron (pbCompInv pbCompHom pbEq pbCompIso pbEqIso)

theorem pbCompInv_fst {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (G : Over Z) :
    (pbCompInv f g G).left ≫ pullback.fst G.hom (f ≫ g) =
      pullback.fst (pullback.snd G.hom g) f ≫ pullback.fst G.hom g := by
  have h := conjugateEquiv_counit ((Over.mapPullbackAdj f).comp (Over.mapPullbackAdj g))
    (Over.mapPullbackAdj (f ≫ g)) (Over.mapComp f g).hom G
  have h2 := congrArg CommaMorphism.left h
  simp only [Over.mapPullbackAdj_counit_app, Adjunction.comp_counit_app] at h2
  simp [pbCompInv, Over.pullbackComp, conjugateIsoEquiv, Over.mapComp]

theorem pbCompHom_fst {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (G : Over Z) :
    (pbCompHom f g G).left ≫ pullback.fst (pullback.snd G.hom g) f ≫ pullback.fst G.hom g =
      pullback.fst G.hom (f ≫ g) := by
  rw [← pbCompInv_fst, ← Category.assoc, ← Over.comp_left]
  have : pbCompHom f g G ≫ pbCompInv f g G = 𝟙 _ := (pbCompIso f g G).hom_inv_id
  rw [this, Over.id_left, Category.id_comp]

theorem pbEq_fst {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g) (G : Over Y) :
    (pbEq h G).left ≫ pullback.fst G.hom g = pullback.fst G.hom f := by
  subst h
  simp [pbEq, pbEqIso]

theorem pbMap_fst {X Y : Scheme.{0}} (d : X ⟶ Y) {G H : Over Y} (m : G ⟶ H) :
    ((Over.pullback d).map m).left ≫ pullback.fst H.hom d = pullback.fst G.hom d ≫ m.left := by
  simp [Over.pullback]

variable {S₀ S₁ T₀ T₁ : Scheme.{0}} (a : T₁ ⟶ S₁) (b : S₁ ⟶ S₀) (c : T₀ ⟶ S₀) (d : T₁ ⟶ T₀)
  (sq : a ≫ b = d ≫ c) (G : Over S₀) (X : Over T₀) (gen : (Over.pullback c).obj G ≅ X)

/-- Base change of a generic-fibre identification along a commutative square
`T₁ → S₁ → S₀ = T₁ → T₀ → S₀`: `(G ×_{S₀} S₁) ×_{S₁} T₁ ≅ G ×_{S₀} T₁ ≅ (G ×_{S₀} T₀) ×_{T₀} T₁ ≅
X ×_{T₀} T₁`. -/
noncomputable irreducible_def genSq :
    (Over.pullback a).obj ((Over.pullback b).obj G) ≅ (Over.pullback d).obj X :=
  (pbCompIso a b G).symm ≪≫ pbEqIso sq G ≪≫ pbCompIso d c G ≪≫ (Over.pullback d).mapIso gen

theorem genSq_hom₁ : (genSq a b c d sq G X gen).hom = ((pbCompIso a b G).symm ≪≫ pbEqIso sq G ≪≫
    pbCompIso d c G ≪≫ (Over.pullback d).mapIso gen).hom :=
  congrArg Iso.hom (genSq_def a b c d sq G X gen)

theorem genSq_hom₂ : (pbCompIso d c G ≪≫ (Over.pullback d).mapIso gen).hom =
    pbCompHom d c G ≫ (Over.pullback d).map gen.hom :=
  (Iso.trans_hom _ _).trans (congrArg₂ (· ≫ ·) (ZInQ.H5Neron.pbCompIso_hom _ _ _) rfl)

theorem genSq_hom₃ : (pbEqIso sq G ≪≫ pbCompIso d c G ≪≫ (Over.pullback d).mapIso gen).hom =
    pbEq sq G ≫ pbCompHom d c G ≫ (Over.pullback d).map gen.hom :=
  (Iso.trans_hom _ _).trans (congrArg₂ (· ≫ ·) (ZInQ.H5Neron.pbEqIso_hom _ _)
    (genSq_hom₂ c d G X gen))

theorem genSq_hom : (genSq a b c d sq G X gen).hom =
    pbCompInv a b G ≫ pbEq sq G ≫ pbCompHom d c G ≫ (Over.pullback d).map gen.hom :=
  (genSq_hom₁ a b c d sq G X gen).trans ((Iso.trans_hom _ _).trans
    (congrArg₂ (· ≫ ·) (ZInQ.H5Neron.pbCompIso_symm_hom _ _ _) (genSq_hom₃ a b c d sq G X gen)))

theorem isMonHom_genSq [GrpObj G] [GrpObj X]
    (hgen : letI : GrpObj ((Over.pullback c).obj G) := Functor.grpObjObj
      IsMonHom gen.hom) :
    letI : GrpObj ((Over.pullback b).obj G) := Functor.grpObjObj
    letI : GrpObj ((Over.pullback a).obj ((Over.pullback b).obj G)) := Functor.grpObjObj
    letI : GrpObj ((Over.pullback d).obj X) := Functor.grpObjObj
    IsMonHom (genSq a b c d sq G X gen).hom := by
  letI : GrpObj ((Over.pullback c).obj G) := Functor.grpObjObj
  have c1 := ZInQ.H5Neron.isMonHom_pbCompInv a b G
  have c2 := ZInQ.H5Neron.isMonHom_pbEq sq G
  have c3 := ZInQ.H5Neron.isMonHom_pbCompHom d c G
  rw [genSq_hom]
  infer_instance

include sq in
theorem genSq_cond : (pullback.fst ((Over.pullback b).obj G).hom a ≫ pullback.fst G.hom b) ≫ G.hom =
    (pullback.snd ((Over.pullback b).obj G).hom a ≫ d) ≫ c := by
  have hc : pullback.fst ((Over.pullback b).obj G).hom a ≫ pullback.snd G.hom b =
      pullback.snd ((Over.pullback b).obj G).hom a ≫ a := pullback.condition
  simp only [Category.assoc]
  rw [pullback.condition (f := G.hom) (g := b), reassoc_of% hc, sq]

/-- The first projection of `genSq`: `(G ×_{S₀} S₁) ×_{S₁} T₁ → G ×_{S₀} T₀ → X`. -/
theorem genSq_fst : (genSq a b c d sq G X gen).hom.left ≫ pullback.fst X.hom d =
    pullback.lift (pullback.fst _ a ≫ pullback.fst G.hom b) (pullback.snd _ a ≫ d)
      (genSq_cond a b c d sq G) ≫ gen.hom.left := by
  rw [genSq_hom, Over.comp_left, Over.comp_left, Over.comp_left, Category.assoc, Category.assoc,
    Category.assoc, pbMap_fst, ← Category.assoc (pbCompHom d c G).left]
  have e : (pbCompHom d c G).left ≫ pullback.fst ((Over.pullback c).obj G).hom d =
      pullback.lift (pullback.fst G.hom (d ≫ c)) (pullback.snd G.hom (d ≫ c) ≫ d)
        (by rw [pullback.condition, Category.assoc]) := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc]
      exact pbCompHom_fst d c G
    · rw [pullback.lift_snd, Category.assoc]
      have hc : pullback.fst ((Over.pullback c).obj G).hom d ≫ pullback.snd G.hom c =
          pullback.snd ((Over.pullback c).obj G).hom d ≫ d := pullback.condition
      have h : (pbCompHom d c G).left ≫ pullback.snd ((Over.pullback c).obj G).hom d =
          pullback.snd G.hom (d ≫ c) := Over.w (pbCompHom d c G)
      rw [hc, reassoc_of% h]
  have e2 : (pbCompInv a b G).left ≫ (pbEq sq G).left ≫
      pullback.lift (pullback.fst G.hom (d ≫ c)) (pullback.snd G.hom (d ≫ c) ≫ d)
        (by rw [pullback.condition, Category.assoc]) =
      pullback.lift (pullback.fst _ a ≫ pullback.fst G.hom b) (pullback.snd _ a ≫ d)
        (genSq_cond a b c d sq G) := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
      rw [pbEq_fst, pbCompInv_fst]
      rfl
    · simp only [Category.assoc, pullback.lift_snd]
      have h1 : (pbEq sq G).left ≫ pullback.snd G.hom (d ≫ c) = pullback.snd G.hom (a ≫ b) :=
        Over.w (pbEq sq G)
      have h2 : (pbCompInv a b G).left ≫ pullback.snd G.hom (a ≫ b) =
          pullback.snd ((Over.pullback b).obj G).hom a := Over.w (pbCompInv a b G)
      rw [reassoc_of% h1, reassoc_of% h2]
  rw [e, reassoc_of% e2]

include sq in
/-- Compatibility of `genSq ≪≫ e` with the projections to `G`, for any `e` whose composite with a
map `p` is the first projection `X ×_{T₀} T₁ → X`. -/
theorem genSq_compat {X' : Over T₁} (e : (Over.pullback d).obj X ≅ X') (p : X'.left ⟶ X.left)
    (he : e.hom.left ≫ p = pullback.fst X.hom d) :
    pullback.fst ((Over.pullback b).obj G).hom a ≫ pullback.fst G.hom b =
      (genSq a b c d sq G X gen ≪≫ e).hom.left ≫ p ≫ gen.inv.left ≫ pullback.fst G.hom c := by
  rw [Iso.trans_hom, Over.comp_left, Category.assoc, reassoc_of% he, reassoc_of% genSq_fst,
    ← Over.comp_left_assoc, Iso.hom_inv_id, Over.id_left, Category.id_comp, pullback.lift_fst]

end Pasting

section BcA

open ZInQ.H5Neron (pbCompInv pbEq pbCompIso pbEqIso)

variable {K : Type} [Field K] (A : AbVar K) (L₀ L' : Type) [Field L₀] [Field L'] [Algebra K L₀]
  [Algebra K L'] [Algebra L₀ L'] [IsScalarTower K L₀ L']

theorem bcA_sq : Spec.map (CommRingCat.ofHom (algebraMap L₀ L')) ≫
    Spec.map (CommRingCat.ofHom (algebraMap K L₀)) = Spec.map (CommRingCat.ofHom (algebraMap K L')) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

local notation "κ₀" => Spec.map (CommRingCat.ofHom (algebraMap K L₀))
local notation "κ'" => Spec.map (CommRingCat.ofHom (algebraMap K L'))
local notation "δ" => Spec.map (CommRingCat.ofHom (algebraMap L₀ L'))

/-- `(A_{L₀})_{L'} ≅ A_{L'}`, at the syntactic pullback types. -/
noncomputable irreducible_def bcA' : (Over.pullback δ).obj ((Over.pullback κ₀).obj A.X) ≅
    (Over.pullback κ').obj A.X :=
  (pbCompIso _ _ A.X).symm ≪≫ pbEqIso (bcA_sq L₀ L') A.X

/-- `(A_{L₀})_{L'} ≅ A_{L'}`. -/
noncomputable def bcA : (Over.pullback δ).obj (A.baseChange L₀).X ≅ (A.baseChange L').X :=
  bcA' A L₀ L'

theorem bcA'_hom₁ : (bcA' A L₀ L').hom =
    ((pbCompIso _ _ A.X).symm ≪≫ pbEqIso (bcA_sq L₀ L') A.X).hom :=
  congrArg Iso.hom (bcA'_def A L₀ L')

theorem bcA'_hom : (bcA' A L₀ L').hom = pbCompInv _ _ A.X ≫ pbEq (bcA_sq L₀ L') A.X :=
  (bcA'_hom₁ A L₀ L').trans ((Iso.trans_hom _ _).trans (congrArg₂ (· ≫ ·)
    (ZInQ.H5Neron.pbCompIso_symm_hom _ _ _) (ZInQ.H5Neron.pbEqIso_hom _ _)))

theorem isMonHom_bcA' :
    letI : GrpObj ((Over.pullback κ₀).obj A.X) := Functor.grpObjObj
    letI : GrpObj ((Over.pullback δ).obj ((Over.pullback κ₀).obj A.X)) := Functor.grpObjObj
    letI : GrpObj ((Over.pullback κ').obj A.X) := Functor.grpObjObj
    IsMonHom (bcA' A L₀ L').hom := by
  have c1 := ZInQ.H5Neron.isMonHom_pbCompInv δ κ₀ A.X
  have c2 := ZInQ.H5Neron.isMonHom_pbEq (bcA_sq L₀ L') A.X
  rw [bcA'_hom]
  infer_instance

theorem isMonHom_bcA :
    letI : GrpObj ((Over.pullback δ).obj (A.baseChange L₀).X) := Functor.grpObjObj
    IsMonHom (bcA A L₀ L').hom :=
  isMonHom_bcA' A L₀ L'

/-- `bcProj` at the syntactic pullback types. -/
noncomputable def bcProj' : pullback A.X.hom κ' ⟶ pullback A.X.hom κ₀ :=
  pullback.map A.X.hom κ' A.X.hom κ₀ (𝟙 _) δ (𝟙 _) (by simp) (by
      rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← IsScalarTower.algebraMap_eq])

theorem bcA'_proj : (bcA' A L₀ L').hom.left ≫ bcProj' A L₀ L' =
    pullback.fst ((Over.pullback κ₀).obj A.X).hom δ := by
  apply pullback.hom_ext
  · rw [Category.assoc]
    have h1 : bcProj' A L₀ L' ≫ pullback.fst A.X.hom κ₀ = pullback.fst A.X.hom κ' ≫ 𝟙 _ :=
      pullback.lift_fst _ _ _
    rw [h1, Category.comp_id, bcA'_hom, Over.comp_left, Category.assoc, pbEq_fst, pbCompInv_fst]
    rfl
  · rw [Category.assoc]
    have h1 : bcProj' A L₀ L' ≫ pullback.snd A.X.hom κ₀ = pullback.snd A.X.hom κ' ≫ δ :=
      pullback.lift_snd _ _ _
    have h2 : (bcA' A L₀ L').hom.left ≫ pullback.snd A.X.hom κ' =
        pullback.snd ((Over.pullback κ₀).obj A.X).hom δ := Over.w (bcA' A L₀ L').hom
    have h3 : pullback.fst ((Over.pullback κ₀).obj A.X).hom δ ≫ pullback.snd A.X.hom κ₀ =
        pullback.snd ((Over.pullback κ₀).obj A.X).hom δ ≫ δ := pullback.condition
    rw [h1, reassoc_of% h2, h3]

theorem bcA_proj : (bcA A L₀ L').hom.left ≫ bcProj A L₀ L' =
    pullback.fst (A.baseChange L₀).X.hom δ :=
  bcA'_proj A L₀ L'

end BcA




/-- At a place with an abelian-scheme model, a local Néron model `𝒩₀` is proper: `𝒜 ×_R O₀` is a
Néron model by N1-ab, isomorphic to `𝒩₀` by uniqueness. -/
theorem isProper_of_abelian (hab : AbelianSchemeIsNeron) {K : Type} [Field K] (A : AbVar K)
    {R : Type} [CommRing R] [Algebra R K] (𝒜 : Over (Spec (CommRingCat.of R))) [GrpObj 𝒜]
    [Smooth 𝒜.hom] [IsProper 𝒜.hom]
    (gen𝒜 : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj 𝒜 ≅ A.X)
    (hgen𝒜 : letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj 𝒜) :=
      Functor.grpObjObj
      IsMonHom gen𝒜.hom)
    {L₀ : Type} [Field L₀] [NumberField L₀] [Algebra K L₀] (O₀ : ValuationSubring L₀)
    [IsDiscreteValuationRing O₀] (ψ : R →+* O₀)
    (sq₀ : Spec.map (CommRingCat.ofHom (algebraMap O₀ L₀)) ≫ Spec.map (CommRingCat.ofHom ψ) =
      Spec.map (CommRingCat.ofHom (algebraMap K L₀)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)))
    (𝒩₀ : NeronModelOver O₀ L₀ (A.baseChange L₀)) : IsProper 𝒩₀.G.hom := by
  letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom ψ))).obj 𝒜) := Functor.grpObjObj
  haveI : Smooth ((Over.pullback (Spec.map (CommRingCat.ofHom ψ))).obj 𝒜).hom := by
    dsimp; infer_instance
  haveI : IsProper ((Over.pullback (Spec.map (CommRingCat.ofHom ψ))).obj 𝒜).hom := by
    dsimp; infer_instance
  have hgen₀ := isMonHom_genSq _ _ _ _ sq₀ 𝒜 A.X gen𝒜 hgen𝒜
  have hN₀ := hab L₀ O₀ (A.baseChange L₀) _ (genSq _ _ _ _ sq₀ 𝒜 A.X gen𝒜) hgen₀
  obtain ⟨φ₀, -, -⟩ := 𝒩₀.uniqueIso ⟨_, genSq _ _ _ _ sq₀ 𝒜 A.X gen𝒜, hgen₀, fun Y _ => hN₀ Y⟩
  rw [← Over.w φ₀.hom]
  infer_instance

/-- If the local Néron model `𝒩₀` is proper, `𝒱 = 𝒩₀ ×_{O₀} O'` is a Néron model over `O'` (N1-ab),
so every Néron model `𝒩'` over `O'` is isomorphic to it, compatibly with `gen`. -/
theorem iso_baseChange_of_proper (hab : AbelianSchemeIsNeron) {K : Type} [Field K] (A : AbVar K)
    {L₀ : Type} [Field L₀] [NumberField L₀] [Algebra K L₀] (O₀ : ValuationSubring L₀)
    (𝒩₀ : NeronModelOver O₀ L₀ (A.baseChange L₀)) [IsProper 𝒩₀.G.hom]
    {L' : Type} [Field L'] [NumberField L'] [Algebra K L'] [Algebra L₀ L'] [IsScalarTower K L₀ L']
    (O' : ValuationSubring L') [IsDiscreteValuationRing O']
    (hO' : O'.comap (algebraMap L₀ L') = O₀) (𝒩' : NeronModelOver O' L' (A.baseChange L'))
    (sqV : Spec.map (CommRingCat.ofHom (algebraMap O' L')) ≫
      Spec.map (CommRingCat.ofHom (resHom O₀ O' hO')) =
      Spec.map (CommRingCat.ofHom (algebraMap L₀ L')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap O₀ L₀))) :
    letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (resHom O₀ O' hO')))).obj 𝒩₀.G) :=
      Functor.grpObjObj
    ∃ φ : 𝒩'.G ≅ (Over.pullback (Spec.map (CommRingCat.ofHom (resHom O₀ O' hO')))).obj 𝒩₀.G,
      IsMonHom φ.hom ∧
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O' L')))).map φ.hom ≫
        (genSq _ _ _ _ sqV 𝒩₀.G (A.baseChange L₀).X 𝒩₀.gen ≪≫ bcA A L₀ L').hom = 𝒩'.gen.hom := by
  letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (resHom O₀ O' hO')))).obj 𝒩₀.G) :=
    Functor.grpObjObj
  haveI : Smooth ((Over.pullback (Spec.map (CommRingCat.ofHom (resHom O₀ O' hO')))).obj
    𝒩₀.G).hom := by dsimp; infer_instance
  haveI : IsProper ((Over.pullback (Spec.map (CommRingCat.ofHom (resHom O₀ O' hO')))).obj
    𝒩₀.G).hom := by dsimp; infer_instance
  have hgenV : letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O' L')))).obj
      ((Over.pullback (Spec.map (CommRingCat.ofHom (resHom O₀ O' hO')))).obj 𝒩₀.G)) :=
      Functor.grpObjObj
      IsMonHom (genSq _ _ _ _ sqV 𝒩₀.G (A.baseChange L₀).X 𝒩₀.gen ≪≫ bcA A L₀ L').hom := by
    have h1 := isMonHom_genSq _ _ _ _ sqV 𝒩₀.G (A.baseChange L₀).X 𝒩₀.gen 𝒩₀.gen_hom
    have h2 := isMonHom_bcA A L₀ L'
    rw [Iso.trans_hom]
    infer_instance
  have hNV := hab L' O' (A.baseChange L') _ _ hgenV
  exact 𝒩'.uniqueIso ⟨_, _, hgenV, fun Y _ => hNV Y⟩

/-- **Glue N2-g1' (`GoodPlaceAnyField`), proved.** -/
theorem goodPlaceAnyField : GoodPlaceAnyField := by
  intro hab K _ _ A f hf0 hf O _ hinv L₀ _ _ _ O₀ _ hO₀ 𝒩₀ L' _ _ _ _ _ O' _ hO' 𝒩'
  -- the localization `R = 𝓞_K[1/f]` with its map to `K`
  have hfK : IsUnit (algebraMap (𝓞 K) K f) := isUnit_iff_ne_zero.2 (by
    rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)]; exact hf0)
  letI : Algebra (Localization.Away f) K := (IsLocalization.Away.lift f hfK).toAlgebra
  haveI : IsScalarTower (𝓞 K) (Localization.Away f) K :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.Away.lift_eq f hfK x).symm
  obtain ⟨𝒜, i𝒜, s𝒜, p𝒜, gen𝒜, hgen𝒜⟩ := hf (Localization.Away f)
  -- the map `𝓞_K[1/f] → O₀`
  have hmem : ∀ x : 𝓞 K, algebraMap K L₀ (algebraMap (𝓞 K) K x) ∈ O₀ := fun x => by
    have : algebraMap (𝓞 K) K x ∈ O₀.comap (algebraMap K L₀) := by
      rw [hO₀]; exact ringOfIntegers_mem O x
    exact this
  let t₀ : 𝓞 K →+* O₀ :=
    ((algebraMap K L₀).comp (algebraMap (𝓞 K) K)).codRestrict O₀.toSubring hmem
  have ht₀ : IsUnit (t₀ f) := by
    have hi : algebraMap K L₀ (algebraMap (𝓞 K) K f)⁻¹ ∈ O₀ := by
      have : (algebraMap (𝓞 K) K f)⁻¹ ∈ O₀.comap (algebraMap K L₀) := by rw [hO₀]; exact hinv
      exact this
    refine isUnit_iff_exists_inv.2 ⟨⟨_, hi⟩, Subtype.ext ?_⟩
    show algebraMap K L₀ (algebraMap (𝓞 K) K f) * algebraMap K L₀ (algebraMap (𝓞 K) K f)⁻¹ = 1
    rw [← map_mul, mul_inv_cancel₀ hfK.ne_zero, map_one]
  let ψ : Localization.Away f →+* O₀ := IsLocalization.Away.lift f ht₀
  have hψ : (algebraMap O₀ L₀).comp ψ =
      (algebraMap K L₀).comp (algebraMap (Localization.Away f) K) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext x
    show ((ψ (algebraMap (𝓞 K) (Localization.Away f) x) : O₀) : L₀) =
      algebraMap K L₀ (algebraMap (Localization.Away f) K (algebraMap (𝓞 K) (Localization.Away f) x))
    rw [IsLocalization.Away.lift_eq, ← IsScalarTower.algebraMap_apply (𝓞 K) (Localization.Away f) K]
    rfl
  have sq₀ : Spec.map (CommRingCat.ofHom (algebraMap O₀ L₀)) ≫ Spec.map (CommRingCat.ofHom ψ) =
      Spec.map (CommRingCat.ofHom (algebraMap K L₀)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away f) K)) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hψ]
  haveI : IsProper 𝒩₀.G.hom := isProper_of_abelian hab A 𝒜 gen𝒜 hgen𝒜 O₀ ψ sq₀ 𝒩₀
  have sqV : Spec.map (CommRingCat.ofHom (algebraMap O' L')) ≫
      Spec.map (CommRingCat.ofHom (resHom O₀ O' hO')) =
      Spec.map (CommRingCat.ofHom (algebraMap L₀ L')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap O₀ L₀)) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  obtain ⟨φ, hφm, hφ⟩ := iso_baseChange_of_proper hab A O₀ 𝒩₀ O' hO' 𝒩' sqV
  -- `U = 𝒩'`, `i = 𝟙`, `j = φ`
  refine ⟨𝒩'.G, inferInstance, 𝟙 _, φ.hom, ?_, inferInstance, ?_, hφm, ?_⟩
  · show IsOpenImmersion (𝟙 𝒩'.G.left)
    infer_instance
  · show IsOpenImmersion ((Over.forget _).map φ.hom)
    infer_instance
  · rw [CategoryTheory.Functor.map_id, Over.id_left, Category.id_comp, ← hφ, Over.comp_left,
      Category.assoc]
    rw [← reassoc_of% (pbMap_fst (Spec.map (CommRingCat.ofHom (algebraMap O' L'))) φ.hom)]
    exact congrArg (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O' L')))).map
      φ.hom).left ≫ ·) (genSq_compat _ _ _ _ sqV 𝒩₀.G (A.baseChange L₀).X 𝒩₀.gen
        (bcA A L₀ L') (bcProj A L₀ L') (bcA_proj A L₀ L'))

end ZInQ.NeronLG

#print axioms ZInQ.NeronLG.neronLocalToGlobal_of
#print axioms ZInQ.NeronLG.neronOverAway_of_abelian
#print axioms ZInQ.NeronLG.localSemistableAt_iff
#print axioms ZInQ.NeronLG.compositumFinset
#print axioms ZInQ.NeronLG.semistableCommonField
#print axioms ZInQ.NeronLG.semistableLocalToGlobal_of
#print axioms ZInQ.NeronLG.dvrAt_center
#print axioms ZInQ.NeronLG.badPlaces_finite
#print axioms ZInQ.NeronLG.goodPlacesAnyField_of
#print axioms ZInQ.NeronLG.n1_n2_of_leaves_and_glue
#print axioms ZInQ.NeronLG.neronModelOver_localize
#print axioms ZInQ.NeronLG.localNeronModelsOf
#print axioms ZInQ.NeronLG.localNeronModelExists_of_self
#print axioms ZInQ.NeronLG.goodPlaceAnyField

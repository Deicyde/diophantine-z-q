import ZInQKernel.Contrib.OneProof.H.TailZ18

/-! # OneProof H, leaf-fold12: three research fields from their printed leaves (c-to-printed), `sixContactMin_of_open15`

c-to-printed (docs/research/c-to-printed.md, scratch/c-to-printed/CToPrinted.lean, copied verbatim below apart
from this header and its import) proves `neronLocalizesDVR` from BLR 1.2 Prop. 4, `faltingsLemma5BC` from
Faltings' Lemma 5 and Raynaud's bound, and `semistableNeronBaseChange` (SS2) from BLR 1.2/4, SGA 3 VI_B 3.10,
SGA 7 IX 3.3, EGA IV 8.10.5 and the textbook field `geomConnOfRationalPoint`. The next research generation
`OpenResearchLeaves12` replaces the three fields by those six printed leaves. -/

/-! # c-to-printed, Part N: `ReductGlue.NeronLocalizesDVR` from BLR §1.2 Prop. 4 in its printed form

`NeronLocalizesDVR` (field `neronLocalizesDVR` of `OpenResearchLeaves10`) is proved here from
`BLR_1_2_4`, Bosch–Lütkebohmert–Raynaud's Prop. 1.2/4 stated over an arbitrary Dedekind domain and an
arbitrary smooth, separated `R`-scheme of finite type, with the Néron property of BLR §1.2 Def. 1 over
Mathlib's schemes (`IsNeronModelOver`). No group law, no abelian variety, no number field occur in the
leaf. -/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace CToPrinted

/-- Verbatim copy of the field statement (`ZInQKernel/Contrib/OneProof/H/TailZ14.lean`, `ReductGlue`). -/
def NeronLocalizesDVR : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒩 : ZInQ.DefFaltings.GroupModel A L), 𝒩.IsNeronModel →
    ∀ (O : ValuationSubring L) [IsDiscreteValuationRing O], (ReductGlue.toO 𝒩 O).IsNeronModel

example : NeronLocalizesDVR = ReductGlue.NeronLocalizesDVR := rfl

/-! ## The printed statement -/

/-- **Néron model** (BLR, *Néron models*, §1.2 Def. 1; UNVERIFIED locator). `R` a Dedekind domain with
field of fractions `K`, `X` an `R`-scheme. `X` is a Néron model of its generic fibre `X_K = X ×_R K` when
`X` is smooth, separated and of finite type over `R` and has the Néron mapping property: for every smooth
`R`-scheme `Y`, every `K`-morphism `Y_K → X_K` extends uniquely to an `R`-morphism `Y → X`, i.e.
`Hom_R(Y, X) → Hom_K(Y_K, X_K)`, `f ↦ f_K`, is bijective. (BLR define a Néron model of a given `X_K`;
"`X` is a Néron model of `X_K`" for an `R`-model `X` with generic fibre `X_K` is this predicate, the
identification `X ×_R K ≅ X_K` being transported by composition.) -/
def IsNeronModelOver (R K : Type) [CommRing R] [Field K] [Algebra R K]
    (X : Over (Spec (CommRingCat.of R))) : Prop :=
  Smooth X.hom ∧ IsSeparated X.hom ∧ LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom ∧
    ∀ (Y : Over (Spec (CommRingCat.of R))) [Smooth Y.hom],
      Function.Bijective fun f : Y ⟶ X =>
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map f

/-- **LEAF `BLR_1_2_4`** (Bosch–Lütkebohmert–Raynaud, *Néron models*, Ergebnisse 21 (1990), §1.2
Prop. 4; number and wording recalled, UNVERIFIED, no network). *Printed* (as recalled): let `R` be a
Dedekind domain with field of fractions `K`, `X_K` a smooth and separated `K`-scheme of finite type, and
`X` a smooth, separated `R`-model of `X_K` of finite type. Then `X` is a Néron model of `X_K` if and only
if, for every closed point `s` of `Spec R`, `X ⊗_R 𝒪_{S,s}` is a Néron model of `X_K` over `𝒪_{S,s}`.

*Lean form*: `𝒪_{S,s} = R_𝔭` is any ring with `IsLocalization.AtPrime R_𝔭 𝔭` (Mathlib's characteristic
predicate; every such ring is uniquely isomorphic to `Localization.AtPrime 𝔭`), with a compatible map to
`K`; `X ⊗_R R_𝔭` is the pullback along `Spec R_𝔭 → Spec R`; its generic fibre is `X_K` because
`R → R_𝔭 → K` is `R → K`. `X_K` is not a separate datum: the model is `X`, with its own generic fibre.
(Reading risk, flagged by reduct-glue §5: the print may use the strict henselizations `𝒪^{sh}_{S,s}`, or
both; the strict-henselization form is not stated here.) -/
def BLR_1_2_4 : Prop :=
  ∀ (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (X : Over (Spec (CommRingCat.of R))) [Smooth X.hom] [IsSeparated X.hom] [QuasiCompact X.hom],
    IsNeronModelOver R K X ↔
      ∀ (𝔭 : Ideal R) [𝔭.IsMaximal] (R𝔭 : Type) [CommRing R𝔭] [Algebra R R𝔭]
        [IsLocalization.AtPrime R𝔭 𝔭] [Algebra R𝔭 K] [IsScalarTower R R𝔭 K],
        IsNeronModelOver R𝔭 K ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R R𝔭)))).obj X)

/-! ## Glue: a discrete valuation ring of a number field is the localization at its center -/

section Loc

variable {L : Type} [Field L] [NumberField L]

/-- The algebra structure `𝓞_L → O` (`ReductGlue.toOL`), as a local definition. -/
@[reducible] noncomputable def algOL (O : ValuationSubring L) : Algebra (𝓞 L) O :=
  (ReductGlue.toOL O).toAlgebra

theorem isScalarTower_OL (O : ValuationSubring L) :
    letI := algOL O
    IsScalarTower (𝓞 L) O L := by
  letI := algOL O
  exact IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/-- **`O = (𝓞_L)_{𝔭_O}`** as a characteristic predicate (from reduct-glue's `mem_iff_exists`). -/
theorem isLocalization_center (O : ValuationSubring L) [IsDiscreteValuationRing O] :
    letI := algOL O
    IsLocalization.AtPrime O (ReductGlue.center O) := by
  letI := algOL O
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨s, hs⟩
    exact ReductGlue.isUnit_toOL O hs
  · intro x
    obtain ⟨a, s, hs, h⟩ := (ReductGlue.mem_iff_exists O (x : L)).mp x.2
    refine ⟨⟨a, ⟨s, hs⟩⟩, ?_⟩
    apply Subtype.ext
    exact h
  · intro a b h
    refine ⟨1, ?_⟩
    have h' : ((a : L)) = (b : L) := congrArg (fun z : O => (z : L)) h
    have : a = b := RingOfIntegers.ext h'
    rw [this]

end Loc

/-! ## The field from the leaf -/

section Field

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- Postcomposition with an isomorphism does not change bijectivity. -/
theorem bijective_comp_iso {C : Type*} [Category C] {Y X : C} {Z W W' : C} (F : (Y ⟶ X) → (Z ⟶ W))
    (e : W ≅ W') : Function.Bijective (fun f => F f ≫ e.hom) ↔ Function.Bijective F := by
  have : (fun f => F f ≫ e.hom) = (fun g : Z ⟶ W => g ≫ e.hom) ∘ F := rfl
  rw [this]
  have hb : Function.Bijective (fun g : Z ⟶ W => g ≫ e.hom) :=
    ⟨fun g₁ g₂ h => by simpa using congrArg (· ≫ e.inv) h,
      fun g => ⟨g ≫ e.inv, by simp⟩⟩
  exact ⟨fun h => (Function.Bijective.of_comp_iff' hb F).mp h, fun h => hb.comp h⟩

/-- The kernel's Néron property of a group model is the printed one of its underlying scheme. -/
theorem isNeronModelOver_of (𝒩 : ZInQ.DefFaltings.GroupModel A L) (h : 𝒩.IsNeronModel) :
    IsNeronModelOver (𝓞 L) L 𝒩.G := by
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, fun Y _ => ?_⟩
  have hb := h Y
  refine ⟨fun a b hab => hb.1 ?_, fun g => ?_⟩
  · simp only at hab ⊢
    rw [hab]
  · obtain ⟨f, hf⟩ := hb.2 (g ≫ 𝒩.gen.hom)
    refine ⟨f, ?_⟩
    simp only at hf ⊢
    exact (cancel_mono 𝒩.gen.hom).mp hf

/-- **The field `neronLocalizesDVR` from the printed BLR 1.2/4.** -/
theorem neronLocalizesDVR_of_printed (hB : BLR_1_2_4) : ReductGlue.NeronLocalizesDVR := by
  intro K _ A L _ _ _ 𝒩 h𝒩 O _
  haveI := ReductGlue.center_isMaximal O
  letI := algOL O
  haveI := isScalarTower_OL O
  haveI := isLocalization_center O
  have h1 := isNeronModelOver_of 𝒩 h𝒩
  have h2 := ((hB (𝓞 L) L 𝒩.G).mp h1) (ReductGlue.center O) O
  obtain ⟨_, _, _, _, h3⟩ := h2
  have h4 : ∀ (Y : Over (Spec (CommRingCat.of O))) [Smooth Y.hom],
      Function.Bijective fun f : Y ⟶ (ReductGlue.toO 𝒩 O).G => (Over.pullback (ReductSplit.jO O)).map f :=
    h3
  intro Y _
  have hb := h4 Y
  refine ⟨fun a b hab => hb.1 ?_, fun g => ?_⟩
  · simp only at hab ⊢
    exact (cancel_mono (ReductGlue.toO 𝒩 O).gen.hom).mp hab
  · obtain ⟨f, hf⟩ := hb.2 (g ≫ (ReductGlue.toO 𝒩 O).gen.inv)
    refine ⟨f, ?_⟩
    simp only at hf ⊢
    rw [hf]
    simp

end Field


/-! # Part S: `semistableNeronBaseChange` (SS2)

reduct-glue proved SS2 from four leaves: reduct-split's `IdentityComponentBaseChangeDVR` (SGA 7 IX 3.3,
second assertion, in an open-subgroup form), `IdentityComponentOL` (SGA 3 VI_B 3.10, in a group-model form),
`OpenImmersionOfLocal` (EGA IV₃ 8.10.5, specialized to `Spec (𝓞_L)_𝔭`) and `NeronLocalizesDVR` (BLR 1.2/4).
The last is now a theorem from the printed `BLR_1_2_4` (Part N). For the other three this part states the
printed theorem over Mathlib definitions (`SGA3_VIB_3_10`, `SGA7_IX_3_3`, `EGAIV_8_10_5_openImm`), with the
identity component of a group scheme over a base defined as a set (`idCompSet`; Mathlib has none), and the
step from each printed form to the field's form as a named glue Prop. -/

/-- **SS2 from the printed BLR 1.2/4 and the three other leaves of reduct-glue** (compiled; the proof is
reduct-glue's `semistableNeronBaseChangeLocalGlobal_of` and `semistableLocalGlobal_leaf`). -/
theorem semistableNeronBaseChange_of_printedBLR (hB : BLR_1_2_4)
    (h33b : ReductSplit.IdentityComponentBaseChangeDVR) (hIC : ReductGlue.IdentityComponentOL)
    (hOI : ReductGlue.OpenImmersionOfLocal) : ZInQ.HeightSplit.SemistableNeronBaseChange :=
  ReductSplit.semistableNeronBaseChange_of_leaves h33b
    (ReductGlue.semistableLocalGlobal_leaf (neronLocalizesDVR_of_printed hB))
    (ReductGlue.semistableNeronBaseChangeLocalGlobal_of hIC hOI (neronLocalizesDVR_of_printed hB))

section IdComp

variable {S : Scheme.{0}}

/-- **The identity component `G⁰` of a group scheme `G → S`, as a set** (SGA 3 VI_B 3.1; Mathlib 4.35 has
no identity component of a group scheme over a base): the points `x` of `G` lying in the connected
component of `e(s)` in the fibre `G_s = f⁻¹(s)`, `s = f(x)` (the fibre with the subspace topology; it is
homeomorphic to the underlying space of the scheme `G ×_S κ(s)`, EGA I 3.6.1). -/
def idCompSet (G : Over S) [GrpObj G] : Set G.left :=
  {x | x ∈ connectedComponentIn (G.hom.base ⁻¹' {G.hom.base x})
    ((η[G] : 𝟙_ (Over S) ⟶ G).left.base (G.hom.base x))}

/-- **LEAF `SGA3_VIB_3_10`** (SGA 3 I, Exp. VI_B, Thm. 3.10; number recalled, UNVERIFIED; also EGA IV₃ 15.6.5,
Stacks 055R-type statements). *Printed* (as recalled): for a group scheme `G → S` locally of finite presentation
with smooth fibres, the union `G⁰` of the identity components of the fibres is open in `G`. *Lean form*: `G`
smooth over `S` (a special case), `G⁰ = idCompSet G`. -/
def SGA3_VIB_3_10 : Prop :=
  ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [Smooth G.hom], IsOpen (idCompSet G)

end IdComp

open ZInQ.HeightSplit ZInQ.DefFaltings in
/-- **GLUE `IdentityComponentGroupModel`** (from the open set `𝒢⁰` to the field's group model). For a group
model `𝒢` of `A_L` over `𝓞_L` whose identity component is open, the open subscheme on `𝒢⁰` is a group model
`𝒢₀` with an open immersion homomorphism into `𝒢` and connected geometric fibres at the maximal ideals.
Needs: (i) `𝒢⁰` is stable under the group law (each `(𝒢_s)⁰` is a subgroup: SGA 3 VI_A 2.3.1, from
`(𝒢_s)⁰ ×_{κ(s)} (𝒢_s)⁰` connected, Stacks 0385 with the bundle leaf `geomConnOfRationalPoint`), so the open
subscheme is a group object and the inclusion a homomorphism; (ii) quasi-compactness (`𝒢` noetherian);
(iii) the generic fibre: `A_L` is connected, so `(𝒢_L)⁰ = 𝒢_L` and `𝒢.gen` restricts; (iv) `(𝒢_𝔭)⁰` is
connected with a rational point, hence geometrically connected (bundle leaf `geomConnOfRationalPoint`,
Stacks 04KV), and the geometric fibre of `𝒢₀` at `𝔭` is `(𝒢_𝔭)⁰ ×_{κ(𝔭)} κ̄(𝔭)`. Not in Lean. -/
def IdentityComponentGroupModel : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L), IsOpen (idCompSet 𝒢.G) →
    ∃ (𝒢₀ : GroupModel A L) (i : 𝒢₀.G ⟶ 𝒢.G), IsOpenImmersion i.left ∧
      IsMonHom i ∧ ∀ (𝔭 : Ideal (𝓞 L)) [𝔭.IsMaximal], ConnectedSpace (geomFibre 𝒢₀ 𝔭).left

/-- `IdentityComponentOL` from the printed SGA 3 VI_B 3.10 and the glue. -/
theorem identityComponentOL_of_printed (h : SGA3_VIB_3_10) (g : IdentityComponentGroupModel) :
    ReductGlue.IdentityComponentOL :=
  fun K _ A L _ _ _ 𝒢 => g K A L 𝒢 (h _ 𝒢.G)

section SGA7

open ReductSplit

variable {K K' : Type} [Field K] [Field K'] [Algebra K K']

/-- The base change `𝒩 ×_O O'` along `O → O'` (`O' ∩ K = O`), as a scheme over `O'`. -/
noncomputable abbrev bcO {O : ValuationSubring K} {O' : ValuationSubring K'}
    (hO : O'.comap (algebraMap K K') = O) (G : Over (Spec (CommRingCat.of O))) :
    Over (Spec (CommRingCat.of O')) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (comapHom hO)))).obj G

/-- **LEAF `SGA7_IX_3_3`** (Grothendieck, SGA 7 I, Exp. IX, Prop. 3.3, second assertion; number and wording
recalled, UNVERIFIED). *Printed* (as recalled): `R → R'` a local homomorphism of discrete valuation rings
with fraction fields `K ⊆ K'`, `A_K` an abelian variety with semistable reduction, `N`, `N'` the Néron models
of `A_K` over `R` and of `A_{K'}` over `R'`; then the canonical morphism `N ×_R R' → N'` induces an
isomorphism `N⁰ ×_R R' ≅ N'⁰` of identity components.

*Lean form*: `K'/K` finite (the print allows any extension of discrete valuation rings, as recalled; the
finite case is a specialization), `O' ∩ K = O`; `c : 𝒩 ×_O O' → 𝒩'` any homomorphism whose generic fibre is
an isomorphism (the canonical morphism is one; any other is the canonical one followed by an automorphism of
the group scheme `𝒩'`, which preserves `𝒩'⁰`); `N⁰ ×_R R'` is the identity component of `𝒩 ×_O O'` (the
identity component commutes with base change, SGA 3 VI_B 3.3, UNVERIFIED), given as an open `U` with
`U = idCompSet`. Conclusion: `U → 𝒩'` is an open immersion with image `𝒩'⁰`. -/
def SGA7_IX_3_3 : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (K' : Type) [Field K'] [Algebra K K'] [FiniteDimensional K K'] (O' : ValuationSubring K')
    [IsDiscreteValuationRing O'] (hO : O'.comap (algebraMap K K') = O) (A : PkgI3.AbVar K),
    HasSemistableReduction A O →
    ∀ 𝒩 : GroupModelO A O, 𝒩.IsNeronModel →
    ∀ 𝒩' : GroupModelO (A.baseChange K') O', 𝒩'.IsNeronModel →
    letI : GrpObj (bcO hO 𝒩.G) := Functor.grpObjObj
    ∀ c : bcO hO 𝒩.G ⟶ 𝒩'.G, IsMonHom c → IsIso ((Over.pullback (jO O')).map c) →
    ∀ U : (bcO hO 𝒩.G).left.Opens, (U : Set (bcO hO 𝒩.G).left) = idCompSet (bcO hO 𝒩.G) →
      IsOpenImmersion (U.ι ≫ c.left) ∧ Set.range (U.ι ≫ c.left).base = idCompSet 𝒩'.G

/-- **GLUE `IdentityComponentFromPrinted`** (from the printed SGA 7 IX 3.3 to reduct-split's
`IdentityComponentBaseChangeDVR`). Needs: (i) the canonical homomorphism `c : 𝒩 ×_O O' → 𝒩'` (Néron mapping
property of `𝒩'` and reduct-glue's `isMonHom_of_ext`; its generic fibre is an isomorphism: `bcbcIso`);
(ii) an open subgroup scheme `U ⊆ 𝒩` with connected generic and geometric special fibres has image `𝒩⁰`
(an open subgroup of a group scheme over a field is closed, so it is a union of components; SGA 3 VI_A
2.3-2.4); (iii) the identity component commutes with base change: `(𝒩 ×_O O')⁰ = 𝒩⁰ ×_O O'` (SGA 3 VI_B 3.3;
fibres of `𝒩⁰` are geometrically connected by (ii) and Stacks 04KV); (iv) openness of `(𝒩 ×_O O')⁰` from
`SGA3_VIB_3_10`; then `U ×_O O' ≅ (𝒩 ×_O O')⁰ → 𝒩'` is an open immersion, a homomorphism because `c` is.
Not in Lean. -/
def IdentityComponentFromPrinted : Prop :=
  SGA3_VIB_3_10 → SGA7_IX_3_3 → IdentityComponentBaseChangeDVR

end SGA7

/-- **LEAF `EGAIV_8_10_5_openImm`** (EGA IV₃ 8.10.5, the open-immersion item; also Stacks 081M-type
statements; locator recalled, UNVERIFIED; the same setting as the kernel's leaf
`ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii`, which is the item for properness). `(D_i)` a directed inverse
system of quasi-compact quasi-separated schemes with affine transition maps, `c` a limit cone, `f_i : X_i → Y_i`
a morphism of schemes of finite presentation over `D_i`. If the base change of `f_i` to `lim D_i` is an open
immersion, so is its base change to some `D_j`. -/
def EGAIV_8_10_5_openImm : Prop :=
  ∀ (J : Type) [Preorder J] [IsDirectedOrder J] [Nonempty J] (D : Jᵒᵖ ⥤ Scheme.{0})
    [∀ {i j : Jᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] (c : Cone D), IsLimit c →
    ∀ (i : Jᵒᵖ) (Xi Yi : Over (D.obj i)), LocallyOfFinitePresentation Xi.hom → QuasiCompact Xi.hom →
      QuasiSeparated Xi.hom → LocallyOfFinitePresentation Yi.hom → QuasiCompact Yi.hom →
      QuasiSeparated Yi.hom → ∀ fi : Xi ⟶ Yi,
      IsOpenImmersion ((Over.pullback (c.π.app i)).map fi).left →
      ∃ (j : Jᵒᵖ) (a : j ⟶ i), IsOpenImmersion ((Over.pullback (D.map a)).map fi).left

/-- **GLUE `OpenImmersionLocalization`** (from EGA IV 8.10.5 to reduct-glue's `OpenImmersionOfLocal`).
Needs: (i) for a maximal ideal `𝔭` of `𝓞_L` (the center of a DVR `O`, `ReductGlue.dvrAt`), `Spec O` is the
limit of the basic opens `Spec 𝓞_L[1/s]`, `s ∉ 𝔭`, a directed system (by divisibility) of affine schemes with
affine transition maps (`O = colim 𝓞_L[1/s]`, as for `Spec L = lim Spec 𝓞_L[1/n!]` in the kernel's
`ZInQ.Contrib.SpreadOut.specConeIsLimit`); (ii) `X`, `Y` smooth, separated, quasi-compact over `𝓞_L` are of
finite presentation (`𝓞_L` noetherian), hence so are their base changes; (iii) an open immersion over each
`D(s_𝔭)` (and `⋃ D(s_𝔭) = Spec 𝓞_L`, the generic point lying in each) is an open immersion: open immersions
are local on the target (`IsZariskiLocalAtTarget`), and the base change along the open immersion
`D(s) → Spec 𝓞_L` is the restriction over `Y_{D(s)}`. Not in Lean. -/
def OpenImmersionLocalization : Prop :=
  EGAIV_8_10_5_openImm → ReductGlue.OpenImmersionOfLocal

/-- **SS2 from printed-form leaves and three named glue Props** (compiled): BLR 1.2/4, SGA 3 VI_B 3.10,
SGA 7 IX 3.3, EGA IV 8.10.5 (open immersions), with `IdentityComponentGroupModel`,
`IdentityComponentFromPrinted`, `OpenImmersionLocalization`. -/
theorem semistableNeronBaseChange_of_printed (hB : BLR_1_2_4) (h3 : SGA3_VIB_3_10)
    (h7 : SGA7_IX_3_3) (hE : EGAIV_8_10_5_openImm) (g1 : IdentityComponentGroupModel)
    (g2 : IdentityComponentFromPrinted) (g3 : OpenImmersionLocalization) :
    ZInQ.HeightSplit.SemistableNeronBaseChange :=
  semistableNeronBaseChange_of_printedBLR hB (g2 h3 h7) (identityComponentOL_of_printed h3 g1) (g3 hE)

/-! # Part F: `faltingsLemma5BC` from Faltings' Lemma 5 (printed identity) and Raynaud's bound

reduct-split proved `FaltingsLemma5BC` from the base-field form `HeightSplit.FaltingsLemma5` with no glue
(`ReductSplit.faltingsLemma5BC_final`). `FaltingsLemma5` (`|h(A) − h(B)| ≤ ½ log deg φ`) is a consequence of
two printed results (height-split §8): Faltings' Lemma 5, an identity with the correction term
`[K:ℚ]⁻¹ log #s*Ω¹_{G/𝓞_K}` for `G = ker(𝒩_A → 𝒩_B)`, and Raynaud's bound on that term. Both are stated here
over Mathlib objects: `G` is the fibre product `𝒩_A ×_{φ_𝒩, 𝒩_B, e} S`, its unit section `s`, and
`#s*Ω¹_{G/S}` is computed stalkwise as the conormal module `I/I²` of `s` (`kerOmegaLog`). -/

section Faltings

open ZInQ.HeightSplit ZInQ.DefFaltings

/-- Verbatim copy of `ZInQ.HeightSplit.FaltingsLemma5` (`ZInQKernel/Contrib/OneProof/H/TailY.lean`). -/
def FaltingsLemma5 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : PkgI3.AbVar K) (φ : A.X ⟶ B.X), IsIsogeny φ →
    ∀ (𝒩A : GroupModel A K) (𝒩B : GroupModel B K), 𝒩A.IsNeronModel → 𝒩B.IsNeronModel →
      IsSemistable 𝒩A → IsSemistable 𝒩B →
      ∀ x y : ℝ, 𝒩A.height = x → 𝒩B.height = y → |x - y| ≤ (1 / 2) * Real.log (isogDeg φ)

example : FaltingsLemma5 = ZInQ.HeightSplit.FaltingsLemma5 := rfl

/-- Verbatim copy of the field statement `ZInQ.HeightSplit.FaltingsLemma5BC`. -/
def FaltingsLemma5BC : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : PkgI3.AbVar K) (φ : A.X ⟶ B.X), IsIsogeny φ →
    ∀ (L : Type) [Field L] [NumberField L] [Algebra K L]
      (𝒩A : GroupModel A L) (𝒩B : GroupModel B L), 𝒩A.IsNeronModel → 𝒩B.IsNeronModel →
      IsSemistable 𝒩A → IsSemistable 𝒩B →
      ∀ x y : ℝ, 𝒩A.height = x → 𝒩B.height = y → |x - y| ≤ (1 / 2) * Real.log (isogDeg φ)

example : FaltingsLemma5BC = ZInQ.HeightSplit.FaltingsLemma5BC := rfl

variable {S : Scheme.{0}}

/-- The kernel `G = X ×_{f, Y, e} S` of a homomorphism `f : X → Y` of group schemes over `S`. -/
noncomputable abbrev kerScheme {X Y : Over S} [GrpObj Y] (f : X ⟶ Y) : Scheme.{0} :=
  pullback f.left (η[Y] : 𝟙_ (Over S) ⟶ Y).left

/-- The unit section `s : S → G` of the kernel of a homomorphism. -/
noncomputable def kerUnit {X Y : Over S} [GrpObj X] [GrpObj Y] (f : X ⟶ Y) (hf : IsMonHom f) :
    (𝟙_ (Over S)).left ⟶ kerScheme f :=
  pullback.lift (η[X] : 𝟙_ (Over S) ⟶ X).left (𝟙 _) (by
    rw [Category.id_comp, ← Over.comp_left, IsMonHom.one_hom])

/-- **`log #s*Ω¹_{G/S}`** for the kernel `G` of `f` and its unit section `s`: the sum over the points `P` of
`S` of `log #(I_P/I_P²)`, `I_P = ker(𝒪_{G,s(P)} → 𝒪_{S,P})` the stalk of the ideal of the section. For a
section `s` of `G → S`, `s*Ω¹_{G/S}` is the conormal sheaf `s*(I/I²)` (EGA IV 17.2.5, UNVERIFIED locator), whose
stalk at `P` is `I_P/I_P²`; over a Dedekind `S` a torsion coherent module is the sum of its stalks, so its
cardinality is the product of theirs. (An infinite stalk would contribute `log 0 = 0`; in the use below all stalks
are finite and almost all trivial.) Faltings' `G` is `𝒩_A⁰ ×_{𝒩_B⁰} S` (quasi-finite flat in the semistable
case); it is an open subscheme of `kerScheme φ_𝒩 = 𝒩_A ×_{𝒩_B} S` containing `s(S)`, so the stalks at `s(P)`,
and hence this number, are the same for both (independent review). -/
noncomputable def kerOmegaLog {X Y : Over S} [GrpObj X] [GrpObj Y] (f : X ⟶ Y) (hf : IsMonHom f) : ℝ :=
  ∑ᶠ (P : (𝟙_ (Over S)).left),
    Real.log (Nat.card (RingHom.ker ((kerUnit f hf).stalkMap P).hom).Cotangent)

theorem kerOmegaLog_nonneg {X Y : Over S} [GrpObj X] [GrpObj Y] (f : X ⟶ Y) (hf : IsMonHom f) :
    0 ≤ kerOmegaLog f hf :=
  finsum_nonneg fun _ => Real.log_natCast_nonneg _

/-- The generic-fibre condition: `φ_𝒩` extends `φ_K` through the identifications of the generic fibres. -/
def ExtendsIsogeny {K : Type} [Field K] [NumberField K] {A B : PkgI3.AbVar K} (φ : A.X ⟶ B.X)
    (𝒩A : GroupModel A K) (𝒩B : GroupModel B K) (φ𝒩 : 𝒩A.G ⟶ 𝒩B.G) : Prop :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 K) K)))).map φ𝒩 ≫ 𝒩B.gen.hom =
    𝒩A.gen.hom ≫ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K K)))).map φ

/-- **LEAF `FaltingsLemma5Printed`** (G. Faltings, *Endlichkeitssätze für abelsche Varietäten über
Zahlkörpern*, Invent. Math. 73 (1983), Lemma 5, p. 358; wording recalled, UNVERIFIED: locators.md could not
read it). *Printed* (as recalled): for an isogeny `φ : A → B` of abelian varieties over a number field `K` with
semistable reduction everywhere, `G = ker(φ_𝒩 : 𝒩_A → 𝒩_B)` (a quasi-finite flat group scheme over
`S = Spec 𝓞_K`) and `s` its unit section,
`h(B) = h(A) + ½ log deg φ − [K:ℚ]⁻¹ log #s*Ω¹_{G/S}`.
*Lean form*: `𝒩_A`, `𝒩_B` semistable Néron models over `𝓞_K` (kernel `GroupModel`), `φ_𝒩` the homomorphism
extending `φ` (unique by the Néron property, so "every" is "the"), heights the kernel's `GroupModel.height`
(the identity does not depend on the normalization of the metric, which shifts both sides equally). -/
def FaltingsLemma5Printed : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : PkgI3.AbVar K) (φ : A.X ⟶ B.X), IsIsogeny φ →
    ∀ (𝒩A : GroupModel A K) (𝒩B : GroupModel B K), 𝒩A.IsNeronModel → 𝒩B.IsNeronModel →
      IsSemistable 𝒩A → IsSemistable 𝒩B →
      ∀ (φ𝒩 : 𝒩A.G ⟶ 𝒩B.G) (hφ𝒩 : IsMonHom φ𝒩), ExtendsIsogeny φ 𝒩A 𝒩B φ𝒩 →
      ∀ x y : ℝ, 𝒩A.height = x → 𝒩B.height = y →
        y = x + (1 / 2) * Real.log (isogDeg φ) - kerOmegaLog φ𝒩 hφ𝒩 / Module.finrank ℚ K

/-- **LEAF `RaynaudKernelBound`** (M. Raynaud, *Hauteurs et isogénies*, Astérisque 127 (1985), Exp. VII,
Cor. 2.1.3 as cited by height-split §8 and Pazuki 2012 Rem. 2.3; number and wording recalled, UNVERIFIED).
In the setting of `FaltingsLemma5Printed`: `log #s*Ω¹_{G/S} ≤ [K:ℚ] log deg φ` (the lower bound `0 ≤` is
automatic, `kerOmegaLog_nonneg`). -/
def RaynaudKernelBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : PkgI3.AbVar K) (φ : A.X ⟶ B.X), IsIsogeny φ →
    ∀ (𝒩A : GroupModel A K) (𝒩B : GroupModel B K), 𝒩A.IsNeronModel → 𝒩B.IsNeronModel →
      IsSemistable 𝒩A → IsSemistable 𝒩B →
      ∀ (φ𝒩 : 𝒩A.G ⟶ 𝒩B.G) (hφ𝒩 : IsMonHom φ𝒩), ExtendsIsogeny φ 𝒩A 𝒩B φ𝒩 →
        kerOmegaLog φ𝒩 hφ𝒩 ≤ Module.finrank ℚ K * Real.log (isogDeg φ)

/-- The Néron extension of an isogeny is a homomorphism extending it (glue, proved). -/
theorem exists_extension {K : Type} [Field K] [NumberField K] {A B : PkgI3.AbVar K} (φ : A.X ⟶ B.X)
    (hφ : IsIsogeny φ) (𝒩A : GroupModel A K) (𝒩B : GroupModel B K) (hB : 𝒩B.IsNeronModel) :
    ∃ (φ𝒩 : 𝒩A.G ⟶ 𝒩B.G), IsMonHom φ𝒩 ∧ ExtendsIsogeny φ 𝒩A 𝒩B φ𝒩 := by
  haveI := hφ.1
  let F := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 K) K)))
  let fK := Spec.map (CommRingCat.ofHom (algebraMap K K))
  let φK : (A.baseChange K).X ⟶ (B.baseChange K).X := (Over.pullback fK).map φ
  have hK : IsMonHom φK := by
    letI : GrpObj ((Over.pullback fK).obj A.X) := Functor.grpObjObj
    letI : GrpObj ((Over.pullback fK).obj B.X) := Functor.grpObjObj
    exact (inferInstance : IsMonHom ((Over.pullback fK).map φ))
  obtain ⟨φ𝒩, h⟩ := (hB 𝒩A.G).2 (𝒩A.gen.hom ≫ φK)
  refine ⟨φ𝒩, ?_, h⟩
  haveI : Smooth (𝟙_ (Over (Spec (CommRingCat.of (𝓞 K))))).hom :=
    ZInQ.Contrib.NeronC.smooth_tensorUnit _
  haveI : Smooth (𝒩A.G ⊗ 𝒩A.G).hom :=
    ZInQ.Contrib.NeronC.smooth_tensor _ _ inferInstance inferInstance
  letI : GrpObj (F.obj 𝒩A.G) := Functor.grpObjObj
  letI : GrpObj (genericFibre K 𝒩A.G) := Functor.grpObjObj
  have hA := 𝒩A.gen_hom
  have h1 : IsMonHom (𝒩A.gen.hom ≫ φK) := @instIsMonHomComp _ _ _ _ _ _ _ _ _ _ _ hA hK
  exact ReductGlue.isMonHom_of_ext F (𝒩A.gen.hom ≫ φK) 𝒩B.gen.hom h1 𝒩B.gen_hom
    (hB _).1 (hB _).1 φ𝒩 h

/-- **`FaltingsLemma5` from the printed Lemma 5 and Raynaud's bound** (compiled). -/
theorem faltingsLemma5_of_printed (hF : FaltingsLemma5Printed) (hR : RaynaudKernelBound) :
    ZInQ.HeightSplit.FaltingsLemma5 := by
  intro K _ _ A B φ hφ 𝒩A 𝒩B hA hB sA sB x y hx hy
  obtain ⟨φ𝒩, hm, he⟩ := exists_extension φ hφ 𝒩A 𝒩B hB
  have hid := hF K A B φ hφ 𝒩A 𝒩B hA hB sA sB φ𝒩 hm he x y hx hy
  have hub := hR K A B φ hφ 𝒩A 𝒩B hA hB sA sB φ𝒩 hm he
  have hlb := kerOmegaLog_nonneg φ𝒩 hm
  have hn : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  set c := kerOmegaLog φ𝒩 hm
  set d := Real.log (isogDeg φ)
  have h1 : c / Module.finrank ℚ K ≤ d := by rw [div_le_iff₀ hn]; linarith
  have h2 : 0 ≤ c / Module.finrank ℚ K := div_nonneg hlb hn.le
  rw [hid, abs_le]
  constructor <;> linarith

/-- **The lower half of `FaltingsLemma5` from the printed Lemma 5 alone** (sem-prune): `h(B) = h(A) + ½ log deg φ −
[K:ℚ]⁻¹ log #s*Ω¹` with `0 ≤ log #s*Ω¹` (`kerOmegaLog_nonneg`); Raynaud's bound is not needed for this half. -/
theorem faltingsLemma5Lower_of_printed (hF : FaltingsLemma5Printed) :
    ZInQ.HeightSplit.FaltingsLemma5Lower := by
  intro K _ _ A B φ hφ 𝒩A 𝒩B hA hB sA sB x y hx hy
  obtain ⟨φ𝒩, hm, he⟩ := exists_extension φ hφ 𝒩A 𝒩B hB
  have hid := hF K A B φ hφ 𝒩A 𝒩B hA hB sA sB φ𝒩 hm he x y hx hy
  have hlb := kerOmegaLog_nonneg φ𝒩 hm
  have hn : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have h2 : 0 ≤ kerOmegaLog φ𝒩 hm / Module.finrank ℚ K := div_nonneg hlb hn.le
  rw [hid]
  linarith

/-- **The lower half of the field `faltingsLemma5BC` from the printed Lemma 5 alone** (sem-prune). -/
theorem faltingsLemma5BCLower_of_printed (hF : FaltingsLemma5Printed) :
    ZInQ.HeightSplit.FaltingsLemma5BCLower :=
  ReductSplit.faltingsLemma5BCLower_final (faltingsLemma5Lower_of_printed hF)

/-- **The field `faltingsLemma5BC` from the printed Lemma 5 and Raynaud's bound** (compiled, with
reduct-split's `faltingsLemma5BC_final`). -/
theorem faltingsLemma5BC_of_printed (hF : FaltingsLemma5Printed) (hR : RaynaudKernelBound) :
    ZInQ.HeightSplit.FaltingsLemma5BC :=
  ReductSplit.faltingsLemma5BC_final (faltingsLemma5_of_printed hF hR)

end Faltings

/-! # Part S, continued: the glue `OpenImmersionLocalization` proved

`Spec O = lim_{s ∉ 𝔭} Spec 𝓞_L[1/s]` for a DVR `O` of `L` with center `𝔭` (`specConeIsLimitO`, the pattern
of the kernel's `ZInQ.Contrib.SpreadOut.NF.specConeIsLimit`); EGA IV 8.10.5 then gives `s_𝔭 ∉ 𝔭` with the
base change to `𝓞_L[1/s_𝔭]` an open immersion; these opens cover `Spec 𝓞_L`, and open immersions are local
on the target (`IsZariskiLocalAtTarget.of_openCover`). -/

section OIL

/-- Base change along `u` then `v` is conjugate to base change along `u ≫ v` (for open immersions). -/
theorem isOpenImmersion_pb_pb_iff {S₁ S₂ S₃ : Scheme.{0}} (u : S₁ ⟶ S₂) (v : S₂ ⟶ S₃) (w : S₁ ⟶ S₃)
    (h : u ≫ v = w) {X Y : Over S₃} (f : X ⟶ Y) :
    IsOpenImmersion ((Over.pullback u).map ((Over.pullback v).map f)).left ↔
      IsOpenImmersion ((Over.pullback w).map f).left := by
  subst h
  have hn := congrArg CommaMorphism.left ((Over.pullbackComp u v).hom.naturality f)
  simp only [Over.comp_left, Functor.comp_map] at hn
  haveI : IsIso ((Over.pullbackComp u v).hom.app X).left :=
    Functor.map_isIso (Over.forget _) ((Over.pullbackComp u v).hom.app X)
  haveI : IsIso ((Over.pullbackComp u v).hom.app Y).left :=
    Functor.map_isIso (Over.forget _) ((Over.pullbackComp u v).hom.app Y)
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsOpenImmersion
    ((Over.pullbackComp u v).hom.app X).left, ← hn,
    MorphismProperty.cancel_right_of_respectsIso @IsOpenImmersion]

variable {L : Type} [Field L] [NumberField L]

/-- The index set `𝓞_L ∖ 𝔭`, preordered by divisibility. -/
abbrev Idx (P : Ideal (𝓞 L)) [P.IsPrime] : Type := P.primeCompl

instance (P : Ideal (𝓞 L)) [P.IsPrime] : Preorder (Idx P) where
  le a b := (a.1 : 𝓞 L) ∣ b.1
  le_refl _ := dvd_refl _
  le_trans _ _ _ h1 h2 := dvd_trans h1 h2

instance (P : Ideal (𝓞 L)) [P.IsPrime] : IsDirected (Idx P) (· ≤ ·) :=
  ⟨fun a b => ⟨⟨a.1 * b.1, P.primeCompl.mul_mem a.2 b.2⟩, dvd_mul_right _ _, dvd_mul_left _ _⟩⟩

instance (P : Ideal (𝓞 L)) [P.IsPrime] : Nonempty (Idx P) := ⟨⟨1, P.primeCompl.one_mem⟩⟩

variable (P : Ideal (𝓞 L)) [P.IsPrime]

/-- The stage `𝓞_L[1/a]`. -/
abbrev RgP (a : Idx P) : Type := Localization.Away (a.1 : 𝓞 L)

theorem ne_zero_idx (a : Idx P) : (a.1 : 𝓞 L) ≠ 0 := fun h => a.2 (h ▸ P.zero_mem)

theorem isUnit_trP {a b : Idx P} (h : a ≤ b) : IsUnit (algebraMap (𝓞 L) (RgP P b) a.1) :=
  isUnit_of_dvd_unit (map_dvd _ h) (IsLocalization.Away.algebraMap_isUnit b.1)

/-- `𝓞_L[1/a] → 𝓞_L[1/b]` for `a ∣ b`. -/
noncomputable def trP {a b : Idx P} (h : a ≤ b) : RgP P a →+* RgP P b :=
  IsLocalization.Away.lift a.1 (isUnit_trP P h)

theorem trP_alg {a b : Idx P} (h : a ≤ b) (x : 𝓞 L) :
    trP P h (algebraMap (𝓞 L) (RgP P a) x) = algebraMap (𝓞 L) (RgP P b) x :=
  IsLocalization.Away.lift_eq _ _ _

theorem homP_ext {a : Idx P} {T : Type*} [CommRing T] {f g : RgP P a →+* T}
    (h : ∀ x : 𝓞 L, f (algebraMap _ _ x) = g (algebraMap _ _ x)) : f = g :=
  IsLocalization.ringHom_ext (Submonoid.powers a.1) (RingHom.ext h)

/-- The diagram `a ↦ 𝓞_L[1/a]`. -/
noncomputable def ringDiagP : Idx P ⥤ CommRingCat.{0} where
  obj a := CommRingCat.of (RgP P a)
  map f := CommRingCat.ofHom (trP P (leOfHom f))
  map_id a := by
    apply CommRingCat.hom_ext
    exact homP_ext P (fun x => by simp [trP_alg])
  map_comp f g := by
    apply CommRingCat.hom_ext
    exact homP_ext P (fun x => by simp [trP_alg])

theorem trP_trP {a b c : Idx P} (h₁ : a ≤ b) (h₂ : b ≤ c) :
    (trP P h₂).comp (trP P h₁) = trP P (h₁.trans h₂) :=
  homP_ext P (fun x => by simp [trP_alg])

theorem trP_refl (a : Idx P) : trP P (le_refl a) = RingHom.id _ :=
  homP_ext P (fun x => by simp [trP_alg])

/-- The diagram `a ↦ Spec 𝓞_L[1/a]`. -/
noncomputable def specDiagP : (Idx P)ᵒᵖ ⥤ Scheme.{0} where
  obj a := Spec (CommRingCat.of (RgP P a.unop))
  map f := Spec.map (CommRingCat.ofHom (trP P (leOfHom f.unop)))
  map_id a := by
    rw [show leOfHom (𝟙 a).unop = le_refl a.unop from rfl, trP_refl, CommRingCat.ofHom_id,
      Spec.map_id]
  map_comp f g := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, trP_trP]

instance specDiagP_isAffineHom {i j : (Idx P)ᵒᵖ} (f : i ⟶ j) : IsAffineHom ((specDiagP P).map f) :=
  show IsAffineHom (Spec.map _) from inferInstance

instance specDiagP_compactSpace (i : (Idx P)ᵒᵖ) : CompactSpace ((specDiagP P).obj i) :=
  show CompactSpace (Spec _) from inferInstance

instance specDiagP_quasiSeparatedSpace (i : (Idx P)ᵒᵖ) : QuasiSeparatedSpace ((specDiagP P).obj i) :=
  show QuasiSeparatedSpace (Spec _) from inferInstance

variable (O : ValuationSubring L) [IsDiscreteValuationRing O]

/-- `𝓞_L[1/a] → O` for `a ∉ 𝔭_O`. -/
noncomputable def toOP (a : Idx (ReductGlue.center O)) : RgP (ReductGlue.center O) a →+* O :=
  IsLocalization.Away.lift a.1 (g := ReductGlue.toOL O) (ReductGlue.isUnit_toOL O a.2)

theorem toOP_alg (a : Idx (ReductGlue.center O)) (x : 𝓞 L) :
    toOP O a (algebraMap (𝓞 L) _ x) = ReductGlue.toOL O x :=
  IsLocalization.Away.lift_eq _ _ _

theorem toOL_injective : Function.Injective (ReductGlue.toOL O) := by
  intro a b h
  have h' : ((ReductGlue.toOL O a : O) : L) = ((ReductGlue.toOL O b : O) : L) := by rw [h]
  exact RingOfIntegers.ext h'

theorem toOP_injective (a : Idx (ReductGlue.center O)) : Function.Injective (toOP O a) := by
  unfold toOP IsLocalization.Away.lift
  rw [IsLocalization.lift_injective_iff]
  intro x y
  constructor
  · intro h
    rw [IsLocalization.injective (RgP _ a)
      (powers_le_nonZeroDivisors_of_noZeroDivisors (ne_zero_idx _ a)) h]
  · intro h
    rw [toOL_injective O h]

/-- `O` as a cocone over `a ↦ 𝓞_L[1/a]`. -/
noncomputable def ringCoconeO : Cocone (ringDiagP (ReductGlue.center O)) :=
  Cocone.mk (CommRingCat.of O)
    { app := fun a => CommRingCat.ofHom (toOP O a)
      naturality := fun a b f => by
        apply CommRingCat.hom_ext
        exact homP_ext _ (fun x => by simp [ringDiagP, trP_alg, toOP_alg]) }

/-- **`O = colim_{a ∉ 𝔭} 𝓞_L[1/a]`.** -/
noncomputable def ringCoconeOIsColimit : IsColimit (ringCoconeO O) := by
  haveI : ReflectsColimit (ringDiagP (ReductGlue.center O)) (forget CommRingCat) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  refine isColimitOfReflects (forget CommRingCat) (Types.FilteredColimit.isColimitOf' _ _ ?_ ?_)
  · intro (x : O)
    obtain ⟨r, s, hs, h⟩ := (ReductGlue.mem_iff_exists O (x : L)).mp x.2
    let j : Idx (ReductGlue.center O) := ⟨s, hs⟩
    refine ⟨j, (IsLocalization.mk' (RgP _ j) r (⟨s, Submonoid.mem_powers s⟩ : Submonoid.powers s) :
      RgP _ j), ?_⟩
    show x = toOP O j _
    unfold toOP IsLocalization.Away.lift
    symm
    rw [IsLocalization.lift_mk'_spec]
    apply Subtype.ext
    change (r : L) = (s : L) * (x : L)
    rw [← h, mul_comm]
  · intro j x y h
    have h' : toOP O j x = toOP O j y := h
    exact ⟨j, 𝟙 j, by rw [toOP_injective O j h']⟩

theorem toOP_trP {a b : Idx (ReductGlue.center O)} (h : a ≤ b) :
    (toOP O b).comp (trP _ h) = toOP O a :=
  homP_ext _ (fun x => by simp [trP_alg, toOP_alg])

/-- `Spec O` as a cone over `a ↦ Spec 𝓞_L[1/a]`. -/
noncomputable def specConeO : Cone (specDiagP (ReductGlue.center O)) :=
  Cone.mk (Spec (CommRingCat.of O))
    { app := fun a => Spec.map (CommRingCat.ofHom (toOP O a.unop))
      naturality := fun a b f => by
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, specDiagP]
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, toOP_trP] }

/-- **`Spec O = lim_{a ∉ 𝔭} Spec 𝓞_L[1/a]`.** -/
noncomputable def specConeOIsLimit : IsLimit (specConeO O) := by
  have h := isLimitOfPreserves Scheme.Spec (ringCoconeOIsColimit O).op
  refine (IsLimit.equivOfNatIsoOfIso (NatIso.ofComponents (fun _ => Iso.refl _) ?_) _ _
    (Cone.ext (Iso.refl _) ?_)) h
  · intro m n f
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · intro n
    simp only [Iso.refl_hom, Category.id_comp]

/-- From EGA IV 8.10.5 at one DVR `O`: some `s ∉ 𝔭_O` with the base change to `𝓞_L[1/s]` an open
immersion. -/
theorem exists_away_of_dvr (hE : EGAIV_8_10_5_openImm) {X Y : Over (Spec (CommRingCat.of (𝓞 L)))}
    [Smooth X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [Smooth Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Y.hom] (f : X ⟶ Y)
    (h : IsOpenImmersion ((Over.pullback (ReductGlue.gO O)).map f).left) :
    ∃ s : 𝓞 L, s ∉ ReductGlue.center O ∧ IsOpenImmersion ((Over.pullback (Spec.map
      (CommRingCat.ofHom (algebraMap (𝓞 L) (Localization.Away s))))).map f).left := by
  let P := ReductGlue.center O
  let i0 : (Idx P)ᵒᵖ := Opposite.op ⟨1, P.primeCompl.one_mem⟩
  let g1 := Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (RgP P i0.unop)))
  have hc : (specConeO O).π.app i0 ≫ g1 = ReductGlue.gO O := by
    show Spec.map (CommRingCat.ofHom (toOP O i0.unop)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (RgP P i0.unop))) =
      Spec.map (CommRingCat.ofHom (ReductGlue.toOL O))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext (toOP_alg O i0.unop)
  have h1 : IsOpenImmersion ((Over.pullback ((specConeO O).π.app i0)).map
      ((Over.pullback g1).map f)).left :=
    (isOpenImmersion_pb_pb_iff _ _ _ hc f).mpr h
  obtain ⟨j, a, hj⟩ := hE (Idx P) (specDiagP P) (specConeO O) (specConeOIsLimit O) i0
    ((Over.pullback g1).obj X) ((Over.pullback g1).obj Y) (ZInQ.Contrib.SpreadOut.lfp_pb g1 X)
    (ZInQ.Contrib.SpreadOut.qc_pb g1 X) (ZInQ.Contrib.SpreadOut.qs_pb g1 X)
    (ZInQ.Contrib.SpreadOut.lfp_pb g1 Y) (ZInQ.Contrib.SpreadOut.qc_pb g1 Y)
    (ZInQ.Contrib.SpreadOut.qs_pb g1 Y) ((Over.pullback g1).map f) h1
  refine ⟨j.unop.1, j.unop.2, ?_⟩
  have hc2 : (specDiagP P).map a ≫ g1 =
      Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (Localization.Away (j.unop.1 : 𝓞 L)))) := by
    show Spec.map (CommRingCat.ofHom (trP P (leOfHom a.unop))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (RgP P i0.unop))) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext (trP_alg P (leOfHom a.unop))
  exact (isOpenImmersion_pb_pb_iff _ _ _ hc2 f).mp hj

end OIL

/-- **The glue `OpenImmersionLocalization`, PROVED**: reduct-glue's `OpenImmersionOfLocal` from the
printed EGA IV 8.10.5 (open immersions). -/
theorem openImmersionLocalization : OpenImmersionLocalization := by
  intro hE L _ _ X Y _ _ _ _ _ _ f hloc
  have key : ∀ t : {𝔭 : Ideal (𝓞 L) // 𝔭.IsMaximal}, ∃ s : 𝓞 L, s ∉ t.1 ∧
      IsOpenImmersion ((Over.pullback (Spec.map
        (CommRingCat.ofHom (algebraMap (𝓞 L) (Localization.Away s))))).map f).left := by
    rintro ⟨𝔭, h𝔭⟩
    obtain ⟨s, hs, h⟩ := exists_away_of_dvr (ReductGlue.dvrAt 𝔭) hE f (hloc _)
    rw [ReductGlue.center_dvrAt] at hs
    exact ⟨s, hs, h⟩
  choose s hs hsO using key
  let gs : ∀ t : {𝔭 : Ideal (𝓞 L) // 𝔭.IsMaximal}, Spec (CommRingCat.of (Localization.Away (s t))) ⟶
      Spec (CommRingCat.of (𝓞 L)) := fun t =>
    Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (Localization.Away (s t))))
  have hcov : ∀ y : Y.left, ∃ t z, (pullback.fst Y.hom (gs t)) z = y := by
    intro y
    let q : PrimeSpectrum (𝓞 L) := Y.hom y
    have hq : ∃ t, s t ∉ q.asIdeal := by
      by_cases hq : q.asIdeal = ⊥
      · obtain ⟨𝔭, h𝔭⟩ := Ideal.exists_maximal (𝓞 L)
        refine ⟨⟨𝔭, h𝔭⟩, ?_⟩
        rw [hq, Ideal.mem_bot]
        intro h0
        exact hs ⟨𝔭, h𝔭⟩ (h0 ▸ 𝔭.zero_mem)
      · exact ⟨⟨q.asIdeal, Ideal.IsPrime.isMaximal q.isPrime hq⟩,
          hs ⟨q.asIdeal, Ideal.IsPrime.isMaximal q.isPrime hq⟩⟩
    obtain ⟨t, ht⟩ := hq
    have hr : y ∈ Set.range (pullback.fst Y.hom (gs t)) := by
      rw [Scheme.Pullback.range_fst]
      have h1 : Y.hom y ∈ ((gs t).opensRange : Set (Spec (CommRingCat.of (𝓞 L)))) := by
        rw [Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of (𝓞 L)) (s t)]
        exact ht
      exact h1
    obtain ⟨z, hz⟩ := hr
    exact ⟨t, z, hz⟩
  let 𝒰 : Y.left.OpenCover := Scheme.Cover.mkOfCovers {𝔭 : Ideal (𝓞 L) // 𝔭.IsMaximal}
    (fun t => pullback Y.hom (gs t)) (fun t => pullback.fst Y.hom (gs t)) hcov
    (fun t => inferInstance)
  refine IsZariskiLocalAtTarget.of_openCover 𝒰 (fun t => ?_)
  show IsOpenImmersion (pullback.snd f.left (pullback.fst Y.hom (gs t)))
  have heq : pullback.snd f.left (pullback.fst Y.hom (gs t)) =
      (pullbackRightPullbackFstIso Y.hom (gs t) f.left ≪≫
        pullback.congrHom (Over.w f) rfl).hom ≫ ((Over.pullback (gs t)).map f).left := by
    apply pullback.hom_ext
    · simp [Over.pullback_map_left, pullbackRightPullbackFstIso_hom_fst_assoc, pullback.condition]
    · simp [Over.pullback_map_left]
  rw [heq]
  haveI := hsO t
  infer_instance

/-- reduct-glue's leaf `OpenImmersionOfLocal` is a theorem from the printed EGA IV 8.10.5. -/
theorem openImmersionOfLocal_of_printed (hE : EGAIV_8_10_5_openImm) :
    ReductGlue.OpenImmersionOfLocal :=
  openImmersionLocalization hE

/-- **SS2 from four printed-form leaves and two named glue Props** (compiled). -/
theorem semistableNeronBaseChange_of_printed' (hB : BLR_1_2_4) (h3 : SGA3_VIB_3_10)
    (h7 : SGA7_IX_3_3) (hE : EGAIV_8_10_5_openImm) (g1 : IdentityComponentGroupModel)
    (g2 : IdentityComponentFromPrinted) : ZInQ.HeightSplit.SemistableNeronBaseChange :=
  semistableNeronBaseChange_of_printed hB h3 h7 hE g1 g2 openImmersionLocalization

/-! # Part S, continued: `IdentityComponentFromPrinted` reduced to two topological glue Props -/

section FromPrinted

open ReductSplit

/-- **GLUE `OpenSubgroupIsIdComp`** (topology of group schemes over a DVR). An open subgroup scheme `U` of a
group model `𝒩` over a DVR `O` whose generic fibre and geometric special fibre are connected has image the
identity component `𝒩⁰` (as a set). Needs: over each of the two points of `Spec O`, the fibre `U_s` is an open
subgroup of `𝒩_s`, hence closed (its complement is a union of cosets; SGA 3 VI_A 2.3-2.4, Stacks 047R-type
statements), and connected (the generic fibre directly; the special fibre as the image of the connected
geometric fibre), so `U_s = (𝒩_s)⁰`. Not in Lean. -/
def OpenSubgroupIsIdComp : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O] (A : PkgI3.AbVar K)
    (𝒩 : GroupModelO A O) (U : Over (Spec (CommRingCat.of O))) [GrpObj U] (i : U ⟶ 𝒩.G),
    IsOpenImmersion i.left → IsMonHom i → ConnectedSpace ((Over.pullback (jO O)).obj U).left →
    ConnectedSpace ((Over.pullback (Spec.map (CommRingCat.ofHom
      (algebraMap O (ResBarO O))))).obj U).left →
    Set.range i.left = idCompSet 𝒩.G

/-- **GLUE `IdCompBaseChangeDVR`** (the identity component commutes with base change; SGA 3 VI_B 3.3,
UNVERIFIED). For a smooth quasi-compact group scheme `G` over a DVR `O` and `O ⊆ O'`, the preimage of `G⁰` in
`G ×_O O'` is `(G ×_O O')⁰`. (Proved below, `idCompBaseChangeDVR_of`, from SGA 3 VI_B 3.10 and the bundle leaf
`geomConnOfRationalPoint`.) Needs: `(G_s)⁰` has a rational point, so it is geometrically connected (bundle leaf
`geomConnOfRationalPoint`, Stacks 04KV), so `(G_s)⁰ ×_{κ(s)} κ(s')` is connected, open and closed in `G_{s'}`
and contains `e`; and the fibre of `G ×_O O'` over `s'` is `G_s ×_{κ(s)} κ(s')`. Not in Lean. -/
def IdCompBaseChangeDVR : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (K' : Type) [Field K'] [Algebra K K'] [FiniteDimensional K K'] (O' : ValuationSubring K')
    [IsDiscreteValuationRing O'] (hO : O'.comap (algebraMap K K') = O)
    (G : Over (Spec (CommRingCat.of O))) [GrpObj G] [Smooth G.hom] [QuasiCompact G.hom],
    letI : GrpObj (bcO hO G) := Functor.grpObjObj
    pullback.fst G.hom (Spec.map (CommRingCat.ofHom (comapHom hO))) ⁻¹' idCompSet G =
      idCompSet (bcO hO G)

/-- **`IdentityComponentFromPrinted` from the two topological glue Props** (compiled). The canonical
homomorphism `c : 𝒩 ×_O O' → 𝒩'` is built from the Néron property of `𝒩'` (reduct-glue's `bcDVR`,
`isMonHom_of_ext`); `j = (i ×_O O') ≫ c` is an open immersion because `i ×_O O'` is an open immersion onto
`(𝒩 ×_O O')⁰` (the two glue Props and `range_map`), on which `c` is an open immersion by SGA 7 IX 3.3. -/
theorem identityComponentFromPrinted_of (ga : OpenSubgroupIsIdComp) (gb : IdCompBaseChangeDVR) :
    IdentityComponentFromPrinted := by
  intro h3 h7 K _ O _ K' _ _ _ O' _ hO A hss 𝒩 h𝒩 𝒩' h𝒩' U _ i hoi hmi hcg hcs
  let N := ReductGlue.bcDVR hO 𝒩
  haveI : Smooth (𝟙_ (Over (Spec (CommRingCat.of O')))).hom :=
    ZInQ.Contrib.NeronC.smooth_tensorUnit _
  haveI : Smooth (N.G ⊗ N.G).hom := ZInQ.Contrib.NeronC.smooth_tensor _ _ inferInstance inferInstance
  obtain ⟨c, hc⟩ := (h𝒩' N.G).2 N.gen.hom
  simp only at hc
  have hcm : IsMonHom c :=
    ReductGlue.isMonHom_of_ext (Over.pullback (jO O')) N.gen.hom 𝒩'.gen.hom N.gen_hom 𝒩'.gen_hom
      (h𝒩' _).1 (h𝒩' _).1 c hc
  have hciso : IsIso ((Over.pullback (jO O')).map c) := by
    have : IsIso ((Over.pullback (jO O')).map c ≫ 𝒩'.gen.hom) := by
      rw [hc]; exact Iso.isIso_hom N.gen
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ (Iso.isIso_hom 𝒩'.gen) this
  letI : GrpObj (bcO hO 𝒩.G) := Functor.grpObjObj
  have hW : IsOpen (idCompSet (bcO hO 𝒩.G)) := h3 _ (bcO hO 𝒩.G)
  let W : (bcO hO 𝒩.G).left.Opens := ⟨idCompSet (bcO hO 𝒩.G), hW⟩
  obtain ⟨hWo, -⟩ := h7 K O K' O' hO A hss 𝒩 h𝒩 𝒩' h𝒩' c hcm hciso W rfl
  let g := Spec.map (CommRingCat.ofHom (comapHom hO))
  let k := (Over.pullback g).map i
  haveI : IsOpenImmersion i.left := hoi
  haveI : IsOpenImmersion k.left := ZInQ.H5Glue.isOpenImmersion_pullback_map _ i
  have hkmap : k.left = pullback.map U.hom g 𝒩.G.hom g i.left (𝟙 _) (𝟙 _) (by simp) (by simp) := by
    apply pullback.hom_ext <;> simp [k, Over.pullback_map_left]
  have hrk : Set.range k.left = Set.range W.ι := by
    rw [Scheme.Opens.range_ι, hkmap, Scheme.Pullback.range_map]
    have hga := ga K O A 𝒩 U i hoi hmi hcg hcs
    have hgb := gb K O K' O' hO 𝒩.G
    have hid : Set.range ((𝟙 (Spec (CommRingCat.of O')) : Spec (CommRingCat.of O') ⟶ _) :
        Spec (CommRingCat.of O') → Spec (CommRingCat.of O')) = Set.univ :=
      Set.range_eq_univ.mpr (fun x => ⟨x, rfl⟩)
    rw [hid, Set.preimage_univ, Set.inter_univ, hga]
    exact hgb
  refine ⟨k ≫ c, ?_, ?_⟩
  · show IsOpenImmersion (k.left ≫ c.left)
    have hfac := IsOpenImmersion.isoOfRangeEq_hom_fac k.left W.ι hrk
    generalize IsOpenImmersion.isoOfRangeEq k.left W.ι hrk = eW at hfac
    have e : k.left ≫ c.left = eW.hom ≫ (W.ι ≫ c.left) := by
      rw [← hfac]
      exact Category.assoc _ _ _
    rw [e]
    haveI := hWo
    infer_instance
  · letI : GrpObj ((Over.pullback g).obj U) := Functor.grpObjObj
    have hk : IsMonHom k := inferInstance
    exact @instIsMonHomComp _ _ _ _ _ _ _ _ _ _ _ hk hcm

end FromPrinted

/-- **SS2 from four printed-form leaves and three topological glue Props** (compiled):
`IdentityComponentGroupModel`, `OpenSubgroupIsIdComp`, `IdCompBaseChangeDVR`. -/
theorem semistableNeronBaseChange_of_printed'' (hB : BLR_1_2_4) (h3 : SGA3_VIB_3_10)
    (h7 : SGA7_IX_3_3) (hE : EGAIV_8_10_5_openImm) (g1 : IdentityComponentGroupModel)
    (ga : OpenSubgroupIsIdComp) (gb : IdCompBaseChangeDVR) :
    ZInQ.HeightSplit.SemistableNeronBaseChange :=
  semistableNeronBaseChange_of_printed' hB h3 h7 hE g1 (identityComponentFromPrinted_of ga gb)

/-! # Part S, continued: `IdentityComponentGroupModel` reduced to three topological glue Props

`OpenSub`: an open `W` of a group scheme `G` closed under the group law carries a group structure making
`W → G` a homomorphism (`GrpObj.ofRepresentableBy` with the presheaf `T ↦ {f : T ⟶ G | f(T) ⊆ W}`). -/

namespace OpenSub

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] (W : G.left.Opens)

/-- Closure of an open set under the group law of `G`. -/
structure IsSubgroupOpen : Prop where
  one : ∀ s, (η[G] : 𝟙_ (Over S) ⟶ G).left s ∈ W
  mul : ∀ z : (G ⊗ G).left, (fst G G).left z ∈ W → (snd G G).left z ∈ W → (μ[G]).left z ∈ W
  inv : ∀ x : G.left, x ∈ W → (GrpObj.inv : G ⟶ G).left x ∈ W

variable {G W}

theorem mem_of_range {T : Over S} {f : T ⟶ G} (h : Set.range f.left ⊆ W) (t : T.left) :
    f.left t ∈ W := h ⟨t, rfl⟩

/-- The maps `T ⟶ G` landing in `W`, a subgroup. -/
def subHom (hW : IsSubgroupOpen G W) (T : Over S) : Subgroup (T ⟶ G) where
  carrier := {f | Set.range f.left ⊆ W}
  one_mem' := by
    rintro _ ⟨t, rfl⟩
    rw [Hom.one_def, Over.comp_left, Scheme.Hom.comp_apply]
    exact hW.one _
  mul_mem' := by
    intro f g hf hg
    rintro _ ⟨t, rfl⟩
    simp only [Set.mem_ofPred_eq] at hf hg
    rw [Hom.mul_def, Over.comp_left, Scheme.Hom.comp_apply]
    refine hW.mul _ ?_ ?_
    · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_fst]
      exact mem_of_range hf t
    · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_snd]
      exact mem_of_range hg t
  inv_mem' := by
    intro f hf
    rintro _ ⟨t, rfl⟩
    simp only [Set.mem_ofPred_eq] at hf
    rw [Hom.inv_def, Over.comp_left, Scheme.Hom.comp_apply]
    exact hW.inv _ (mem_of_range hf t)

/-- Precomposition, as a group homomorphism. -/
def subHomMap (hW : IsSubgroupOpen G W) {T T' : Over S} (h : T' ⟶ T) :
    subHom hW T →* subHom hW T' where
  toFun f := ⟨h ≫ f.1, by
    rintro _ ⟨t, rfl⟩
    rw [Over.comp_left, Scheme.Hom.comp_apply]
    exact mem_of_range f.2 _⟩
  map_one' := by
    apply Subtype.ext
    simp [Hom.one_def]
  map_mul' f g := by
    apply Subtype.ext
    simp [MonObj.comp_mul]

/-- The presheaf of groups `T ↦ {f : T ⟶ G | f(T) ⊆ W}`. -/
noncomputable def subFunctor (hW : IsSubgroupOpen G W) : (Over S)ᵒᵖ ⥤ GrpCat.{0} where
  obj T := GrpCat.of (subHom hW T.unop)
  map h := GrpCat.ofHom (subHomMap hW h.unop)
  map_id T := by
    ext f
    simp [subHomMap]
  map_comp h h' := by
    ext f
    simp [subHomMap]

variable (W) in
/-- The open subscheme on `W`, over `S`. -/
noncomputable abbrev G0 : Over S := Over.mk (W.ι ≫ G.hom)

variable (W) in
/-- Its inclusion into `G`. -/
noncomputable abbrev incl : G0 W ⟶ G := Over.homMk W.ι rfl

/-- Maps into `G0` are maps into `G` landing in `W`. -/
noncomputable def reprBy (hW : IsSubgroupOpen G W) :
    (subFunctor hW ⋙ forget GrpCat).RepresentableBy (G0 W) where
  homEquiv {T} :=
    { toFun := fun f => (⟨f ≫ incl W, by
        rintro _ ⟨t, rfl⟩
        rw [Over.comp_left, Scheme.Hom.comp_apply]
        have hm : W.ι (f.left t) ∈ Set.range W.ι := ⟨_, rfl⟩
        rw [Scheme.Opens.range_ι] at hm
        exact hm⟩ : subHom hW T)
      invFun := fun g => Over.homMk (IsOpenImmersion.lift W.ι g.1.left (by
          rw [Scheme.Opens.range_ι]; exact g.2)) (by
          simp only [G0, Over.mk_hom]
          rw [← Category.assoc, IsOpenImmersion.lift_fac, Over.w])
      left_inv := fun f => by
        apply Over.OverMorphism.ext
        simp only [Over.homMk_left]
        rw [← cancel_mono W.ι, IsOpenImmersion.lift_fac]
        rfl
      right_inv := fun g => by
        apply Subtype.ext
        apply Over.OverMorphism.ext
        simp only [Over.comp_left, Over.homMk_left]
        exact IsOpenImmersion.lift_fac _ _ _ }
  homEquiv_comp f g := Subtype.ext (Category.assoc f g (incl W))

/-- The group structure on `G0 W` (from `GrpObj.ofRepresentableBy`). -/
@[instance_reducible] noncomputable def grpG0 (hW : IsSubgroupOpen G W) : GrpObj (G0 W) :=
  GrpObj.ofRepresentableBy (G0 W) (subFunctor hW) (reprBy hW)

/-- The inclusion `G0 W → G` is a homomorphism. -/
theorem isMonHom_incl (hW : IsSubgroupOpen G W) :
    letI := grpG0 hW
    IsMonHom (incl W) := by
  letI := grpG0 hW
  constructor
  · have h1 : η[G0 W] ≫ incl W = ((reprBy hW).homEquiv η[G0 W]).1 := rfl
    have h2 : η[G0 W] = (reprBy hW).homEquiv.symm 1 := rfl
    rw [h1, h2, Equiv.apply_symm_apply]
    show (1 : 𝟙_ (Over S) ⟶ G) = η[G]
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  · have h1 : μ[G0 W] ≫ incl W = ((reprBy hW).homEquiv μ[G0 W]).1 := rfl
    have h2 : μ[G0 W] = (reprBy hW).homEquiv.symm
        ((reprBy hW).homEquiv (fst (G0 W) (G0 W)) * (reprBy hW).homEquiv (snd (G0 W) (G0 W))) := rfl
    rw [h1, h2, Equiv.apply_symm_apply]
    show ((fst (G0 W) (G0 W) ≫ incl W) * (snd (G0 W) (G0 W) ≫ incl W) : G0 W ⊗ G0 W ⟶ G) =
      (incl W ⊗ₘ incl W) ≫ μ[G]
    rw [Hom.mul_def]
    congr 1

end OpenSub

section IdCompGM

open ZInQ.HeightSplit ZInQ.DefFaltings

/-- `e(s) ∈ G⁰`. -/
theorem idCompSet_one {S : Scheme.{0}} (G : Over S) [GrpObj G] (s : S) :
    (η[G] : 𝟙_ (Over S) ⟶ G).left s ∈ idCompSet G := by
  have h : G.hom ((η[G] : 𝟙_ (Over S) ⟶ G).left s) = s := by
    rw [← Scheme.Hom.comp_apply, Over.w]
    rfl
  show _ ∈ connectedComponentIn _ _
  rw [h]
  exact mem_connectedComponentIn (show _ ∈ G.hom ⁻¹' {s} from h)

/-- **GLUE `IdCompSubgroup`** (SGA 3 VI_A 2.3 fibrewise): for a smooth quasi-compact group scheme `G` over a
noetherian scheme `S`, `G⁰` is closed under the group law. (Proved below, `idCompSubgroup_of`, from SGA 3 VI_B 3.10
and the bundle leaf `geomConnOfRationalPoint`.) Needs: the fibre of `G ×_S G` over `s` is `G_s ×_{κ(s)} G_s`, and `(G_s)⁰ ×_{κ(s)} (G_s)⁰` is
connected (`(G_s)⁰` is geometrically connected, Stacks 04KV = bundle leaf `geomConnOfRationalPoint`; a product
of a connected and a geometrically connected scheme is connected, Stacks 0385), so its image under `μ` is a
connected subset of `G_s` containing `e(s)`; likewise for the inverse (a homeomorphism of `G_s` fixing
`e(s)`). Not in Lean. -/
def IdCompSubgroup : Prop :=
  ∀ (S : Scheme.{0}) [IsNoetherian S] (G : Over S) [GrpObj G] [Smooth G.hom] [QuasiCompact G.hom],
    (∀ z : (G ⊗ G).left, (fst G G).left z ∈ idCompSet G → (snd G G).left z ∈ idCompSet G →
      (μ[G]).left z ∈ idCompSet G) ∧
    (∀ x : G.left, x ∈ idCompSet G → (GrpObj.inv : G ⟶ G).left x ∈ idCompSet G)

/-- **GLUE `IdCompGenericFibre`**: for a group model `𝒢` of `A_L` over `𝓞_L`, every point over the generic
point lies in `𝒢⁰`. Needs: the subspace `𝒢.hom⁻¹{η}` is homeomorphic to the generic fibre `𝒢_L ≅ A_L`
(EGA I 3.6.1; Mathlib's `Scheme.Hom.fiber`), which is connected (`A_L` geometrically integral). Not in Lean. -/
def IdCompGenericFibre : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (x : 𝒢.G.left), (𝒢.G.hom x).asIdeal = ⊥ → x ∈ idCompSet 𝒢.G

/-- **GLUE `IdCompGeomFibres`**: for a group model `𝒢` over `𝓞_L` and an open `W = 𝒢⁰`, the geometric fibre of
the open subscheme `W` at a maximal ideal is connected. Needs: the fibre of `W` at `𝔭` is `(𝒢_𝔭)⁰`, connected with
a rational point, hence geometrically connected (bundle leaf `geomConnOfRationalPoint`, Stacks 04KV). Not in
Lean. -/
def IdCompGeomFibres : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (W : 𝒢.G.left.Opens), (W : Set 𝒢.G.left) = idCompSet 𝒢.G →
    ∀ (𝔭 : Ideal (𝓞 L)) [𝔭.IsMaximal], ConnectedSpace ((Over.pullback (Spec.map (CommRingCat.ofHom
      (algebraMap (𝓞 L) (ResBar 𝔭))))).obj (Over.mk (W.ι ≫ 𝒢.G.hom))).left

/-- **`IdentityComponentGroupModel` from the three topological glue Props** (compiled): the open subscheme on
`𝒢⁰` with the group structure of `OpenSub`; smooth, separated, quasi-compact (`𝒢` is noetherian); its generic
fibre is that of `𝒢` (the inclusion is an open immersion, surjective on the generic fibre). -/
theorem identityComponentGroupModel_of (gc : IdCompSubgroup) (ge : IdCompGenericFibre)
    (gf : IdCompGeomFibres) : IdentityComponentGroupModel := by
  intro K _ A L _ _ _ 𝒢 hO
  let W : 𝒢.G.left.Opens := ⟨idCompSet 𝒢.G, hO⟩
  have hW : OpenSub.IsSubgroupOpen 𝒢.G W :=
    { one := fun s => idCompSet_one 𝒢.G s
      mul := (gc _ 𝒢.G).1
      inv := (gc _ 𝒢.G).2 }
  letI : GrpObj (OpenSub.G0 W) := OpenSub.grpG0 hW
  have hmon : IsMonHom (OpenSub.incl W) := OpenSub.isMonHom_incl hW
  haveI : Smooth (OpenSub.G0 W).hom := show Smooth (W.ι ≫ 𝒢.G.hom) from inferInstance
  haveI : IsSeparated (OpenSub.G0 W).hom := show IsSeparated (W.ι ≫ 𝒢.G.hom) from inferInstance
  haveI : QuasiCompact (OpenSub.G0 W).hom := by
    haveI : IsLocallyNoetherian 𝒢.G.left := LocallyOfFiniteType.isLocallyNoetherian 𝒢.G.hom
    haveI : CompactSpace 𝒢.G.left := QuasiCompact.compactSpace_of_compactSpace 𝒢.G.hom
    haveI : IsNoetherian 𝒢.G.left := {}
    show QuasiCompact (W.ι ≫ 𝒢.G.hom)
    infer_instance
  let jL := Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L))
  have hmap : ((Over.pullback jL).map (OpenSub.incl W)).left =
      pullback.map (W.ι ≫ 𝒢.G.hom) jL 𝒢.G.hom jL W.ι (𝟙 _) (𝟙 _) (by simp) (by simp) := by
    apply pullback.hom_ext <;> simp [Over.pullback_map_left]
  haveI : IsOpenImmersion (OpenSub.incl W).left := show IsOpenImmersion W.ι from inferInstance
  have hiso : IsIso ((Over.pullback jL).map (OpenSub.incl W)).left := by
    rw [isIso_iff_isOpenImmersion_and_surjective]
    refine ⟨ZInQ.H5Glue.isOpenImmersion_pullback_map _ _, ⟨fun z => ?_⟩⟩
    have hz : z ∈ Set.range ((Over.pullback jL).map (OpenSub.incl W)).left := by
      rw [hmap, Scheme.Pullback.range_map]
      refine ⟨?_, ⟨pullback.snd 𝒢.G.hom jL z, rfl⟩⟩
      show pullback.fst 𝒢.G.hom jL z ∈ Set.range W.ι
      rw [Scheme.Opens.range_ι]
      apply ge K A L 𝒢
      have h1 : 𝒢.G.hom (pullback.fst 𝒢.G.hom jL z) = jL (pullback.snd 𝒢.G.hom jL z) := by
        rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
      rw [h1]
      set p := pullback.snd 𝒢.G.hom jL z
      have hp : p.asIdeal = ⊥ :=
        (Ideal.eq_bot_or_top p.asIdeal).resolve_right p.isPrime.ne_top
      show Ideal.comap (algebraMap (𝓞 L) L) p.asIdeal = ⊥
      rw [hp]
      exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 L) L)
    exact hz
  haveI : IsIso ((Over.forget _).map ((Over.pullback jL).map (OpenSub.incl W))) := hiso
  haveI : IsIso ((Over.pullback jL).map (OpenSub.incl W)) :=
    isIso_of_reflects_iso _ (Over.forget _)
  let e := asIso ((Over.pullback jL).map (OpenSub.incl W))
  haveI := hmon
  let 𝒢₀ : GroupModel A L :=
    { G := OpenSub.G0 W
      gen := e ≪≫ 𝒢.gen
      gen_hom := by
        letI : GrpObj (genericFibre L (OpenSub.G0 W)) := Functor.grpObjObj
        letI : GrpObj (genericFibre L 𝒢.G) := Functor.grpObjObj
        letI : GrpObj ((Over.pullback jL).obj (OpenSub.G0 W)) := Functor.grpObjObj
        letI : GrpObj ((Over.pullback jL).obj 𝒢.G) := Functor.grpObjObj
        have h1 : IsMonHom ((Over.pullback jL).map (OpenSub.incl W)) := inferInstance
        exact @instIsMonHomComp _ _ _ _ _ _ _ _ _ _ _ h1 𝒢.gen_hom }
  exact ⟨𝒢₀, OpenSub.incl W, inferInstanceAs (IsOpenImmersion W.ι), hmon,
    fun 𝔭 _ => gf K A L 𝒢 W rfl 𝔭⟩

end IdCompGM

open ZInQ.HeightSplit ZInQ.DefFaltings in
/-- **The glue `IdCompGenericFibre`, PROVED.** The generic fibre `𝒢 ×_{𝓞_L} L ≅ A_L` is connected, its image in
`𝒢` is the set of points over the generic point (`range_fst`), and that image is a connected set containing
`e(η)`, so it lies in the connected component of `e(η)` in the fibre. -/
theorem idCompGenericFibre : IdCompGenericFibre := by
  intro K _ A L _ _ _ 𝒢 x hx
  let jL := Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L))
  have hbot : ∀ p : Spec (CommRingCat.of L), (jL p).asIdeal = ⊥ := by
    intro p
    have hp : p.asIdeal = ⊥ := (Ideal.eq_bot_or_top p.asIdeal).resolve_right p.isPrime.ne_top
    show Ideal.comap (algebraMap (𝓞 L) L) p.asIdeal = ⊥
    rw [hp]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 L) L)
  -- the generic fibre is connected
  haveI : IrreducibleSpace (A.baseChange L).X.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton (A.baseChange L).X.hom
  haveI hc : ConnectedSpace (genericFibre L 𝒢.G).left :=
    (Scheme.homeoOfIso ((Over.forget _).mapIso 𝒢.gen)).connectedSpace_iff.mpr
      (inferInstanceAs (ConnectedSpace (A.baseChange L).X.left))
  have hc' : ConnectedSpace ↥(pullback 𝒢.G.hom jL : Scheme.{0}) := hc
  -- its image
  set R := Set.range (pullback.fst 𝒢.G.hom jL)
  have hR : _root_.IsPreconnected R := (isConnected_range (pullback.fst 𝒢.G.hom jL).continuous).isPreconnected
  have hsub : R ⊆ 𝒢.G.hom ⁻¹' {𝒢.G.hom x} := by
    rintro _ ⟨z, rfl⟩
    show 𝒢.G.hom (pullback.fst 𝒢.G.hom jL z) = 𝒢.G.hom x
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    exact PrimeSpectrum.ext ((hbot _).trans hx.symm)
  have hmem : ∀ y : 𝒢.G.left, (𝒢.G.hom y).asIdeal = ⊥ → y ∈ R := by
    intro y hy
    show y ∈ Set.range (pullback.fst 𝒢.G.hom jL)
    rw [Scheme.Pullback.range_fst]
    refine ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
    exact PrimeSpectrum.ext ((hbot _).trans hy.symm)
  have he : (η[𝒢.G] : 𝟙_ (Over (Spec (CommRingCat.of (𝓞 L)))) ⟶ 𝒢.G).left (𝒢.G.hom x) ∈ R := by
    apply hmem
    have h : 𝒢.G.hom ((η[𝒢.G] : 𝟙_ (Over (Spec (CommRingCat.of (𝓞 L)))) ⟶ 𝒢.G).left
        (𝒢.G.hom x)) = 𝒢.G.hom x := by
      rw [← Scheme.Hom.comp_apply, Over.w]
      rfl
    rw [h]
    exact hx
  exact hR.subset_connectedComponentIn he hsub (hmem x hx)

/-- **`G⁰ → S` is geometrically connected** (from the bundle leaf `AVGlue.GeomConnOfRationalPoint`, Stacks
04KV). `G` a group scheme over `S`, `W = G⁰` open with `W → S` locally of finite type and quasi-compact. At every
`y ∈ S` the fibre of `W` is homeomorphic (`fiberHomeo`) to the connected component of `e(y)` in `G_y`, so it is
connected; it has the rational point `e(y)` and is of finite type, so it is geometrically connected; conclude by
`GeometricallyConnected.iff_geometricallyConnected_fiber`. -/
theorem geomConnected_idComp (hG : AVGlue.GeomConnOfRationalPoint) {S : Scheme.{0}}
    (G : Over S) [GrpObj G] (W : G.left.Opens) (hW : (W : Set G.left) = idCompSet G)
    [LocallyOfFiniteType (W.ι ≫ G.hom)] [QuasiCompact (W.ι ≫ G.hom)] :
    GeometricallyConnected (W.ι ≫ G.hom) := by
  rw [GeometricallyConnected.iff_geometricallyConnected_fiber]
  intro y
  let f0 : W.toScheme ⟶ S := W.ι ≫ G.hom
  -- the fibre of `f0` over `y` is connected
  have hT : _root_.IsConnected (f0 ⁻¹' {y}) := by
    let C := connectedComponentIn (G.hom ⁻¹' {y})
      ((η[G] : 𝟙_ (Over S) ⟶ G).left y)
    have hey : (η[G] : 𝟙_ (Over S) ⟶ G).left y ∈ G.hom ⁻¹' {y} := by
      show G.hom ((η[G] : 𝟙_ (Over S) ⟶ G).left y) = y
      rw [← Scheme.Hom.comp_apply, Over.w]
      rfl
    have hC : _root_.IsConnected C := isConnected_connectedComponentIn_iff.mpr hey
    have himg : W.ι '' (f0 ⁻¹' {y}) = C := by
      ext x
      constructor
      · rintro ⟨w, hw, rfl⟩
        have hw' : G.hom (W.ι w) = y := hw
        have hmem : W.ι w ∈ idCompSet G := by
          rw [← hW]
          have : W.ι w ∈ Set.range W.ι := ⟨w, rfl⟩
          rwa [Scheme.Opens.range_ι] at this
        have h2 : W.ι w ∈ connectedComponentIn (G.hom ⁻¹' {G.hom (W.ι w)})
            ((η[G] : 𝟙_ (Over S) ⟶ G).left (G.hom (W.ι w))) := hmem
        rw [hw'] at h2
        exact h2
      · intro hx
        have hxy : G.hom x = y := connectedComponentIn_subset (G.hom ⁻¹' {y}) _ hx
        have hmem : x ∈ idCompSet G := by
          show x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x})
            ((η[G] : 𝟙_ (Over S) ⟶ G).left (G.hom x))
          rw [hxy]
          exact hx
        have hxW : x ∈ Set.range W.ι := by rw [Scheme.Opens.range_ι, hW]; exact hmem
        obtain ⟨w, rfl⟩ := hxW
        exact ⟨w, hxy, rfl⟩
    rw [← himg] at hC
    exact ⟨hC.1.of_image, (W.ι.isOpenEmbedding.isInducing.isPreconnected_image).mp hC.2⟩
  haveI : ConnectedSpace (f0 ⁻¹' {y}) := isConnected_iff_connectedSpace.mp hT
  haveI hconn : ConnectedSpace (f0.fiber y) := (f0.fiberHomeo y).connectedSpace_iff.mpr inferInstance
  -- the rational point
  have hη : Set.range (η[G] : 𝟙_ (Over S) ⟶ G).left ⊆ Set.range W.ι := by
    rintro _ ⟨s, rfl⟩
    rw [Scheme.Opens.range_ι, hW]
    exact idCompSet_one G s
  let eW : S ⟶ W.toScheme := IsOpenImmersion.lift W.ι (η[G] : 𝟙_ (Over S) ⟶ G).left hη
  have heW : eW ≫ f0 = 𝟙 S := by
    show eW ≫ W.ι ≫ G.hom = 𝟙 S
    rw [← Category.assoc, IsOpenImmersion.lift_fac, Over.w]
    rfl
  let sec : Spec (S.residueField y) ⟶ f0.fiber y :=
    pullback.lift (S.fromSpecResidueField y ≫ eW) (𝟙 _) (by
      rw [Category.assoc, heW, Category.comp_id, Category.id_comp])
  have hsec : sec ≫ f0.fiberToSpecResidueField y = 𝟙 _ := pullback.lift_snd _ _ _
  exact hG (S.residueField y) (f0.fiber y) (f0.fiberToSpecResidueField y) sec hsec
      (show LocallyOfFiniteType (pullback.snd f0 (S.fromSpecResidueField y)) from inferInstance)
      (show QuasiCompact (pullback.snd f0 (S.fromSpecResidueField y)) from inferInstance) hconn

/-- **The base change of `G⁰` to a field is connected** (`geomConnected_idComp`). -/
theorem connectedSpace_pullback_idComp (hG : AVGlue.GeomConnOfRationalPoint) {S : Scheme.{0}}
    (G : Over S) [GrpObj G] (W : G.left.Opens) (hW : (W : Set G.left) = idCompSet G)
    [LocallyOfFiniteType (W.ι ≫ G.hom)] [QuasiCompact (W.ι ≫ G.hom)] (K : Type) [Field K]
    (g : Spec (CommRingCat.of K) ⟶ S) : ConnectedSpace ↥(pullback (W.ι ≫ G.hom) g) := by
  exact (geomConnected_idComp hG G W hW).geometrically_connectedSpace g (pullback.fst _ _)
    (pullback.snd _ _) (IsPullback.of_hasPullback _ _)

open ZInQ.HeightSplit ZInQ.DefFaltings in
/-- **The glue `IdCompGeomFibres`, PROVED from the bundle leaf `AVGlue.GeomConnOfRationalPoint`** (Stacks
04KV), by `connectedSpace_pullback_idComp` at `Spec κ̄(𝔭) → Spec 𝓞_L`. -/
theorem idCompGeomFibres (hG : AVGlue.GeomConnOfRationalPoint) : IdCompGeomFibres := by
  intro K _ A L _ _ _ 𝒢 W hW 𝔭 _
  haveI : IsLocallyNoetherian 𝒢.G.left := LocallyOfFiniteType.isLocallyNoetherian 𝒢.G.hom
  haveI : CompactSpace 𝒢.G.left := QuasiCompact.compactSpace_of_compactSpace 𝒢.G.hom
  haveI : IsNoetherian 𝒢.G.left := {}
  exact connectedSpace_pullback_idComp hG 𝒢.G W hW (ResBar 𝔭)
    (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (ResBar 𝔭))))

/-- The unit of a base change of a group scheme, followed by the projection, is the unit composed with the
base change map. -/
theorem unit_bc_fst {S S' : Scheme.{0}} (g : S' ⟶ S) (G : Over S) [GrpObj G] :
    letI : GrpObj ((Over.pullback g).obj G) := Functor.grpObjObj
    (η[(Over.pullback g).obj G] : 𝟙_ (Over S') ⟶ _).left ≫ pullback.fst G.hom g =
      g ≫ (η[G] : 𝟙_ (Over S) ⟶ G).left := by
  letI : GrpObj ((Over.pullback g).obj G) := Functor.grpObjObj
  have h1 : (η[(Over.pullback g).obj G] : 𝟙_ (Over S') ⟶ _) =
      Functor.LaxMonoidal.ε (Over.pullback g) ≫ (Over.pullback g).map η[G] := rfl
  rw [h1, Over.comp_left, Category.assoc]
  simp only [Over.pullback_map_left, pullback.lift_fst]
  have hw := Over.w (Functor.LaxMonoidal.ε (Over.pullback g))
  have hc : pullback.fst (𝟙_ (Over S)).hom g = pullback.snd (𝟙_ (Over S)).hom g ≫ g := by
    rw [← pullback.condition]; exact (Category.comp_id _).symm
  rw [← Category.assoc, hc, ← Category.assoc]
  erw [hw]
  exact congrArg (· ≫ _) (Category.id_comp g)

/-- **The identity component commutes with base change** (SGA 3 VI_B 3.3; PROVED here from the printed
SGA 3 VI_B 3.10 and the bundle leaf `AVGlue.GeomConnOfRationalPoint`, Stacks 04KV), for a smooth quasi-compact
group scheme over a noetherian scheme and any base change `g : S' → S`. For `s' ∈ S'`, the set
`P = {w : fst w ∈ G⁰, w over s'}` is the image of `G⁰ ×_S Spec κ(s')`, which is connected
(`connectedSpace_pullback_idComp`), so `P ⊆ (G ×_S S')⁰`; conversely the image under `fst` of the component of
`e'(s')` is a connected subset of `G_{g(s')}` containing `e(g(s'))`. -/
theorem idComp_baseChange (h3 : SGA3_VIB_3_10) (hG : AVGlue.GeomConnOfRationalPoint)
    {S S' : Scheme.{0}} [IsNoetherian S] (g : S' ⟶ S) (G : Over S) [GrpObj G] [Smooth G.hom]
    [QuasiCompact G.hom] :
    letI : GrpObj ((Over.pullback g).obj G) := Functor.grpObjObj
    pullback.fst G.hom g ⁻¹' idCompSet G = idCompSet ((Over.pullback g).obj G) := by
  letI : GrpObj ((Over.pullback g).obj G) := Functor.grpObjObj
  let W : G.left.Opens := ⟨idCompSet G, h3 S G⟩
  have hW : (W : Set G.left) = idCompSet G := rfl
  haveI : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  haveI : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  haveI : IsNoetherian G.left := {}
  let e' := (η[(Over.pullback g).obj G] : 𝟙_ (Over S') ⟶ _).left
  let e := (η[G] : 𝟙_ (Over (S)) ⟶ G).left
  have hu1 : ∀ s', pullback.fst G.hom g (e' s') = e (g s') := by
    intro s'
    rw [← Scheme.Hom.comp_apply, unit_bc_fst g G, Scheme.Hom.comp_apply]
  have hu2 : ∀ s', pullback.snd G.hom g (e' s') = s' := by
    intro s'
    show ((Over.pullback g).obj G).hom (e' s') = s'
    rw [← Scheme.Hom.comp_apply, Over.w]
    rfl
  have hfib : ∀ w : ((Over.pullback g).obj G).left, G.hom (pullback.fst G.hom g w) = g (pullback.snd G.hom g w) := by
    intro w
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  -- the sets `P s'` are preconnected
  have hP : ∀ s' : S', _root_.IsPreconnected
      {w : ((Over.pullback g).obj G).left | pullback.fst G.hom g w ∈ W ∧ pullback.snd G.hom g w = s'} := by
    intro s'
    let f0 := W.ι ≫ G.hom
    let m2 := pullback.map f0 g G.hom g W.ι (𝟙 _) (𝟙 _) (by simp [f0]) (by simp)
    let r := (S').fromSpecResidueField s'
    let m1 := pullback.fst (pullback.snd f0 g) r
    haveI hc : ConnectedSpace ↥(pullback f0 (r ≫ g)) :=
      connectedSpace_pullback_idComp hG G W hW
        (↑((S').residueField s')) (r ≫ g)
    haveI : ConnectedSpace ↥(pullback (pullback.snd f0 g) r) :=
      (Scheme.homeoOfIso (pullbackLeftPullbackSndIso f0 g r)).connectedSpace_iff.mpr hc
    have hrange : Set.range (m1 ≫ m2) =
        {w : ((Over.pullback g).obj G).left | pullback.fst G.hom g w ∈ W ∧ pullback.snd G.hom g w = s'} := by
      ext w
      constructor
      · rintro ⟨u, rfl⟩
        constructor
        · rw [← Scheme.Hom.comp_apply, Category.assoc, pullback.lift_fst, ← Category.assoc,
            Scheme.Hom.comp_apply]
          have : W.ι ((m1 ≫ pullback.fst f0 g) u) ∈ Set.range W.ι := ⟨_, rfl⟩
          rwa [Scheme.Opens.range_ι] at this
        · rw [← Scheme.Hom.comp_apply, Category.assoc, pullback.lift_snd, Category.comp_id,
            pullback.condition, Scheme.Hom.comp_apply]
          have : r (pullback.snd (pullback.snd f0 g) r u) ∈ Set.range r := ⟨_, rfl⟩
          rwa [Scheme.range_fromSpecResidueField] at this
      · rintro ⟨h1, h2⟩
        have hw : w ∈ Set.range m2 := by
          rw [Scheme.Pullback.range_map]
          refine ⟨?_, ⟨pullback.snd G.hom g w, rfl⟩⟩
          show pullback.fst G.hom g w ∈ Set.range W.ι
          rw [Scheme.Opens.range_ι]
          exact h1
        obtain ⟨v, rfl⟩ := hw
        have hv : pullback.snd f0 g v ∈ Set.range r := by
          rw [Scheme.range_fromSpecResidueField]
          have : (m2 ≫ pullback.snd G.hom g) v = s' := h2
          rw [pullback.lift_snd, Category.comp_id] at this
          exact this
        have hv' : v ∈ Set.range m1 := by
          rw [Scheme.Pullback.range_fst]
          exact hv
        obtain ⟨u, rfl⟩ := hv'
        exact ⟨u, rfl⟩
    rw [← hrange]
    exact (isConnected_range (m1 ≫ m2).continuous).isPreconnected
  ext z
  constructor
  · intro hz
    let s' := pullback.snd G.hom g z
    show z ∈ connectedComponentIn (((Over.pullback g).obj G).hom ⁻¹' {((Over.pullback g).obj G).hom z}) (e' (((Over.pullback g).obj G).hom z))
    refine (hP s').subset_connectedComponentIn ⟨?_, hu2 s'⟩ ?_ ⟨hz, rfl⟩
    · rw [hu1]
      exact idCompSet_one G (g s')
    · rintro w ⟨-, hw⟩
      exact hw
  · intro hz
    let s' := pullback.snd G.hom g z
    have hz' : z ∈ connectedComponentIn (pullback.snd G.hom g ⁻¹' {s'}) (e' s') := hz
    set C := connectedComponentIn (pullback.snd G.hom g ⁻¹' {s'}) (e' s')
    have hC : _root_.IsPreconnected (pullback.fst G.hom g '' C) :=
      isPreconnected_connectedComponentIn.image _ (pullback.fst G.hom g).continuous.continuousOn
    have hsub : pullback.fst G.hom g '' C ⊆ G.hom ⁻¹' {g s'} := by
      rintro _ ⟨w, hw, rfl⟩
      show G.hom (pullback.fst G.hom g w) = g s'
      rw [hfib]
      exact congrArg g (connectedComponentIn_subset (pullback.snd G.hom g ⁻¹' {s'}) _ hw)
    have hmem : e (g s') ∈ pullback.fst G.hom g '' C :=
      ⟨e' s', mem_connectedComponentIn (hu2 s'), hu1 s'⟩
    have := hC.subset_connectedComponentIn hmem hsub ⟨z, hz', rfl⟩
    show pullback.fst G.hom g z ∈ connectedComponentIn (G.hom ⁻¹' {G.hom (pullback.fst G.hom g z)})
      (e (G.hom (pullback.fst G.hom g z)))
    rw [hfib]
    exact this

/-- **The glue `IdCompBaseChangeDVR`, PROVED** (`idComp_baseChange` at `Spec O' → Spec O`). -/
theorem idCompBaseChangeDVR_of (h3 : SGA3_VIB_3_10) (hG : AVGlue.GeomConnOfRationalPoint) :
    IdCompBaseChangeDVR := by
  intro K _ O _ K' _ _ _ O' _ hO G _ _ _
  exact idComp_baseChange h3 hG (Spec.map (CommRingCat.ofHom (ReductSplit.comapHom hO))) G

/-- **The glue `IdCompSubgroup`, PROVED** from the printed SGA 3 VI_B 3.10 and the bundle leaf
`AVGlue.GeomConnOfRationalPoint`. `W = G⁰ → S` is geometrically connected (`geomConnected_idComp`), hence so is
`W ×_S W → S` (base change and composition), so the points of `W ×_S W` over `s` form a connected set; its image
under `μ` is connected, lies in `G_s` and contains `μ(e, e) = e(s)`. For the inverse, `ι` maps the component of
`e(s)` to a connected set containing `ι(e(s)) = e(s)`. -/
theorem idCompSubgroup_of (h3 : SGA3_VIB_3_10) (hG : AVGlue.GeomConnOfRationalPoint) :
    IdCompSubgroup := by
  intro S _ G _ _ _
  let W : G.left.Opens := ⟨idCompSet G, h3 S G⟩
  haveI : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  haveI : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  haveI : IsNoetherian G.left := {}
  let f0 : W.toScheme ⟶ S := W.ι ≫ G.hom
  haveI : GeometricallyConnected f0 := geomConnected_idComp hG G W rfl
  let e := (η[G] : 𝟙_ (Over S) ⟶ G).left
  have he : ∀ s, G.hom (e s) = s := by
    intro s
    rw [← Scheme.Hom.comp_apply, Over.w]
    rfl
  constructor
  · intro z hz1 hz2
    let s := G.hom (pullback.fst G.hom G.hom z)
    let m := pullback.map f0 f0 G.hom G.hom W.ι W.ι (𝟙 _) (by simp [f0]) (by simp [f0])
    let f00 := pullback.snd f0 f0 ≫ f0
    haveI : GeometricallyConnected f00 := GeometricallyConnected.comp _ _
    have hc : _root_.IsConnected (f00 ⁻¹' {s}) := f00.isConnected_preimage_singleton s
    have hm : ∀ v, G.hom (pullback.fst G.hom G.hom (m v)) = f00 v := by
      intro v
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition,
        ← Category.assoc, pullback.lift_snd, Category.assoc]
    let μl := (μ[G] : G ⊗ G ⟶ G).left
    have hμ : ∀ w : (G ⊗ G).left, G.hom (μl w) = G.hom (pullback.fst G.hom G.hom w) := by
      intro w
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
      exact congrArg (fun h => h w) (congrArg (fun k => k.base) (Over.w (μ[G] : G ⊗ G ⟶ G)))
    let P := μl '' (m '' (f00 ⁻¹' {s}))
    have hP : _root_.IsPreconnected P :=
      (hc.isPreconnected.image _ m.continuous.continuousOn).image _ μl.continuous.continuousOn
    have hPsub : P ⊆ G.hom ⁻¹' {s} := by
      rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      show G.hom (μl (m v)) = s
      rw [hμ, hm]
      exact hv
    -- `e(s) ∈ P`
    have hη : Set.range e ⊆ Set.range W.ι := by
      rintro _ ⟨t, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact idCompSet_one G t
    let eW : S ⟶ W.toScheme := IsOpenImmersion.lift W.ι e hη
    have heW : eW ≫ W.ι = e := IsOpenImmersion.lift_fac _ _ _
    let v0 : S ⟶ pullback f0 f0 := pullback.lift eW eW rfl
    have hv0 : v0 ≫ m = (lift (η[G]) (η[G]) : 𝟙_ (Over S) ⟶ G ⊗ G).left := by
      apply pullback.hom_ext
      · simp [v0, m, heW, e]
      · simp [v0, m, heW, e]
    have hlift : lift (η[G]) (η[G]) ≫ μ[G] = (η[G] : 𝟙_ (Over S) ⟶ G) := by
      have := MonObj.lift_comp_one_left (𝟙 (𝟙_ (Over S))) (η[G] : 𝟙_ (Over S) ⟶ G)
      rwa [Category.id_comp] at this
    have hes : e s ∈ P := by
      refine ⟨m (v0 s), ⟨v0 s, ?_, rfl⟩, ?_⟩
      · show f00 (v0 s) = s
        have hlf : (lift (η[G]) (η[G]) : 𝟙_ (Over S) ⟶ G ⊗ G).left ≫ pullback.fst G.hom G.hom = e := by
          have h0 := congrArg CommaMorphism.left
            (CartesianMonoidalCategory.lift_fst (η[G] : 𝟙_ (Over S) ⟶ G) (η[G] : 𝟙_ (Over S) ⟶ G))
          exact h0
        rw [← hm, ← Scheme.Hom.comp_apply v0 m, hv0]
        show G.hom (pullback.fst G.hom G.hom
          ((lift (η[G]) (η[G]) : 𝟙_ (Over S) ⟶ G ⊗ G).left s)) = s
        rw [← Scheme.Hom.comp_apply (lift (η[G]) (η[G]) : 𝟙_ (Over S) ⟶ G ⊗ G).left
          (pullback.fst G.hom G.hom), hlf]
        exact he s
      · show μl (m (v0 s)) = e s
        rw [← Scheme.Hom.comp_apply v0 m, hv0, ← Scheme.Hom.comp_apply, ← Over.comp_left, hlift]
    -- `z ∈ m '' (f00⁻¹ {s})`
    have hz : z ∈ Set.range m := by
      rw [Scheme.Pullback.range_map]
      refine ⟨?_, ?_⟩
      · show pullback.fst G.hom G.hom z ∈ Set.range W.ι
        rw [Scheme.Opens.range_ι]; exact hz1
      · show pullback.snd G.hom G.hom z ∈ Set.range W.ι
        rw [Scheme.Opens.range_ι]; exact hz2
    obtain ⟨v, rfl⟩ := hz
    have hzP : μl (m v) ∈ P := ⟨m v, ⟨v, (hm v).symm, rfl⟩, rfl⟩
    have := hP.subset_connectedComponentIn hes hPsub hzP
    show μl (m v) ∈ connectedComponentIn (G.hom ⁻¹' {G.hom (μl (m v))}) (e (G.hom (μl (m v))))
    rw [hμ]
    exact this
  · intro x hx
    let ιl := (GrpObj.inv : G ⟶ G).left
    have hι : ∀ y, G.hom (ιl y) = G.hom y := by
      intro y
      rw [← Scheme.Hom.comp_apply, Over.w]
    let C := connectedComponentIn (G.hom ⁻¹' {G.hom x}) (e (G.hom x))
    have hC : _root_.IsPreconnected (ιl '' C) :=
      isPreconnected_connectedComponentIn.image _ ιl.continuous.continuousOn
    have hsub : ιl '' C ⊆ G.hom ⁻¹' {G.hom x} := by
      rintro _ ⟨y, hy, rfl⟩
      show G.hom (ιl y) = G.hom x
      rw [hι]
      exact connectedComponentIn_subset (G.hom ⁻¹' {G.hom x}) _ hy
    have hes : e (G.hom x) ∈ ιl '' C := by
      refine ⟨e (G.hom x), mem_connectedComponentIn (he _), ?_⟩
      show ιl (e (G.hom x)) = e (G.hom x)
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, GrpObj.one_inv]
    have := hC.subset_connectedComponentIn hes hsub ⟨x, hx, rfl⟩
    show ιl x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom (ιl x)}) (e (G.hom (ιl x)))
    rw [hι]
    exact this

/-- `IdentityComponentOL` (reduct-glue's SGA 3 leaf) from the printed SGA 3 VI_B 3.10 and the three
topological glue Props. -/
theorem identityComponentOL_of_printed' (h3 : SGA3_VIB_3_10) (gc : IdCompSubgroup)
    (ge : IdCompGenericFibre) (gf : IdCompGeomFibres) : ReductGlue.IdentityComponentOL :=
  identityComponentOL_of_printed h3 (identityComponentGroupModel_of gc ge gf)

/-- **SS2 from four printed-form leaves and five topological glue Props** (compiled). The glue left is about
the topology of the identity component of a group scheme: `IdCompSubgroup`, `IdCompGenericFibre`,
`IdCompGeomFibres`, `OpenSubgroupIsIdComp`, `IdCompBaseChangeDVR`. -/
theorem semistableNeronBaseChange_of_printed_final (hB : BLR_1_2_4) (h3 : SGA3_VIB_3_10)
    (h7 : SGA7_IX_3_3) (hE : EGAIV_8_10_5_openImm) (gc : IdCompSubgroup) (ge : IdCompGenericFibre)
    (gf : IdCompGeomFibres) (ga : OpenSubgroupIsIdComp) (gb : IdCompBaseChangeDVR) :
    ZInQ.HeightSplit.SemistableNeronBaseChange :=
  semistableNeronBaseChange_of_printed'' hB h3 h7 hE (identityComponentGroupModel_of gc ge gf) ga gb

/-- **SS2 from four printed-form leaves and four topological glue Props** (compiled; `IdCompGenericFibre` is
proved). -/
theorem semistableNeronBaseChange_of_printed_final' (hB : BLR_1_2_4) (h3 : SGA3_VIB_3_10)
    (h7 : SGA7_IX_3_3) (hE : EGAIV_8_10_5_openImm) (gc : IdCompSubgroup) (gf : IdCompGeomFibres)
    (ga : OpenSubgroupIsIdComp) (gb : IdCompBaseChangeDVR) :
    ZInQ.HeightSplit.SemistableNeronBaseChange :=
  semistableNeronBaseChange_of_printed_final hB h3 h7 hE gc idCompGenericFibre gf ga gb

/-- **SS2 from four printed-form leaves, the bundle leaf `AVGlue.GeomConnOfRationalPoint` (Stacks 04KV) and
three topological glue Props** (compiled): `IdCompSubgroup`, `OpenSubgroupIsIdComp`, `IdCompBaseChangeDVR`. -/
theorem semistableNeronBaseChange_of_printed_final'' (hB : BLR_1_2_4) (h3 : SGA3_VIB_3_10)
    (h7 : SGA7_IX_3_3) (hE : EGAIV_8_10_5_openImm) (hG : AVGlue.GeomConnOfRationalPoint)
    (gc : IdCompSubgroup) (ga : OpenSubgroupIsIdComp) (gb : IdCompBaseChangeDVR) :
    ZInQ.HeightSplit.SemistableNeronBaseChange :=
  semistableNeronBaseChange_of_printed_final' hB h3 h7 hE gc (idCompGeomFibres hG) ga gb

/-- **SS2 from four printed-form leaves, the bundle leaf `AVGlue.GeomConnOfRationalPoint` (Stacks 04KV) and
one topological glue Prop `OpenSubgroupIsIdComp`** (compiled; `IdCompSubgroup`, `IdCompGenericFibre`,
`IdCompGeomFibres`, `IdCompBaseChangeDVR` are proved). -/
theorem semistableNeronBaseChange_of_printed_best (hB : BLR_1_2_4) (h3 : SGA3_VIB_3_10)
    (h7 : SGA7_IX_3_3) (hE : EGAIV_8_10_5_openImm) (hG : AVGlue.GeomConnOfRationalPoint)
    (ga : OpenSubgroupIsIdComp) : ZInQ.HeightSplit.SemistableNeronBaseChange :=
  semistableNeronBaseChange_of_printed_final'' hB h3 h7 hE hG (idCompSubgroup_of h3 hG) ga
    (idCompBaseChangeDVR_of h3 hG)

/-! # Part S, final: SS2 from published-form leaves only

`OpenSubgroupIsIdComp` is avoided: the identity component group model `𝒢₀` built here has image exactly `𝒢⁰`
(`IdentityComponentOLRange`), the local SGA 7 IX 3.3 step is used in the form "open subgroup with image `𝒩⁰`"
(`IdentityComponentBaseChangeDVRRange`), and the image of `𝒢₀ ×_{𝓞_L} O` is `(𝒩 ×_{𝓞_L} O)⁰` by
`idComp_baseChange`. The global argument is reduct-glue's `semistableNeronBaseChangeLocalGlobal_of`, copied with
these two changes. -/

open ZInQ.HeightSplit ZInQ.DefFaltings in
/-- reduct-glue's `IdentityComponentOL` with the image of `𝒢₀` pinned down: `Set.range i = 𝒢⁰`. -/
def IdentityComponentOLRange : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L), ∃ (𝒢₀ : GroupModel A L) (i : 𝒢₀.G ⟶ 𝒢.G), IsOpenImmersion i.left ∧
      IsMonHom i ∧ Set.range i.left = idCompSet 𝒢.G

open ZInQ.HeightSplit ZInQ.DefFaltings in
/-- **`IdentityComponentOLRange`, PROVED** from SGA 3 VI_B 3.10 and the bundle leaf
`AVGlue.GeomConnOfRationalPoint` (the construction of `identityComponentGroupModel_of`). -/
theorem identityComponentOLRange_of (h3 : SGA3_VIB_3_10) (hG : AVGlue.GeomConnOfRationalPoint) :
    IdentityComponentOLRange := by
  intro K _ A L _ _ _ 𝒢
  have hO : IsOpen (idCompSet 𝒢.G) := h3 _ 𝒢.G
  have gc := idCompSubgroup_of h3 hG
  have ge := idCompGenericFibre
  let W : 𝒢.G.left.Opens := ⟨idCompSet 𝒢.G, hO⟩
  have hW : OpenSub.IsSubgroupOpen 𝒢.G W :=
    { one := fun s => idCompSet_one 𝒢.G s
      mul := (gc _ 𝒢.G).1
      inv := (gc _ 𝒢.G).2 }
  letI : GrpObj (OpenSub.G0 W) := OpenSub.grpG0 hW
  have hmon : IsMonHom (OpenSub.incl W) := OpenSub.isMonHom_incl hW
  haveI : Smooth (OpenSub.G0 W).hom := show Smooth (W.ι ≫ 𝒢.G.hom) from inferInstance
  haveI : IsSeparated (OpenSub.G0 W).hom := show IsSeparated (W.ι ≫ 𝒢.G.hom) from inferInstance
  haveI : QuasiCompact (OpenSub.G0 W).hom := by
    haveI : IsLocallyNoetherian 𝒢.G.left := LocallyOfFiniteType.isLocallyNoetherian 𝒢.G.hom
    haveI : CompactSpace 𝒢.G.left := QuasiCompact.compactSpace_of_compactSpace 𝒢.G.hom
    haveI : IsNoetherian 𝒢.G.left := {}
    show QuasiCompact (W.ι ≫ 𝒢.G.hom)
    infer_instance
  let jL := Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L))
  have hmap : ((Over.pullback jL).map (OpenSub.incl W)).left =
      pullback.map (W.ι ≫ 𝒢.G.hom) jL 𝒢.G.hom jL W.ι (𝟙 _) (𝟙 _) (by simp) (by simp) := by
    apply pullback.hom_ext <;> simp [Over.pullback_map_left]
  haveI : IsOpenImmersion (OpenSub.incl W).left := show IsOpenImmersion W.ι from inferInstance
  have hiso : IsIso ((Over.pullback jL).map (OpenSub.incl W)).left := by
    rw [isIso_iff_isOpenImmersion_and_surjective]
    refine ⟨ZInQ.H5Glue.isOpenImmersion_pullback_map _ _, ⟨fun z => ?_⟩⟩
    have hz : z ∈ Set.range ((Over.pullback jL).map (OpenSub.incl W)).left := by
      rw [hmap, Scheme.Pullback.range_map]
      refine ⟨?_, ⟨pullback.snd 𝒢.G.hom jL z, rfl⟩⟩
      show pullback.fst 𝒢.G.hom jL z ∈ Set.range W.ι
      rw [Scheme.Opens.range_ι]
      apply ge K A L 𝒢
      have h1 : 𝒢.G.hom (pullback.fst 𝒢.G.hom jL z) = jL (pullback.snd 𝒢.G.hom jL z) := by
        rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
      rw [h1]
      set p := pullback.snd 𝒢.G.hom jL z
      have hp : p.asIdeal = ⊥ :=
        (Ideal.eq_bot_or_top p.asIdeal).resolve_right p.isPrime.ne_top
      show Ideal.comap (algebraMap (𝓞 L) L) p.asIdeal = ⊥
      rw [hp]
      exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 L) L)
    exact hz
  haveI : IsIso ((Over.forget _).map ((Over.pullback jL).map (OpenSub.incl W))) := hiso
  haveI : IsIso ((Over.pullback jL).map (OpenSub.incl W)) :=
    isIso_of_reflects_iso _ (Over.forget _)
  let e := asIso ((Over.pullback jL).map (OpenSub.incl W))
  haveI := hmon
  let 𝒢₀ : GroupModel A L :=
    { G := OpenSub.G0 W
      gen := e ≪≫ 𝒢.gen
      gen_hom := by
        letI : GrpObj (genericFibre L (OpenSub.G0 W)) := Functor.grpObjObj
        letI : GrpObj (genericFibre L 𝒢.G) := Functor.grpObjObj
        letI : GrpObj ((Over.pullback jL).obj (OpenSub.G0 W)) := Functor.grpObjObj
        letI : GrpObj ((Over.pullback jL).obj 𝒢.G) := Functor.grpObjObj
        have h1 : IsMonHom ((Over.pullback jL).map (OpenSub.incl W)) := inferInstance
        exact @instIsMonHomComp _ _ _ _ _ _ _ _ _ _ _ h1 𝒢.gen_hom }
  exact ⟨𝒢₀, OpenSub.incl W, inferInstanceAs (IsOpenImmersion W.ι), hmon, Scheme.Opens.range_ι W⟩


open ReductSplit in
/-- reduct-split's local `IdentityComponentBaseChangeDVR` with the connectedness hypotheses on `U` replaced
by `Set.range i = 𝒩⁰` (the form in which it is used below). -/
def IdentityComponentBaseChangeDVRRange : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (K' : Type) [Field K'] [Algebra K K'] [FiniteDimensional K K'] (O' : ValuationSubring K')
    [IsDiscreteValuationRing O'] (hO : O'.comap (algebraMap K K') = O) (A : PkgI3.AbVar K),
    HasSemistableReduction A O →
    ∀ 𝒩 : GroupModelO A O, 𝒩.IsNeronModel →
    ∀ 𝒩' : GroupModelO (A.baseChange K') O', 𝒩'.IsNeronModel →
    ∀ (U : Over (Spec (CommRingCat.of O))) [GrpObj U] (i : U ⟶ 𝒩.G), IsOpenImmersion i.left →
      IsMonHom i → Set.range i.left = idCompSet 𝒩.G →
      ∃ j : (Over.pullback (Spec.map (CommRingCat.ofHom (comapHom hO)))).obj U ⟶ 𝒩'.G,
        IsOpenImmersion j.left ∧
        (letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (comapHom hO)))).obj U) :=
          Functor.grpObjObj
         IsMonHom j)

open ReductSplit in
/-- **`IdentityComponentBaseChangeDVRRange`, PROVED** from the printed SGA 3 VI_B 3.10, SGA 7 IX 3.3 and the
bundle leaf `AVGlue.GeomConnOfRationalPoint` (the argument of `identityComponentFromPrinted_of`). -/
theorem identityComponentBaseChangeDVRRange_of (h3 : SGA3_VIB_3_10) (h7 : SGA7_IX_3_3)
    (hG : AVGlue.GeomConnOfRationalPoint) : IdentityComponentBaseChangeDVRRange := by
  intro K _ O _ K' _ _ _ O' _ hO A hss 𝒩 h𝒩 𝒩' h𝒩' U _ i hoi hmi hri
  have gb := idCompBaseChangeDVR_of h3 hG
  let N := ReductGlue.bcDVR hO 𝒩
  haveI : Smooth (𝟙_ (Over (Spec (CommRingCat.of O')))).hom :=
    ZInQ.Contrib.NeronC.smooth_tensorUnit _
  haveI : Smooth (N.G ⊗ N.G).hom := ZInQ.Contrib.NeronC.smooth_tensor _ _ inferInstance inferInstance
  obtain ⟨c, hc⟩ := (h𝒩' N.G).2 N.gen.hom
  simp only at hc
  have hcm : IsMonHom c :=
    ReductGlue.isMonHom_of_ext (Over.pullback (jO O')) N.gen.hom 𝒩'.gen.hom N.gen_hom 𝒩'.gen_hom
      (h𝒩' _).1 (h𝒩' _).1 c hc
  have hciso : IsIso ((Over.pullback (jO O')).map c) := by
    have : IsIso ((Over.pullback (jO O')).map c ≫ 𝒩'.gen.hom) := by
      rw [hc]; exact Iso.isIso_hom N.gen
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ (Iso.isIso_hom 𝒩'.gen) this
  letI : GrpObj (bcO hO 𝒩.G) := Functor.grpObjObj
  have hW : IsOpen (idCompSet (bcO hO 𝒩.G)) := h3 _ (bcO hO 𝒩.G)
  let W : (bcO hO 𝒩.G).left.Opens := ⟨idCompSet (bcO hO 𝒩.G), hW⟩
  obtain ⟨hWo, -⟩ := h7 K O K' O' hO A hss 𝒩 h𝒩 𝒩' h𝒩' c hcm hciso W rfl
  let g := Spec.map (CommRingCat.ofHom (comapHom hO))
  let k := (Over.pullback g).map i
  haveI : IsOpenImmersion i.left := hoi
  haveI : IsOpenImmersion k.left := ZInQ.H5Glue.isOpenImmersion_pullback_map _ i
  have hkmap : k.left = pullback.map U.hom g 𝒩.G.hom g i.left (𝟙 _) (𝟙 _) (by simp) (by simp) := by
    apply pullback.hom_ext <;> simp [k, Over.pullback_map_left]
  have hrk : Set.range k.left = Set.range W.ι := by
    rw [Scheme.Opens.range_ι, hkmap, Scheme.Pullback.range_map]
    have hga := hri
    have hgb := gb K O K' O' hO 𝒩.G
    have hid : Set.range ((𝟙 (Spec (CommRingCat.of O')) : Spec (CommRingCat.of O') ⟶ _) :
        Spec (CommRingCat.of O') → Spec (CommRingCat.of O')) = Set.univ :=
      Set.range_eq_univ.mpr (fun x => ⟨x, rfl⟩)
    rw [hid, Set.preimage_univ, Set.inter_univ, hga]
    exact hgb
  refine ⟨k ≫ c, ?_, ?_⟩
  · show IsOpenImmersion (k.left ≫ c.left)
    have hfac := IsOpenImmersion.isoOfRangeEq_hom_fac k.left W.ι hrk
    generalize IsOpenImmersion.isoOfRangeEq k.left W.ι hrk = eW at hfac
    have e : k.left ≫ c.left = eW.hom ≫ (W.ι ≫ c.left) := by
      rw [← hfac]
      exact Category.assoc _ _ _
    rw [e]
    haveI := hWo
    infer_instance
  · letI : GrpObj ((Over.pullback g).obj U) := Functor.grpObjObj
    have hk : IsMonHom k := inferInstance
    exact @instIsMonHomComp _ _ _ _ _ _ _ _ _ _ _ hk hcm


open ReductSplit ReductGlue ZInQ.HeightSplit ZInQ.DefFaltings in
/-- **The field `semistableNeronBaseChange` (SS2) from published-form leaves alone** (compiled): BLR 1.2/4,
SGA 3 VI_B 3.10, SGA 7 IX 3.3, EGA IV 8.10.5 (open immersions) and the bundle leaf
`AVGlue.GeomConnOfRationalPoint` (Stacks 04KV). No glue Prop is left. -/
theorem semistableNeronBaseChange_of_printed_full (hB : BLR_1_2_4) (h3 : SGA3_VIB_3_10)
    (h7 : SGA7_IX_3_3) (hE : EGAIV_8_10_5_openImm) (hG : AVGlue.GeomConnOfRationalPoint) :
    ZInQ.HeightSplit.SemistableNeronBaseChange := by
  have hIC := identityComponentOLRange_of h3 hG
  have h33 := identityComponentBaseChangeDVRRange_of h3 h7 hG
  have hOI := openImmersionLocalization hE
  have hL := neronLocalizesDVR_of_printed hB
  intro K _ _ A L _ _ _ 𝒩 h𝒩 hss L' _ _ _ _ _ 𝒩' h𝒩'
  obtain ⟨𝒢₀, i, hoi, hmi, hri⟩ := hIC K A L 𝒩
  haveI : FiniteDimensional L L' := Module.Finite.of_restrictScalars_finite ℚ L L'
  let gLL : Spec (CommRingCat.of (𝓞 L')) ⟶ Spec (CommRingCat.of (𝓞 L)) :=
    Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L')))
  let 𝒱 : GroupModel A L' := ZInQ.H5Glue.GroupModel.baseChange L L' 𝒩
  let 𝒰 : GroupModel A L' := ZInQ.H5Glue.GroupModel.baseChange L L' 𝒢₀
  let jL' : Spec (CommRingCat.of L') ⟶ Spec (CommRingCat.of (𝓞 L')) :=
    Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L') L'))
  letI : GrpObj ((Over.pullback jL').obj 𝒰.G) := Functor.grpObjObj
  letI : GrpObj ((Over.pullback jL').obj 𝒩'.G) := Functor.grpObjObj
  obtain ⟨j, hj⟩ := (h𝒩' 𝒰.G).2 𝒰.gen.hom
  simp only at hj
  haveI : Smooth (𝟙_ (Over (Spec (CommRingCat.of (𝓞 L'))))).hom :=
    ZInQ.Contrib.NeronC.smooth_tensorUnit _
  haveI : Smooth (𝒰.G ⊗ 𝒰.G).hom := ZInQ.Contrib.NeronC.smooth_tensor _ _ inferInstance inferInstance
  have hjm : IsMonHom j :=
    isMonHom_of_ext (Over.pullback jL') 𝒰.gen.hom 𝒩'.gen.hom 𝒰.gen_hom 𝒩'.gen_hom
      (h𝒩' _).1 (h𝒩' _).1 j hj
  haveI := hmi
  letI : GrpObj ((Over.pullback gLL).obj 𝒢₀.G) := Functor.grpObjObj
  letI : GrpObj ((Over.pullback gLL).obj 𝒩.G) := Functor.grpObjObj
  refine ⟨𝒰, 𝒱, ⟨Iso.refl _, (inferInstance : IsMonHom (𝟙 𝒱.G))⟩, ⟨j, ?_, hjm⟩,
    ⟨(Over.pullback gLL).map i, ZInQ.H5Glue.isOpenImmersion_pullback_map _ i,
      (inferInstance : IsMonHom ((Over.pullback gLL).map i))⟩⟩
  -- `j` is an open immersion: check at every DVR `O'` of `L'`
  refine hOI L' 𝒰.G 𝒩'.G j (fun O' _ => ?_)
  let O : ValuationSubring L := O'.comap (algebraMap L L')
  haveI : IsDiscreteValuationRing O := dvrComapFinite L L' O' inferInstance
  haveI := center_isMaximal O
  have hO : O'.comap (algebraMap L L') = O := rfl
  have hssO : HasSemistableReduction (A.baseChange L) O :=
    (semistableLocalGlobal_leaf hL K A L 𝒩 h𝒩).mp hss O inferInstance
  let N := toO 𝒩' O'
  have hN : N.IsNeronModel := hL K A L' 𝒩' h𝒩' O'
  let N' := N.transport (bcbcIso A L L') (bcbcIso_isMonHom A L L')
  have hN' : N'.IsNeronModel := N.transport_isNeronModel _ _ hN
  let U := (Over.pullback (gO O)).obj 𝒢₀.G
  letI : GrpObj U := Functor.grpObjObj
  letI : GrpObj ((Over.pullback (gO O)).obj 𝒩.G) := Functor.grpObjObj
  letI : GrpObj ((Over.pullback (gO O)).obj 𝒢₀.G) := Functor.grpObjObj
  have hmiO : IsMonHom ((Over.pullback (gO O)).map i) := inferInstance
  -- the image of `U` is the identity component of `𝒩 ×_{𝓞_L} O`
  have hrange : Set.range ((Over.pullback (gO O)).map i).left =
      CToPrinted.idCompSet ((Over.pullback (gO O)).obj 𝒩.G) := by
    haveI : IsOpenImmersion i.left := hoi
    have hkmap : ((Over.pullback (gO O)).map i).left = pullback.map 𝒢₀.G.hom (gO O) 𝒩.G.hom (gO O)
        i.left (𝟙 _) (𝟙 _) (by simp) (by simp) := by
      apply pullback.hom_ext <;> simp [Over.pullback_map_left]
    rw [hkmap, Scheme.Pullback.range_map]
    have hid : Set.range ((𝟙 (Spec (CommRingCat.of O)) : Spec (CommRingCat.of O) ⟶ _) :
        Spec (CommRingCat.of O) → Spec (CommRingCat.of O)) = Set.univ :=
      Set.range_eq_univ.mpr (fun x => ⟨x, rfl⟩)
    rw [hid, Set.preimage_univ, Set.inter_univ, hri]
    exact CToPrinted.idComp_baseChange h3 hG (gO O) 𝒩.G
  obtain ⟨j', hj'o, hj'm⟩ := h33 L O L' O' hO (A.baseChange L) hssO (toO 𝒩 O)
    (hL K A L 𝒩 h𝒩 O) N' hN' U ((Over.pullback (gO O)).map i)
    (ZInQ.H5Glue.isOpenImmersion_pullback_map _ i) hmiO hrange
  -- compare `T = 𝒰 ×_{𝓞_{L'}} O'` with `U ×_O O'`
  have hsq : gO O' ≫ gLL = Spec.map (CommRingCat.ofHom (comapHom hO)) ≫ gO O := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  let c := isoX (pbCompIso (gO O') gLL _ hsq (Grp.mk 𝒢₀.G)) ≪≫
    (isoX (pbCompIso (Spec.map (CommRingCat.ofHom (comapHom hO))) (gO O) _ rfl (Grp.mk 𝒢₀.G))).symm
  let T := (Over.pullback (gO O')).obj 𝒰.G
  haveI : Smooth T.hom := by change Smooth (pullback.snd 𝒰.G.hom (gO O')); infer_instance
  let j₂ : T ⟶ N.G := c.hom ≫ j'
  haveI : IsOpenImmersion j₂.left := by
    have h1 : IsOpenImmersion c.hom.left := by
      haveI : IsIso c.hom.left := Functor.map_isIso (Over.forget _) c.hom
      infer_instance
    have h2 : IsOpenImmersion j'.left := hj'o
    show IsOpenImmersion (c.hom.left ≫ j'.left)
    exact @IsOpenImmersion.comp _ _ _ _ _ h1 h2
  -- generic identification of `T`
  let eT : (Over.pullback (jO O')).obj T ≅ (A.baseChange L').X :=
    isoX (pbCompIso (jO O') (gO O') _ (jO_gO O') (Grp.mk 𝒰.G)) ≪≫ 𝒰.gen
  have h₂ : IsIso ((Over.pullback (jO O')).map j₂) := by
    haveI : IsOpenImmersion ((Over.pullback (jO O')).map j₂).left :=
      ZInQ.H5Glue.isOpenImmersion_pullback_map _ j₂
    exact isIso_of_openImmersion_of_iso (A.baseChange L') eT N.gen _
  have hcomp := pbCompIso_natural' (jO O') (gO O') _ (jO_gO O') j
  have hjL : IsIso ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L') L')))).map j) := by
    have : IsIso ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L') L')))).map j ≫
        𝒩'.gen.hom) := by
      rw [hj]; exact Iso.isIso_hom 𝒰.gen
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ (Iso.isIso_hom 𝒩'.gen) this
  have h₁ : IsIso ((Over.pullback (jO O')).map ((Over.pullback (gO O')).map j)) := by
    have : IsIso ((Over.pullback (jO O')).map ((Over.pullback (gO O')).map j) ≫
        (isoX (pbCompIso (jO O') (gO O') _ (jO_gO O') (Grp.mk 𝒩'.G))).hom) := by
      rw [hcomp]
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_hom _) hjL
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ (Iso.isIso_hom _) this
  exact isOpenImmersion_of_neron N hN T ((Over.pullback (gO O')).map j) j₂ h₁ h₂


/-- reduct-glue's leaf `IdentityComponentOL` is a theorem from the printed SGA 3 VI_B 3.10 and the bundle
leaf `AVGlue.GeomConnOfRationalPoint`. -/
theorem identityComponentOL_of_printed_full (h3 : SGA3_VIB_3_10)
    (hG : AVGlue.GeomConnOfRationalPoint) : ReductGlue.IdentityComponentOL :=
  identityComponentOL_of_printed' h3 (idCompSubgroup_of h3 hG) idCompGenericFibre (idCompGeomFibres hG)

/-- **The published-form leaves of this task** (part H's `ShimuraMainThmIY3` is in `Shimura.lean`).
`AVGlue.GeomConnOfRationalPoint` is already a field of the leaf bundles. -/
structure CToPrintedLeaves : Prop where
  blr : BLR_1_2_4
  faltings5 : FaltingsLemma5Printed
  raynaud : RaynaudKernelBound
  sga3 : SGA3_VIB_3_10
  sga7 : SGA7_IX_3_3
  ega : EGAIV_8_10_5_openImm
  geomConn : AVGlue.GeomConnOfRationalPoint

/-- **Three of the four fields from the leaves** (compiled). -/
theorem fields_of_leaves (l : CToPrintedLeaves) :
    ReductGlue.NeronLocalizesDVR ∧ ZInQ.HeightSplit.FaltingsLemma5BC ∧
      ZInQ.HeightSplit.SemistableNeronBaseChange :=
  ⟨neronLocalizesDVR_of_printed l.blr, faltingsLemma5BC_of_printed l.faltings5 l.raynaud,
    semistableNeronBaseChange_of_printed_full l.blr l.sga3 l.sga7 l.ega l.geomConn⟩

/-- **reduct-glue's leaves `NeronLocalizesDVR`, `IdentityComponentOL`, `OpenImmersionOfLocal` from the leaves**
(compiled). -/
theorem reductGlue_leaves_of_printed (l : CToPrintedLeaves) :
    ReductGlue.NeronLocalizesDVR ∧ ReductGlue.IdentityComponentOL ∧ ReductGlue.OpenImmersionOfLocal :=
  ⟨neronLocalizesDVR_of_printed l.blr, identityComponentOL_of_printed_full l.sga3 l.geomConn,
    openImmersionLocalization l.ega⟩

end CToPrinted

#print axioms CToPrinted.neronLocalizesDVR_of_printed
#print axioms CToPrinted.semistableNeronBaseChange_of_printedBLR
#print axioms CToPrinted.semistableNeronBaseChange_of_printed
#print axioms CToPrinted.faltingsLemma5BC_of_printed
#print axioms CToPrinted.openImmersionLocalization
#print axioms CToPrinted.semistableNeronBaseChange_of_printed'
#print axioms CToPrinted.semistableNeronBaseChange_of_printed''
#print axioms CToPrinted.semistableNeronBaseChange_of_printed_final
#print axioms CToPrinted.semistableNeronBaseChange_of_printed_final'
#print axioms CToPrinted.semistableNeronBaseChange_of_printed_final''
#print axioms CToPrinted.semistableNeronBaseChange_of_printed_best
#print axioms CToPrinted.semistableNeronBaseChange_of_printed_full
#print axioms CToPrinted.fields_of_leaves
#print axioms CToPrinted.reductGlue_leaves_of_printed

namespace HDec

namespace HSyn

/-- **The research leaves still open** (leaf-fold12): route-a-fold's `OpenResearchLeaves11` with `neronLocalizesDVR`,
`faltingsLemma5BC` and `semistableNeronBaseChange` replaced by the printed leaves they follow from (c-to-printed). 32 fields. -/
structure OpenResearchLeaves12 : Prop where
  /-- H-1 (`r1r2`), printed form: the fine moduli scheme `Y` of abelian schemes with `𝒪`-action and level 3
  (`R1fpPropsAb`) with the coarse `X₆`, the Hecke, recognition and `π₀` clauses of `R1R2fpRep`. Replaces `r1r2`. -/
  r1r2Ab : LeafAdopt.R1R2fpRepAb
  /-- H-139, printed form: Shimura's family over the fine moduli scheme of abelian schemes. Replaces
  `shimuraFamily`. -/
  shimuraFamilyAb : QMSplit.Moduli.ShimuraFamilyAb
  igusaPsi4 : QMSplit.Theta.IgusaPsi4
  igusaChi10 : QMSplit.Theta.IgusaChi10
  r7a : _root_.PkgI2.NeronOggShafarevich.{0}
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  dsThm965 : _root_.ZInQ.Contrib.HodgeSplit.DSThm965
  dsThm966 : _root_.ZInQ.Contrib.HodgeSplit.DSThm966
  r16 : _root_.LeafModCurves.R16_EichlerShimuraJ1'
  r17 : _root_.LadicCond.CarayolR17'
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795), replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.BostLowerBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14
  /-- reduct-split, r8: SGA 7 IX Thm 3.6 over a DVR (semistable reduction after a finite extension, at every place
  above `O`). -/
  semistableReductionDVR : _root_.ReductSplit.SemistableReductionDVR
  /-- reduct-split, r8: SGA 7 IX Prop. 3.5, "semistable ⇒ `(σ - 1)² = 0` on `T_ℓ`" (weakest reading). -/
  semistableUnipotent : _root_.ReductSplit.SemistableUnipotent
  /-- reduct-split, r8: BLR §1.4 Thm 3 over a DVR (scheme form). -/
  neronSchemeModelExistsDVR : _root_.ReductSplit.NeronSchemeModelExistsDVR
  /-- shimura-split, r5count, printed form: González–Rotger 2006 Prop. 5.6 at `(D, N) = (6, 1)` on the points of
  one canonical coarse witness `X₆` of the fine moduli scheme of abelian schemes. Replaces
  `gonzalezRotgerCountX6`. -/
  gonzalezRotgerCountX6Ab : _root_.ShimuraSplit.GonzalezRotgerCountX6Ab
  /-- reduct-split, r6: SGA 7 I Exp. IX Prop. 4.7 (Raynaud's criterion) over a DVR (published form pending the
  base review). -/
  raynaudSemistable : _root_.ReductSplit.RaynaudSemistable
  /-- reduct-split, SS1/SS3: SGA 7 I Exp. IX 3.3, first assertion, over a DVR (published form pending the base
  review). -/
  semistablePersistsDVR : _root_.ReductSplit.SemistablePersistsDVR
  /-- r1univ-rigid: **Mumford's rigidity over a base, printed core** (GIT Thm 6.14 on each connected component and
  Cor. 6.4 over `S`; numbers UNVERIFIED): a proper smooth geometrically connected family over a locally noetherian
  `S` with a section `e`, all of whose field fibres are abelian varieties with identity `e(s)`, is a group object in
  `Over S` with identity `e`, and every `S`-endomorphism fixing `e` is a homomorphism. -/
  mumfordRigidityCore : _root_.LeafQM.AV.R1UnivRigid.MumfordRigidityCore
  /-- c-to-printed, printed form: Bosch–Lütkebohmert–Raynaud, *Néron models*, §1.2 Prop. 4 (over a Dedekind
  domain, a smooth separated model of finite type is a Néron model iff its localizations at the closed points are;
  locator UNVERIFIED). Replaces `neronLocalizesDVR`. -/
  blr_1_2_4 : _root_.CToPrinted.BLR_1_2_4
  /-- c-to-printed, printed form: Faltings 1983, Lemma 5 (the change of the Faltings height under an isogeny
  through `log #s*Ω¹` of its kernel; locator UNVERIFIED). With `raynaudKernelBound` replaces `faltingsLemma5BC`. -/
  faltingsLemma5Printed : _root_.CToPrinted.FaltingsLemma5Printed
  /-- c-to-printed, printed form: Raynaud's bound on the kernel term in Faltings' Lemma 5 (locator UNVERIFIED). -/
  raynaudKernelBound : _root_.CToPrinted.RaynaudKernelBound
  /-- c-to-printed, printed form: SGA 3 VI_B 3.10 (the identity component `G⁰` of a smooth group scheme is open;
  number UNVERIFIED). With the next two and `geomConnOfRationalPoint` replaces `semistableNeronBaseChange`. -/
  sga3_VIB_3_10 : _root_.CToPrinted.SGA3_VIB_3_10
  /-- c-to-printed, printed form: SGA 7 IX 3.3 (`N⁰ ⊗ R' ≅ N'⁰` for semistable reduction; locator UNVERIFIED). -/
  sga7_IX_3_3 : _root_.CToPrinted.SGA7_IX_3_3
  /-- c-to-printed, printed form: EGA IV 8.10.5, open immersions descend through limits (locator UNVERIFIED). -/
  egaIV_8_10_5_openImm : _root_.CToPrinted.EGAIV_8_10_5_openImm

/-- route-a-fold's research bundle from leaf-fold12's: the three fields are c-to-printed's theorems from
their printed leaves (and the textbook field `geomConnOfRationalPoint`, Stacks 04KV). -/
theorem researchLeaves11_of_open12 (r : OpenResearchLeaves12) (t : OpenTextbookLeaves10) :
    OpenResearchLeaves11 where
  r1r2Ab := r.r1r2Ab
  shimuraFamilyAb := r.shimuraFamilyAb
  igusaPsi4 := r.igusaPsi4
  igusaChi10 := r.igusaChi10
  r7a := r.r7a
  r9a := r.r9a
  r9b := r.r9b
  hodgeTateDecompAbVar := r.hodgeTateDecompAbVar
  deRhamH1AbVarT := r.deRhamH1AbVarT
  r11r12 := r.r11r12
  eigenformHTNew := r.eigenformHTNew
  dsThm965 := r.dsThm965
  dsThm966 := r.dsThm966
  r16 := r.r16
  r17 := r.r17
  semistableNeronBaseChange := _root_.CToPrinted.semistableNeronBaseChange_of_printed_full r.blr_1_2_4
    r.sga3_VIB_3_10 r.sga7_IX_3_3 r.egaIV_8_10_5_openImm t.geomConnOfRationalPoint
  bostLowerBound := r.bostLowerBound
  javanpeykarBound := r.javanpeykarBound
  faltingsLemma5BC := _root_.CToPrinted.faltingsLemma5BC_of_printed r.faltingsLemma5Printed r.raynaudKernelBound
  pazukiCor13Upper := r.pazukiCor13Upper
  gaudronRemondThm14 := r.gaudronRemondThm14
  semistableReductionDVR := r.semistableReductionDVR
  semistableUnipotent := r.semistableUnipotent
  neronSchemeModelExistsDVR := r.neronSchemeModelExistsDVR
  gonzalezRotgerCountX6Ab := r.gonzalezRotgerCountX6Ab
  raynaudSemistable := r.raynaudSemistable
  semistablePersistsDVR := r.semistablePersistsDVR
  neronLocalizesDVR := _root_.CToPrinted.neronLocalizesDVR_of_printed r.blr_1_2_4
  mumfordRigidityCore := r.mumfordRigidityCore

/-- **G0 with only the open leaves and the open glue** (leaf-fold12; no `sorry`, standard axioms).
`ZInQ.SixContactMin` from `OpenResearchLeaves12` (32), `OpenTextbookLeaves10` (15), `OpenAddedLeaves11` (13) and
`OpenGlue7` (1). -/
theorem sixContactMin_of_open15 (r : OpenResearchLeaves12) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves11)
    (g : OpenGlue7) (hYu : QMLattice.YuB6Alg) (hY3 : TSHecke.Y3Connected) : ZInQ.SixContactMin :=
  sixContactMin_of_open14 (researchLeaves11_of_open12 r t) t l g hYu hY3

end HSyn

end HDec

#print axioms HDec.HSyn.researchLeaves11_of_open12
#print axioms HDec.HSyn.sixContactMin_of_open15

import ShRG

/-! # sh-printed2, Part S: the field `sga7_IX_3_3` from SGA 7 IX 3.3 over strictly henselian traits

`CToPrinted.SGA7_IX_3_3` (field `sga7_IX_3_3` of `HDec.HSyn.OpenResearchLeaves12`) states the second
assertion of SGA 7 IX 3.3 over any pair of discrete valuation rings `O ⊆ O'` with `K'/K` finite. If the
print is over strictly henselian traits only, the published form is `SGA7_IX_3_3_SH` below. This part proves
`SGA7_IX_3_3_0` (the field statement word for word with `[CharZero K]` and `[PerfectField κ(O)]` added; the
one use is at number fields) from `SGA7_IX_3_3_SH`, sh-route's Néron leaf `ShRoute.NeronBaseChangeSH`, and
two leaves already in the bundles (`CToPrinted.SGA3_VIB_3_10`, `AVGlue.GeomConnOfRationalPoint`):
* sh-route's `shPair0` (proved commutative algebra) gives strict henselizations `P ⊇ O`, `P' ⊇ O'` with
  `P' ∩ E = P`, `E'/E` finite;
* the Néron models base change to `P`, `P'` (`NeronBaseChangeSH`) and semistability passes to `P`
  (reduct-glue's `isSemistable_bcDVR_iff`);
* the SH form gives the open immersion with image `𝒩'⁰` over `P'`;
* the open immersion descends along the faithfully flat `Spec P' → Spec O'` (Mathlib's fpqc descent of
  open immersions, `IsOpenImmersion.DescendsAlong (Surjective ⊓ Flat ⊓ QuasiCompact)`), and the image
  descends because the identity component commutes with base change (c-to-printed's `idComp_baseChange`,
  from SGA 3 VI_B 3.10 and Stacks 04KV) and `Spec P' → Spec O'` is surjective. -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReductSplit ReductGlue CToPrinted

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace SHPrinted2

/-! ## Statements -/

/-- **LEAF `SGA7_IX_3_3_SH`** (Grothendieck, SGA 7 I, Exp. IX, Prop. 3.3, second assertion, over strictly
henselian traits; number and wording recalled, UNVERIFIED, no network). The field statement
`CToPrinted.SGA7_IX_3_3` with both discrete valuation rings strictly henselian (reduct-glue's
`IsStrictlyHenselianDVR`: henselian with separably closed residue field) and `K` of characteristic 0.
*Printed* (as recalled): `S' → S` a morphism of strictly henselian traits, `A_K` with semistable
reduction, `N`, `N'` the Néron models of `A_K` over `S` and of `A_{K'}` over `S'`; then
`N ×_S S' → N'` induces an isomorphism `N⁰ ×_S S' ≅ N'⁰`. The Lean conclusion is the field's: for the
open `U = (N ×_O O')⁰`, `U → N'` is an open immersion with image `N'⁰`. It is a specialization of the
field statement (`sga7_IX_3_3_SH_of_field`) and of the print. -/
def SGA7_IX_3_3_SH : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O],
    IsStrictlyHenselianDVR O →
    ∀ (K' : Type) [Field K'] [Algebra K K'] [FiniteDimensional K K'] (O' : ValuationSubring K')
    [IsDiscreteValuationRing O'], IsStrictlyHenselianDVR O' →
    ∀ (hO : O'.comap (algebraMap K K') = O) (A : PkgI3.AbVar K),
    HasSemistableReduction A O →
    ∀ 𝒩 : GroupModelO A O, 𝒩.IsNeronModel →
    ∀ 𝒩' : GroupModelO (A.baseChange K') O', 𝒩'.IsNeronModel →
    letI : GrpObj (bcO hO 𝒩.G) := Functor.grpObjObj
    ∀ c : bcO hO 𝒩.G ⟶ 𝒩'.G, IsMonHom c → IsIso ((Over.pullback (jO O')).map c) →
    ∀ U : (bcO hO 𝒩.G).left.Opens, (U : Set (bcO hO 𝒩.G).left) = idCompSet (bcO hO 𝒩.G) →
      IsOpenImmersion (U.ι ≫ c.left) ∧ Set.range (U.ι ≫ c.left).base = idCompSet 𝒩'.G

/-- **`SGA7_IX_3_3` for characteristic 0 and a perfect residue field**: `CToPrinted.SGA7_IX_3_3` word for
word with `[CharZero K]` and `[PerfectField (IsLocalRing.ResidueField O)]` added (its one use is at a
number field, whose residue fields are finite). -/
def SGA7_IX_3_3_0 : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [PerfectField (IsLocalRing.ResidueField O)]
    (K' : Type) [Field K'] [Algebra K K'] [FiniteDimensional K K'] (O' : ValuationSubring K')
    [IsDiscreteValuationRing O'] (hO : O'.comap (algebraMap K K') = O) (A : PkgI3.AbVar K),
    HasSemistableReduction A O →
    ∀ 𝒩 : GroupModelO A O, 𝒩.IsNeronModel →
    ∀ 𝒩' : GroupModelO (A.baseChange K') O', 𝒩'.IsNeronModel →
    letI : GrpObj (bcO hO 𝒩.G) := Functor.grpObjObj
    ∀ c : bcO hO 𝒩.G ⟶ 𝒩'.G, IsMonHom c → IsIso ((Over.pullback (jO O')).map c) →
    ∀ U : (bcO hO 𝒩.G).left.Opens, (U : Set (bcO hO 𝒩.G).left) = idCompSet (bcO hO 𝒩.G) →
      IsOpenImmersion (U.ι ≫ c.left) ∧ Set.range (U.ι ≫ c.left).base = idCompSet 𝒩'.G

/-- Both new statements are specializations of the field's. -/
theorem sga7_IX_3_3_SH_of_field (h : SGA7_IX_3_3) : SGA7_IX_3_3_SH :=
  fun K _ _ O _ _ K' _ _ _ O' _ _ hO A => h K O K' O' hO A

theorem sga7_IX_3_3_0_of_field (h : SGA7_IX_3_3) : SGA7_IX_3_3_0 :=
  fun K _ _ O _ _ K' _ _ _ O' _ hO A => h K O K' O' hO A

/-! ## Pullback bookkeeping -/

section PB

/-- The composite pullback comparison preserves the projection to the original object (copied from
the vendored `CategoryTheory.Over.pullbackComp_hom_app_left_fst_fst`,
ZInQKernel/Contrib/CloudW07JacobiansCurves/Jacobian/CategoryTheory/Comma/Over/Pullback.lean, Apache-2.0,
Axel Delaval, Jie Xu, Shitan Xu; not imported by TailZ19). -/
theorem pullbackComp_hom_app_left_fst_fst' {C : Type*} [Category C] [HasPullbacks C]
    {base middle extension : C}
    (firstMap : extension ⟶ middle) (secondMap : middle ⟶ base) (object : Over base) :
    ((Over.pullbackComp firstMap secondMap).hom.app object).left ≫
      pullback.fst (pullback.snd object.hom secondMap) firstMap ≫
        pullback.fst object.hom secondMap =
      pullback.fst object.hom (firstMap ≫ secondMap) := by
  have comparison := conjugateEquiv_counit (Over.mapPullbackAdj (firstMap ≫ secondMap))
    ((Over.mapPullbackAdj firstMap).comp (Over.mapPullbackAdj secondMap))
    (Over.mapComp firstMap secondMap).inv object
  rw [Adjunction.comp_counit_app] at comparison
  have projection := congrArg (fun morphism ↦ morphism.left) comparison
  simpa [Over.pullbackComp, conjugateIsoEquiv, Over.mapComp, Over.comp_left,
    Over.mapPullbackAdj_counit_app, Category.assoc] using projection

/-- `pbCompIso` preserves the projection to the original group scheme. -/
theorem pbCompIso_fst {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (hfg : f ≫ g = h)
    (𝒢 : Grp (Over Z)) :
    (isoX (pbCompIso f g h hfg 𝒢)).hom.left ≫ pullback.fst 𝒢.X.hom h =
      pullback.fst (pullback.snd 𝒢.X.hom g) f ≫ pullback.fst 𝒢.X.hom g := by
  subst hfg
  have e := pullbackComp_hom_app_left_fst_fst' f g 𝒢.X
  have hx : (isoX (pbCompIso f g (f ≫ g) rfl 𝒢)).hom =
      𝟙 _ ≫ (Over.pullbackComp f g).inv.app 𝒢.X ≫ 𝟙 _ := by
    rw [pbCompIso_eq]; rfl
  rw [hx, Category.id_comp, Category.comp_id, ← e]
  have h2 : ((Over.pullbackComp f g).inv.app 𝒢.X).left ≫ ((Over.pullbackComp f g).hom.app 𝒢.X).left =
      𝟙 _ := by
    rw [← Over.comp_left, ← NatTrans.comp_app, Iso.inv_hom_id]; rfl
  calc _ = (((Over.pullbackComp f g).inv.app 𝒢.X).left ≫ ((Over.pullbackComp f g).hom.app 𝒢.X).left) ≫
        pullback.fst (pullback.snd 𝒢.X.hom g) f ≫ pullback.fst 𝒢.X.hom g := by simp only [Category.assoc]; rfl
    _ = _ := by rw [h2, Category.id_comp]

theorem pbCompIso_inv_fst {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (hfg : f ≫ g = h)
    (𝒢 : Grp (Over Z)) :
    (isoX (pbCompIso f g h hfg 𝒢)).inv.left ≫ pullback.fst (pullback.snd 𝒢.X.hom g) f ≫
      pullback.fst 𝒢.X.hom g = pullback.fst 𝒢.X.hom h := by
  have e := pbCompIso_fst f g h hfg 𝒢
  have hi : (isoX (pbCompIso f g h hfg 𝒢)).inv.left ≫ (isoX (pbCompIso f g h hfg 𝒢)).hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id]; rfl
  calc _ = (isoX (pbCompIso f g h hfg 𝒢)).inv.left ≫
        ((isoX (pbCompIso f g h hfg 𝒢)).hom.left ≫ pullback.fst 𝒢.X.hom h) := by erw [e]; rfl
    _ = _ := by erw [← Category.assoc, hi, Category.id_comp]

end PB

/-! ## `Spec O₁ → Spec O` is faithfully flat for an extension of valuation rings over a DVR -/

section FF

variable {K K₁ : Type} [Field K] [Field K₁] [Algebra K K₁] {O : ValuationSubring K}
  {O₁ : ValuationSubring K₁}

theorem comapHom_injective (hO : O₁.comap (algebraMap K K₁) = O) :
    Function.Injective (comapHom hO) := by
  intro a b h
  apply Subtype.ext
  have h' := congrArg (fun z : O₁ => (z : K₁)) h
  exact (algebraMap K K₁).injective h'

theorem flat_surjective_gD [IsDiscreteValuationRing O] (hO : O₁.comap (algebraMap K K₁) = O) :
    Flat (gD hO) ∧ Surjective (gD hO) := by
  rw [flat_and_surjective_SpecMap_iff]
  letI : Algebra O O₁ := (comapHom hO).toAlgebra
  show Module.FaithfullyFlat O O₁
  haveI : IsLocalHom (algebraMap O O₁) := comapHom_isLocalHom hO
  haveI : Module.Flat O O₁ := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    rintro m ⟨⟨r, hr⟩, h⟩
    have h1 : comapHom hO r * m = 0 := h
    have h2 : comapHom hO r ≠ 0 := by
      intro h0
      apply nonZeroDivisors.coe_ne_zero ⟨r, hr⟩
      exact comapHom_injective hO (by rw [h0, map_zero])
    exact (mul_eq_zero.mp h1).resolve_left h2
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

end FF

end SHPrinted2

namespace SHPrinted2

/-! ## Descent of an open immersion and its image along a faithfully flat base change -/

section Descent

/-- The base change of an `S`-morphism `c : Y → N` along `g : S' → S` is a pullback of `c`. -/
theorem isPullback_bc {S S' : Scheme.{0}} (g : S' ⟶ S) {Y N : Over S} (c : Y ⟶ N) :
    IsPullback ((Over.pullback g).map c).left (pullback.fst Y.hom g) (pullback.fst N.hom g) c.left := by
  have t := (IsPullback.of_hasPullback N.hom g).flip
  have s : IsPullback (((Over.pullback g).map c).left ≫ pullback.snd N.hom g) (pullback.fst Y.hom g) g
      (c.left ≫ N.hom) := by
    have e1 : ((Over.pullback g).map c).left ≫ pullback.snd N.hom g = pullback.snd Y.hom g :=
      Over.w ((Over.pullback g).map c)
    have e2 : c.left ≫ N.hom = Y.hom := Over.w c
    rw [e1, e2]
    exact (IsPullback.of_hasPullback Y.hom g).flip
  refine IsPullback.of_right s ?_ t
  simp [Over.pullback_map_left]

/-- The same square with the corner replaced through an isomorphism. -/
theorem isPullback_bc_iso {S S' : Scheme.{0}} (g : S' ⟶ S) {Y N : Over S} (c : Y ⟶ N) {Y₁ : Scheme.{0}}
    (e : Y₁ ⟶ ((Over.pullback g).obj Y).left) [IsIso e] :
    IsPullback (e ≫ ((Over.pullback g).map c).left) (e ≫ pullback.fst Y.hom g) (pullback.fst N.hom g)
      c.left := by
  have s : IsPullback e (e ≫ pullback.fst Y.hom g) (pullback.fst Y.hom g) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have := s.paste_horiz (isPullback_bc g c)
  simpa using this

/-- **Descent of an open immersion with prescribed image** along a surjective, flat, quasi-compact `p`
(Mathlib's fpqc descent of open immersions, `IsOpenImmersion.DescendsAlong`). -/
theorem descend_openImm {Y Y₁ N N₁ : Scheme.{0}} (U : Y.Opens) (c : Y ⟶ N) (c₁ : Y₁ ⟶ N₁)
    (q : Y₁ ⟶ Y) (p : N₁ ⟶ N) (hsq : IsPullback c₁ q p c) [Surjective p] [Flat p] [QuasiCompact p]
    (U₁ : Y₁.Opens) (hU₁ : (U₁ : Set Y₁) = q.base ⁻¹' U) (ho : IsOpenImmersion (U₁.ι ≫ c₁))
    (T : Set N) (T₁ : Set N₁) (hT : p.base ⁻¹' T = T₁) (hr : Set.range (U₁.ι ≫ c₁).base = T₁) :
    IsOpenImmersion (U.ι ≫ c) ∧ Set.range (U.ι ≫ c).base = T := by
  have hU : U₁ = q ⁻¹ᵁ U := by
    ext x
    rw [hU₁]
    rfl
  subst hU
  have sq := (isPullback_morphismRestrict q U).flip.paste_horiz hsq
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) p := ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  refine ⟨MorphismProperty.of_isPullback_of_descendsAlong (P := @IsOpenImmersion) sq hQ ho, ?_⟩
  have hfst : (q ⁻¹ᵁ U).ι ≫ c₁ = sq.isoPullback.hom ≫ pullback.fst p (U.ι ≫ c) :=
    (sq.isoPullback_hom_fst).symm
  have hr' : Set.range ((q ⁻¹ᵁ U).ι ≫ c₁).base = p.base ⁻¹' Set.range (U.ι ≫ c).base := by
    have hcomp : ⇑(sq.isoPullback.hom ≫ pullback.fst p (U.ι ≫ c)) =
        ⇑(pullback.fst p (U.ι ≫ c)) ∘ ⇑sq.isoPullback.hom :=
      funext (Scheme.Hom.comp_apply _ _)
    change Set.range ⇑((q ⁻¹ᵁ U).ι ≫ c₁) = p ⁻¹' Set.range ⇑(U.ι ≫ c)
    rw [hfst, hcomp, Function.Surjective.range_comp sq.isoPullback.hom.surjective,
      Scheme.Pullback.range_fst]
  rw [hr', ← hT] at hr
  exact (Set.preimage_injective.mpr p.surjective) hr

end Descent

end SHPrinted2

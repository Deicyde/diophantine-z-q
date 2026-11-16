import ZInQKernel.Contrib.OneProof.H.TailZ23
import ZInQKernel.Contrib.OneProof.StrictHenselizationPair
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.CategoryTheory.Comma.Over.Pullback

/-!
# `CToPrinted.SGA7_IX_3_3` from its strictly henselian form (task gt-sga7)

The open hypothesis `sga7_IX_3_3` (`CToPrinted.SGA7_IX_3_3`, `ZInQKernel/Contrib/OneProof/H/TailZ19.lean`) is the
**second** assertion of SGA 7 I, Exp. IX, Prop. 3.3 (`N⁰ ×_R R' ≅ N'⁰` for semistable reduction) over an
arbitrary pair of discrete valuation rings `O ⊆ O'` with `K'/K` finite. It counts GLUE because SGA 7 IX may
be printed over strictly henselian traits. The chain's leaf `ReductB.SemistablePersistsSHcp` is the *first*
assertion of 3.3 (semistable reduction persists) and does not give the second, so a strictly henselian form
of the second assertion enters as a leaf.

This file proves, by strict henselization and fpqc descent (the argument of task sh-printed2, ported to
gt-shpair's every-characteristic commutative algebra `GapSHPair.shPair`):

* `SGA7PersistsNF.sga7_IX_3_3_of_SH : SGA7_IX_3_3_SH → GapSHPair.NeronBaseChangeStrictHenselization →
    CToPrinted.SGA3_VIB_3_10 → AVGlue.GeomConnOfRationalPoint → CToPrinted.SGA7_IX_3_3`
  — the field **exactly**, from the strictly henselian form `SGA7_IX_3_3_SH` (any characteristic; reading
  risk: the print may assume an algebraically closed residue field) and three leaves already in the bundles;
* `SGA7PersistsNF.sga7_IX_3_3cp_of_SHcp` — the field restricted to `[CharZero K]` and
  `[PerfectField κ(O)]` (`SGA7_IX_3_3cp`), from the restricted leaf `SGA7_IX_3_3_SHcp` (strictly
  henselian, characteristic 0, perfect hence algebraically closed residue field: a specialization of every
  reading of the print), with the same three bundle leaves;
* `SGA7PersistsNF.semistableNeronBaseChange_of_printed_cp` — the one consumer
  (`CToPrinted.semistableNeronBaseChange_of_printed_full`) rerouted through `SGA7_IX_3_3cp`: at its use
  `K = L` is a number field and `κ(O)` is finite (`ReductB.perfectField_residue_nf`).

Descent: `Spec P' → Spec O'` is faithfully flat (`P'` a valuation ring over the DVR `O'`), the open
immersion descends by Mathlib's `IsOpenImmersion.DescendsAlong (Surjective ⊓ Flat ⊓ QuasiCompact)`, and the
image descends because the identity component commutes with base change (c-to-printed's
`CToPrinted.idComp_baseChange`, from SGA 3 VI_B 3.10 and Stacks 04KV). The pullback/descent helpers below are
sh-printed2's (`scratch/sh-printed2/PartS.lean` on `origin/wip/sh-printed2`, not in the chain).
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ReductSplit ReductGlue CToPrinted

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace SGA7PersistsNF

/-! ## Statements -/

/-- **LEAF `SGA7_IX_3_3_SH`** (Grothendieck, SGA 7 I, Exp. IX, Prop. 3.3, second assertion, over strictly
henselian traits; number and wording recalled, UNVERIFIED, no network). The field statement
`CToPrinted.SGA7_IX_3_3` word for word with both discrete valuation rings strictly henselian (reduct-glue's
`IsStrictlyHenselianDVR`: henselian with separably closed residue field). *Printed* (as recalled):
`S' → S` a morphism of traits, `A_K` with semistable reduction, `N`, `N'` the Néron models of `A_K` over `S`
and of `A_{K'}` over `S'`; then `N ×_S S' → N'` induces an isomorphism `N⁰ ×_S S' ≅ N'⁰`. The Lean
conclusion is the field's: for the open `U = (N ×_O O')⁰`, `U → N'` is an open immersion with image `N'⁰`.
A specialization of the field statement (`sga7_IX_3_3_SH_of_field`). Reading risk (as for the chain's
`raynaudSemistableSH`, reduct-b §5): SGA 7 IX may work over traits with algebraically closed residue field;
then the restricted form `SGA7_IX_3_3_SHcp` is the print. -/
def SGA7_IX_3_3_SH : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O],
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

/-- **LEAF (restricted) `SGA7_IX_3_3_SHcp`** (SGA 7 I, Exp. IX, Prop. 3.3, second assertion; number
UNVERIFIED): `SGA7_IX_3_3_SH` with `[CharZero K]` and `[PerfectField κ(O)]` added, so that the residue field
of the strictly henselian `O` is algebraically closed (Mathlib `isAlgClosed_of_perfectField`). The same
restriction as the chain's `ReductB.SemistablePersistsSHcp` (the first assertion): a specialization of every
reading of the print (`sga7_IX_3_3_SHcp_of_SH`). -/
def SGA7_IX_3_3_SHcp : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [PerfectField (IsLocalRing.ResidueField O)], IsStrictlyHenselianDVR O →
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

/-- **`SGA7_IX_3_3cp`** (the form the one consumer needs): `CToPrinted.SGA7_IX_3_3` word for word with
`[CharZero K]` and `[PerfectField (IsLocalRing.ResidueField O)]` added. Its one use is at a number field,
whose residue fields are finite. -/
def SGA7_IX_3_3cp : Prop :=
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

/-- The new leaves are specializations of the field statement (never stronger than it), and the restricted
leaf is a specialization of the unrestricted one. -/
theorem sga7_IX_3_3_SH_of_field (h : SGA7_IX_3_3) : SGA7_IX_3_3_SH :=
  fun K _ O _ _ K' _ _ _ O' _ _ hO A => h K O K' O' hO A

theorem sga7_IX_3_3_SHcp_of_SH (h : SGA7_IX_3_3_SH) : SGA7_IX_3_3_SHcp :=
  fun K _ _ O _ _ hS K' _ _ _ O' _ hS' hO A => h K O hS K' O' hS' hO A

theorem sga7_IX_3_3cp_of_field (h : SGA7_IX_3_3) : SGA7_IX_3_3cp :=
  fun K _ _ O _ _ K' _ _ _ O' _ hO A => h K O K' O' hO A

/-- The body of the statements after `hO` (an abbreviation for the proofs below). -/
def Body {K K' : Type} [Field K] [Field K'] [Algebra K K'] (O : ValuationSubring K)
    (O' : ValuationSubring K') (hO : O'.comap (algebraMap K K') = O) : Prop :=
  ∀ (A : PkgI3.AbVar K), HasSemistableReduction A O →
    ∀ 𝒩 : GroupModelO A O, 𝒩.IsNeronModel →
    ∀ 𝒩' : GroupModelO (A.baseChange K') O', 𝒩'.IsNeronModel →
    letI : GrpObj (bcO hO 𝒩.G) := Functor.grpObjObj
    ∀ c : bcO hO 𝒩.G ⟶ 𝒩'.G, IsMonHom c → IsIso ((Over.pullback (jO O')).map c) →
    ∀ U : (bcO hO 𝒩.G).left.Opens, (U : Set (bcO hO 𝒩.G).left) = idCompSet (bcO hO 𝒩.G) →
      IsOpenImmersion (U.ι ≫ c.left) ∧ Set.range (U.ι ≫ c.left).base = idCompSet 𝒩'.G

/-! ## Pullback bookkeeping -/

section PB

/-- `pbCompIso` preserves the projection to the original group scheme (from the vendored
`CategoryTheory.Over.pullbackComp_hom_app_left_fst_fst`). -/
theorem pbCompIso_fst {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (hfg : f ≫ g = h)
    (𝒢 : Grp (Over Z)) :
    (isoX (pbCompIso f g h hfg 𝒢)).hom.left ≫ pullback.fst 𝒢.X.hom h =
      pullback.fst (pullback.snd 𝒢.X.hom g) f ≫ pullback.fst 𝒢.X.hom g := by
  subst hfg
  have e := Over.pullbackComp_hom_app_left_fst_fst f g 𝒢.X
  have hx : (isoX (pbCompIso f g (f ≫ g) rfl 𝒢)).hom =
      𝟙 _ ≫ (Over.pullbackComp f g).inv.app 𝒢.X ≫ 𝟙 _ := by
    rw [pbCompIso_eq]; rfl
  rw [hx, Category.id_comp, Category.comp_id, ← e]
  have h2 : ((Over.pullbackComp f g).inv.app 𝒢.X).left ≫ ((Over.pullbackComp f g).hom.app 𝒢.X).left =
      𝟙 _ := by
    rw [← Over.comp_left, ← NatTrans.comp_app, Iso.inv_hom_id]; rfl
  calc _ = (((Over.pullbackComp f g).inv.app 𝒢.X).left ≫ ((Over.pullbackComp f g).hom.app 𝒢.X).left) ≫
        pullback.fst (pullback.snd 𝒢.X.hom g) f ≫ pullback.fst 𝒢.X.hom g := by
          simp only [Category.assoc]; rfl
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
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) p :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
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

/-! ## The core: the statement at `(O, O')` from the statement at strict henselizations `(P, P')` -/

/-- **Descent from strict henselizations.** `P ⊇ O`, `P' ⊇ O'` with `IsSHNeronExt` (Néron models base
change), `P' ∩ E = P`: the statement at `(P, P')` implies the statement at `(O, O')`. -/
theorem body_of_SH {K K' : Type} [Field K] [Field K'] [Algebra K K'] {O : ValuationSubring K}
    {O' : ValuationSubring K'} [IsDiscreteValuationRing O] [IsDiscreteValuationRing O']
    (hO : O'.comap (algebraMap K K') = O) {E E' : Type} [Field E] [Field E'] [Algebra K E]
    [Algebra K' E'] [Algebra E E'] [Algebra K E'] [IsScalarTower K E E'] [IsScalarTower K K' E']
    {P : ValuationSubring E} {P' : ValuationSubring E'} [IsDiscreteValuationRing P]
    [IsDiscreteValuationRing P'] (hP : P.comap (algebraMap K E) = O)
    (hP' : P'.comap (algebraMap K' E') = O') (hSHP : IsSHNeronExt O P hP)
    (hSHP' : IsSHNeronExt O' P' hP') (hPP' : P'.comap (algebraMap E E') = P) (h3 : SGA3_VIB_3_10)
    (hG : AVGlue.GeomConnOfRationalPoint) (h7 : Body P P' hPP') : Body O O' hO := by
  intro A hss 𝒩 h𝒩 𝒩' h𝒩' c hc hciso U hU
  -- the Néron models over `P` and `P'`
  let 𝒩₁ := bcDVR hP 𝒩
  have h𝒩₁ : 𝒩₁.IsNeronModel := hSHP.2.2 A 𝒩 h𝒩
  have hss₁ : HasSemistableReduction (A.baseChange E) P := by
    obtain ⟨𝒩₀, h𝒩₀, hs⟩ := hss
    exact ⟨bcDVR hP 𝒩₀, hSHP.2.2 A 𝒩₀ h𝒩₀, (isSemistable_bcDVR_iff hP hSHP.2.1 𝒩₀).mp hs⟩
  have he : IsMonHom (bcbcIso A E E' ≪≫ (bcbcIso A K' E').symm).hom := by
    haveI := bcbcIso_isMonHom A E E'
    have : IsMonHom (bcbcIso A K' E').inv := by
      haveI := bcbcIso_isMonHom A K' E'
      infer_instance
    exact @instIsMonHomComp _ _ _ _ _ _ _ _ _ _ _ (bcbcIso_isMonHom A E E') this
  let 𝒩'₁ : GroupModelO ((A.baseChange E).baseChange E') P' :=
    (bcDVR hP' 𝒩').transport (bcbcIso A E E' ≪≫ (bcbcIso A K' E').symm) he
  have h𝒩'₁ : 𝒩'₁.IsNeronModel :=
    GroupModelO.transport_isNeronModel _ he _ (hSHP'.2.2 (A.baseChange K') 𝒩' h𝒩')
  -- the square of bases `O → O' → P'`, `O → P → P'`
  have sq : gD hP' ≫ gD hO = gD hPP' ≫ gD hP := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    show algebraMap K' E' (algebraMap K K' (x : K)) = algebraMap E E' (algebraMap K E (x : K))
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  -- the comparison map over `P'`
  let Y := bcO hO 𝒩.G
  letI : GrpObj Y := Functor.grpObjObj
  let Y₁ := bcO hPP' 𝒩₁.G
  letI : GrpObj Y₁ := Functor.grpObjObj
  haveI : Smooth Y₁.hom := by change Smooth (pullback.snd _ _); infer_instance
  let eIG := pbCompIso (gD hPP') (gD hP) _ rfl (Grp.mk 𝒩.G) ≪≫
    (pbCompIso (gD hP') (gD hO) _ sq (Grp.mk 𝒩.G)).symm
  let eI : Y₁ ≅ (Over.pullback (gD hP')).obj Y := isoX eIG
  let c₁ : Y₁ ⟶ 𝒩'₁.G := eI.hom ≫ (Over.pullback (gD hP')).map c
  haveI := hc
  haveI := hciso
  letI : GrpObj ((Over.pullback (gD hP')).obj Y) := Functor.grpObjObj
  letI : GrpObj ((Over.pullback (gD hP')).obj 𝒩'.G) := Functor.grpObjObj
  have hc₁ : IsMonHom c₁ := by
    have h1 : IsMonHom eI.hom := inferInstanceAs (IsMonHom (isoX eIG).hom)
    have h2 : IsMonHom ((Over.pullback (gD hP')).map c) := inferInstance
    exact @instIsMonHomComp _ _ _ _ _ _ _ _ _ _ _ h1 h2
  have hiso₁ : IsIso ((Over.pullback (jO P')).map c₁) := by
    have n1 := pbCompIso_natural' (jO P') (gD hP') _ (jO_gD hP') c
    have n2 := pbCompIso_natural' (sKK (K := K') (K' := E')) (jO O') _ rfl c
    haveI hA : IsIso ((Over.pullback (sKK (K := K') (K' := E') ≫ jO O')).map c) := by
      have : IsIso ((Over.pullback (sKK (K := K') (K' := E'))).map ((Over.pullback (jO O')).map c) ≫
          (isoX (pbCompIso (sKK (K := K') (K' := E')) (jO O') _ rfl (Grp.mk 𝒩'.G))).hom) := by
        exact @IsIso.comp_isIso _ _ _ _ _ _ _ (Functor.map_isIso _ _) (Iso.isIso_hom _)
      rw [n2] at this
      exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ (Iso.isIso_hom _) this
    haveI : IsIso ((Over.pullback (jO P')).map ((Over.pullback (gD hP')).map c)) := by
      have : IsIso ((isoX (pbCompIso (jO P') (gD hP') _ (jO_gD hP') (Grp.mk Y))).hom ≫
          (Over.pullback (sKK (K := K') (K' := E') ≫ jO O')).map c) :=
        @IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_hom _) hA
      rw [← n1] at this
      exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ (Iso.isIso_hom _) this
    show IsIso ((Over.pullback (jO P')).map (eI.hom ≫ (Over.pullback (gD hP')).map c))
    rw [Functor.map_comp]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ (Functor.map_isIso _ eI.hom) inferInstance
  let U₁ : Y₁.left.Opens := ⟨idCompSet Y₁, h3 _ Y₁⟩
  obtain ⟨ho₁, hr₁⟩ := h7 (A.baseChange E) hss₁ 𝒩₁ h𝒩₁ 𝒩'₁ h𝒩'₁ c₁ hc₁ hiso₁ U₁ rfl
  -- descent along `Spec P' → Spec O'`
  haveI := (flat_surjective_gD hP').1
  haveI := (flat_surjective_gD hP').2
  haveI : IsIso eI.hom.left := Functor.map_isIso (Over.forget _) eI.hom
  let q : Y₁.left ⟶ Y.left := eI.hom.left ≫ pullback.fst Y.hom (gD hP')
  let p : 𝒩'₁.G.left ⟶ 𝒩'.G.left := pullback.fst 𝒩'.G.hom (gD hP')
  haveI : Surjective p := by show Surjective (pullback.fst _ _); infer_instance
  haveI : Flat p := by show Flat (pullback.fst _ _); infer_instance
  haveI : QuasiCompact p := by show QuasiCompact (pullback.fst _ _); infer_instance
  have hsq : IsPullback c₁.left q p c.left := isPullback_bc_iso (gD hP') c eI.hom.left
  have hq : q ≫ pullback.fst 𝒩.G.hom (gD hO) =
      pullback.fst 𝒩₁.G.hom (gD hPP') ≫ pullback.fst 𝒩.G.hom (gD hP) := by
    have e1 := pbCompIso_fst (gD hPP') (gD hP) _ rfl (Grp.mk 𝒩.G)
    have e2 := pbCompIso_inv_fst (gD hP') (gD hO) _ sq (Grp.mk 𝒩.G)
    have hE : eI.hom.left = (isoX (pbCompIso (gD hPP') (gD hP) _ rfl (Grp.mk 𝒩.G))).hom.left ≫
        (isoX (pbCompIso (gD hP') (gD hO) _ sq (Grp.mk 𝒩.G))).inv.left := rfl
    have e2' : (isoX (pbCompIso (gD hP') (gD hO) _ sq (Grp.mk 𝒩.G))).inv.left ≫
        pullback.fst Y.hom (gD hP') ≫ pullback.fst 𝒩.G.hom (gD hO) =
        pullback.fst 𝒩.G.hom (gD hPP' ≫ gD hP) := e2
    show (eI.hom.left ≫ pullback.fst Y.hom (gD hP')) ≫ pullback.fst 𝒩.G.hom (gD hO) = _
    rw [hE]
    refine Eq.trans ?_ (Eq.trans (congrArg
      ((isoX (pbCompIso (gD hPP') (gD hP) _ rfl (Grp.mk 𝒩.G))).hom.left ≫ ·) e2') e1)
    exact (Category.assoc _ _ _).trans (Category.assoc _ _ _)
  have hU₁ : (U₁ : Set Y₁.left) = q.base ⁻¹' U := by
    have i1 : pullback.fst 𝒩.G.hom (gD hO) ⁻¹' idCompSet 𝒩.G = idCompSet Y :=
      idComp_baseChange h3 hG (gD hO) 𝒩.G
    have i2 : pullback.fst 𝒩.G.hom (gD hP) ⁻¹' idCompSet 𝒩.G = idCompSet 𝒩₁.G :=
      idComp_baseChange h3 hG (gD hP) 𝒩.G
    have i3 : pullback.fst 𝒩₁.G.hom (gD hPP') ⁻¹' idCompSet 𝒩₁.G = idCompSet Y₁ :=
      idComp_baseChange h3 hG (gD hPP') 𝒩₁.G
    show idCompSet Y₁ = q.base ⁻¹' (U : Set Y.left)
    rw [hU, ← i1, ← i3, ← i2]
    ext x
    show (pullback.fst 𝒩.G.hom (gD hP)) ((pullback.fst 𝒩₁.G.hom (gD hPP')) x) ∈ idCompSet 𝒩.G ↔
      (pullback.fst 𝒩.G.hom (gD hO)) (q x) ∈ idCompSet 𝒩.G
    exact (Iff.of_eq (congrArg (fun f : Y₁.left ⟶ 𝒩.G.left => f x ∈ idCompSet 𝒩.G) hq)).symm
  have hT : p.base ⁻¹' idCompSet 𝒩'.G = idCompSet 𝒩'₁.G := idComp_baseChange h3 hG (gD hP') 𝒩'.G
  exact descend_openImm U c.left c₁.left q p hsq U₁ hU₁ ho₁ _ _ hT hr₁

/-! ## The field and its restricted form -/

/-- **The field `sga7_IX_3_3`, exactly** (`CToPrinted.SGA7_IX_3_3`), from its strictly henselian form
`SGA7_IX_3_3_SH` and three leaves already in the bundles: gt-shpair's Néron leaf
`GapSHPair.NeronBaseChangeStrictHenselization` (BLR 1.2/2), SGA 3 VI_B 3.10 and Stacks 04KV. -/
theorem sga7_IX_3_3_of_SH (h7 : SGA7_IX_3_3_SH) (hN : GapSHPair.NeronBaseChangeStrictHenselization)
    (h3 : SGA3_VIB_3_10) (hG : AVGlue.GeomConnOfRationalPoint) : SGA7_IX_3_3 := by
  intro K _ O _ K' _ _ _ O' _ hO
  obtain ⟨E, E', _, _, _, _, _, _, _, _, _, P, P', hP, hP', hSHP, hSHP', hPP'⟩ :=
    GapSHPair.strictHenselizationPair_of_neron hN K O K' O' hO
  haveI : IsDiscreteValuationRing P := hSHP.1.1
  haveI : IsDiscreteValuationRing P' := hSHP'.1.1
  exact body_of_SH hO hP hP' hSHP hSHP' hPP' h3 hG (h7 E P hSHP.1 E' P' hSHP'.1 hPP')

/-- **`SGA7_IX_3_3cp`** (the field with `[CharZero K]`, `[PerfectField κ(O)]`) from the restricted leaf
`SGA7_IX_3_3_SHcp` and the same three bundle leaves. The strict henselization `E` has characteristic 0
and `κ(P)` is algebraic over the perfect `κ(O)`, hence perfect (`ReductB.perfectField_of_isSHNeronExt`). -/
theorem sga7_IX_3_3cp_of_SHcp (h7 : SGA7_IX_3_3_SHcp)
    (hN : GapSHPair.NeronBaseChangeStrictHenselization) (h3 : SGA3_VIB_3_10)
    (hG : AVGlue.GeomConnOfRationalPoint) : SGA7_IX_3_3cp := by
  intro K _ _ O _ _ K' _ _ _ O' _ hO
  obtain ⟨E, E', _, _, _, _, _, _, _, _, _, P, P', hP, hP', hSHP, hSHP', hPP'⟩ :=
    GapSHPair.strictHenselizationPair_of_neron hN K O K' O' hO
  haveI : IsDiscreteValuationRing P := hSHP.1.1
  haveI : IsDiscreteValuationRing P' := hSHP'.1.1
  haveI : CharZero E := ReductB.charZero_of_algebra K E
  haveI : PerfectField (IsLocalRing.ResidueField P) := ReductB.perfectField_of_isSHNeronExt hSHP
  exact body_of_SH hO hP hP' hSHP hSHP' hPP' h3 hG (h7 E P hSHP.1 E' P' hSHP'.1 hPP')

/-! ## The one consumer, rerouted through `SGA7_IX_3_3cp`

`CToPrinted.semistableNeronBaseChange_of_printed_full` uses `SGA7_IX_3_3` once, through
`CToPrinted.identityComponentBaseChangeDVRRange_of`, at a number field `L` and a DVR `O` of `L`. The two
proofs are restated below with `SGA7_IX_3_3cp`; the only changes are the hypothesis, the restricted Prop
`IdentityComponentBaseChangeDVRRangeCP` and one `haveI` for `PerfectField κ(O)`. -/

/-- `CToPrinted.IdentityComponentBaseChangeDVRRange` with `[CharZero K]` and `[PerfectField κ(O)]`. -/
def IdentityComponentBaseChangeDVRRangeCP : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [PerfectField (IsLocalRing.ResidueField O)]
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

/-- `CToPrinted.identityComponentBaseChangeDVRRange_of` with `SGA7_IX_3_3cp`. -/
theorem identityComponentBaseChangeDVRRangeCP_of (h3 : SGA3_VIB_3_10) (h7 : SGA7_IX_3_3cp)
    (hG : AVGlue.GeomConnOfRationalPoint) : IdentityComponentBaseChangeDVRRangeCP := by
  intro K _ _ O _ _ K' _ _ _ O' _ hO A hss 𝒩 h𝒩 𝒩' h𝒩' U _ i hoi hmi hri
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

open ZInQ.HeightSplit ZInQ.DefFaltings in
/-- **The field `semistableNeronBaseChange` (SS2) with `SGA7_IX_3_3cp`**:
`CToPrinted.semistableNeronBaseChange_of_printed_full` with `h7 : SGA7_IX_3_3cp`. -/
theorem semistableNeronBaseChange_of_printed_cp (hB : BLR_1_2_4) (h3 : SGA3_VIB_3_10)
    (h7 : SGA7_IX_3_3cp) (hE : EGAIV_8_10_5_openImm) (hG : AVGlue.GeomConnOfRationalPoint) :
    ZInQ.HeightSplit.SemistableNeronBaseChange := by
  have hIC := identityComponentOLRange_of h3 hG
  have h33 := identityComponentBaseChangeDVRRangeCP_of h3 h7 hG
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
  haveI : PerfectField (IsLocalRing.ResidueField O) := ReductB.perfectField_residue_nf O
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

/-- **SS2 from the restricted leaf**: `semistableNeronBaseChange` from BLR 1.2/4, SGA 3 VI_B 3.10, the
restricted SGA 7 IX 3.3 `SGA7_IX_3_3_SHcp`, BLR 1.2/2 (`NeronBaseChangeStrictHenselization`), EGA IV 8.10.5
and Stacks 04KV. This is the term a fold uses at the consumer sites in place of
`CToPrinted.semistableNeronBaseChange_of_printed_full hB h3 h7 hE hG`. -/
theorem semistableNeronBaseChange_of_SHcp (hB : BLR_1_2_4) (h3 : SGA3_VIB_3_10)
    (h7 : SGA7_IX_3_3_SHcp) (hN : GapSHPair.NeronBaseChangeStrictHenselization)
    (hE : EGAIV_8_10_5_openImm) (hG : AVGlue.GeomConnOfRationalPoint) :
    ZInQ.HeightSplit.SemistableNeronBaseChange :=
  semistableNeronBaseChange_of_printed_cp hB h3 (sga7_IX_3_3cp_of_SHcp h7 hN h3 hG) hE hG

end SGA7PersistsNF

import ZInQKernel.Contrib.OneProof.SGA7PersistsNF

/-!
# `SGA7PersistsNF.SGA7_IX_3_3_SH` from SGA 7 IX 3.3 with `N⁰ ×_S S'` as printed (task dict-models)

The research field `sga7_IX_3_3_SH` (`SGA7PersistsNF.SGA7_IX_3_3_SH`) asks, for the open `U` of `N ×_O O'` with
`U = idCompSet (N ×_O O')` (the identity component of the base change), that `U → N'` be an open immersion with
image `N'⁰`. The print (SGA 7 I, Exp. IX, Prop. 3.3, second assertion) speaks of `N⁰ ×_S S'`, the base change of
the open subscheme `N⁰ ⊆ N`, i.e. the open `pullback.fst ⁻¹' N⁰` of `N ×_S S'`. The two opens agree only through
SGA 3 VI_B 3.3 (the identity component commutes with base change), which the 11-16 dictionary pass counted against
the row.

This file states the leaf with `U := pullback.fst ⁻¹' idCompSet N` (`SGA7_IX_3_3_SHpre`, the print's `N⁰ ×_S S'`)
and proves the field from it, with the two bundle leaves `CToPrinted.SGA3_VIB_3_10` and
`AVGlue.GeomConnOfRationalPoint`, through the chain's `CToPrinted.idComp_baseChange` (SGA 3 VI_B 3.3, proved in
`ZInQKernel/Contrib/OneProof/H/TailZ19.lean` from those two leaves).

* `DictModels.SGA7Pre.SGA7_IX_3_3_SHpre : Prop` — the new LEAF;
* `DictModels.SGA7Pre.sga7_IX_3_3_SH_of_pre : SGA7_IX_3_3_SHpre → SGA3_VIB_3_10 → GeomConnOfRationalPoint →
    SGA7PersistsNF.SGA7_IX_3_3_SH` — the field, exactly;
* `DictModels.SGA7Pre.pre_of_SH` — conversely the field gives the new leaf (with the same two bundle leaves), so
  the two are equivalent modulo the bundle.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReductSplit ReductGlue CToPrinted

namespace DictModels.SGA7Pre

/-- **LEAF `SGA7_IX_3_3_SHpre`** (Grothendieck, SGA 7 I, Exp. IX, Prop. 3.3, second assertion, over strictly
henselian traits; number and wording recalled, UNVERIFIED, no network). *Printed* (as recalled): `S' → S` a
morphism of traits, `A_K` with semistable reduction, `N`, `N'` the Néron models of `A_K` over `S` and of `A_{K'}`
over `S'`; then `N ×_S S' → N'` induces an isomorphism `N⁰ ×_S S' ≅ N'⁰`.

*Lean form*: `SGA7PersistsNF.SGA7_IX_3_3_SH` word for word, except that the open `U` of `N ×_O O'` is the print's
`N⁰ ×_S S'`, the preimage of `N⁰ = idCompSet N` under the projection `pullback.fst : N ×_O O' → N` (the base change
of the open immersion `N⁰ → N`), instead of the identity component of `N ×_O O'`. The conclusion "`U → N'` is an open
immersion with image `N'⁰`" is "`N⁰ ×_S S' → N'⁰` is an isomorphism" (`N'⁰` is open, SGA 3 VI_B 3.10). As in the
field, `c` is any homomorphism whose generic fibre is an isomorphism (the canonical one composed with an
automorphism of `N'`, which preserves `N'⁰`), and `K'/K` is finite (a specialization). -/
def SGA7_IX_3_3_SHpre : Prop :=
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
    ∀ U : (bcO hO 𝒩.G).left.Opens,
      (U : Set (bcO hO 𝒩.G).left) =
        pullback.fst 𝒩.G.hom (Spec.map (CommRingCat.ofHom (comapHom hO))) ⁻¹' idCompSet 𝒩.G →
      IsOpenImmersion (U.ι ≫ c.left) ∧ Set.range (U.ι ≫ c.left).base = idCompSet 𝒩'.G

/-- The two opens agree: `pullback.fst ⁻¹' N⁰ = (N ×_O O')⁰` (SGA 3 VI_B 3.3, the chain's `idComp_baseChange`). -/
theorem preimage_eq {K K' : Type} [Field K] [Field K'] [Algebra K K'] {O : ValuationSubring K}
    [IsDiscreteValuationRing O] {O' : ValuationSubring K'} (hO : O'.comap (algebraMap K K') = O)
    {A : PkgI3.AbVar K} (𝒩 : GroupModelO A O) (h3 : SGA3_VIB_3_10) (hG : AVGlue.GeomConnOfRationalPoint) :
    letI : GrpObj (bcO hO 𝒩.G) := Functor.grpObjObj
    pullback.fst 𝒩.G.hom (Spec.map (CommRingCat.ofHom (comapHom hO))) ⁻¹' idCompSet 𝒩.G =
      idCompSet (bcO hO 𝒩.G) :=
  idComp_baseChange h3 hG (Spec.map (CommRingCat.ofHom (comapHom hO))) 𝒩.G

/-- **The field `sga7_IX_3_3_SH`, exactly**, from the print's form `SGA7_IX_3_3_SHpre` and the bundle leaves
`SGA3_VIB_3_10` (research) and `GeomConnOfRationalPoint` (textbook). -/
theorem sga7_IX_3_3_SH_of_pre (h : SGA7_IX_3_3_SHpre) (h3 : SGA3_VIB_3_10)
    (hG : AVGlue.GeomConnOfRationalPoint) : SGA7PersistsNF.SGA7_IX_3_3_SH := by
  intro K _ O _ hS K' _ _ _ O' _ hS' hO A hA 𝒩 h𝒩 𝒩' h𝒩' c hc hci U hU
  exact h K O hS K' O' hS' hO A hA 𝒩 h𝒩 𝒩' h𝒩' c hc hci U (hU.trans (preimage_eq hO 𝒩 h3 hG).symm)

/-- Conversely, the field gives the new leaf (with the same two bundle leaves). -/
theorem pre_of_SH (h : SGA7PersistsNF.SGA7_IX_3_3_SH) (h3 : SGA3_VIB_3_10)
    (hG : AVGlue.GeomConnOfRationalPoint) : SGA7_IX_3_3_SHpre := by
  intro K _ O _ hS K' _ _ _ O' _ hS' hO A hA 𝒩 h𝒩 𝒩' h𝒩' c hc hci U hU
  exact h K O hS K' O' hS' hO A hA 𝒩 h𝒩 𝒩' h𝒩' c hc hci U (hU.trans (preimage_eq hO 𝒩 h3 hG))

end DictModels.SGA7Pre

end

import ZInQKernel.Contrib.OneProof.SGA7IX33SHPre
import ZInQKernel.Contrib.OneProof.PersistsDVR

/-!
# SGA 7 IX 3.3 (second assertion) over traits with algebraically closed residue field (task sga33-shpre)

The research field `sga7_IX_3_3_SHpre` (`DictModels.SGA7Pre.SGA7_IX_3_3_SHpre`, kind published, strict GLUE) is
SGA 7 I, Exp. IX, Prop. 3.3, second assertion (`N⁰ ×_S S' ≅ N'⁰` for semistable reduction), over strictly
henselian traits. It is rated GLUE for one reading risk only: SGA 7 IX may assume an algebraically closed residue
field, and then the print is the restriction of the field to such traits.

This file states that restriction and shows it is all the chain uses.

* `SGA7_IX_3_3_SHpreAC : Prop` — the new leaf: `SGA7_IX_3_3_SHpre` word for word with
  `[IsAlgClosed κ(O)]` and `[IsAlgClosed κ(O')]` added. A specialization of the field (`preAC_of_pre`), and of every
  reading of the print.
* `SGA7_IX_3_3_SHcp_of_preAC` — gt-sga7's restricted leaf `SGA7PersistsNF.SGA7_IX_3_3_SHcp`
  (characteristic 0, perfect residue field) from the new leaf with the bundle leaves `SGA3_VIB_3_10` and
  `GeomConnOfRationalPoint`.
* `semistablePersistsDVRcp_of_cp`, `semistablePersistsSHcp_of_preAC` — the consumer `semistablePersistsSHcp`
  (`ReductB.SemistablePersistsSHcp`, filled at `TailZ41` from `sga7_IX_3_3_SH`) from the new leaf.
* `semistableNeronBaseChange_of_preAC` — the consumer `semistableNeronBaseChange` (SS2, filled at `TailZ23` from
  `sga7_IX_3_3` through `sga7_IX_3_3_of_SH` at `TailZ33`) from the new leaf.

These are the only two places where the chain reads `sga7_IX_3_3_SHpre` (through `sga7_IX_3_3_SH` and
`sga7_IX_3_3`); both are at characteristic 0 with perfect residue field.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReductSplit ReductGlue CToPrinted

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace DictModels.SGA7PreAC

/-- **LEAF `SGA7_IX_3_3_SHpreAC`** (Grothendieck, SGA 7 I, Exp. IX, Prop. 3.3, second assertion, over strictly
henselian traits with algebraically closed residue fields; number and wording recalled, UNVERIFIED, no network).
*Printed* (as recalled): `S' → S` a morphism of traits, `A_K` with semistable reduction, `N`, `N'` the Néron models
of `A_K` over `S` and of `A_{K'}` over `S'`; then `N ×_S S' → N'` induces an isomorphism `N⁰ ×_S S' ≅ N'⁰`.

*Lean form*: `DictModels.SGA7Pre.SGA7_IX_3_3_SHpre` word for word with `[IsAlgClosed κ(O)]` and
`[IsAlgClosed κ(O')]` added (the second follows from the first, `κ(O')` being algebraic over `κ(O)`; it is stated so
that the leaf is a specialization even if the print's convention puts the hypothesis on both traits). `U` is the
print's `N⁰ ×_S S'` (the preimage of `N⁰` under the projection `N ×_O O' → N`). `c` is any homomorphism whose generic
fibre is an isomorphism (the canonical one composed with an automorphism of `N'`, which preserves `N'⁰`); `K'/K` is
finite. With algebraically closed residue fields the two readings of "semistable" (over `k(s)` or over `k̄`) agree. -/
def SGA7_IX_3_3_SHpreAC : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [IsAlgClosed (IsLocalRing.ResidueField O)],
    IsStrictlyHenselianDVR O →
    ∀ (K' : Type) [Field K'] [Algebra K K'] [FiniteDimensional K K'] (O' : ValuationSubring K')
    [IsDiscreteValuationRing O'] [IsAlgClosed (IsLocalRing.ResidueField O')], IsStrictlyHenselianDVR O' →
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

/-- The new leaf is a specialization of the field `SGA7_IX_3_3_SHpre` (never stronger). -/
theorem preAC_of_pre (h : DictModels.SGA7Pre.SGA7_IX_3_3_SHpre) : SGA7_IX_3_3_SHpreAC :=
  fun K _ O _ _ hS K' _ _ _ O' _ _ hS' hO A => h K O hS K' O' hS' hO A

/-- The residue field of a strictly henselian DVR with perfect residue field is algebraically closed. -/
theorem isAlgClosed_of_SH_perfect {K : Type} [Field K] {O : ValuationSubring K}
    [PerfectField (IsLocalRing.ResidueField O)] (hS : IsStrictlyHenselianDVR O) :
    IsAlgClosed (IsLocalRing.ResidueField O) := by
  haveI : IsSepClosed (IsLocalRing.ResidueField O) := hS.2.2
  infer_instance

/-- **gt-sga7's restricted leaf `SGA7_IX_3_3_SHcp` from the new leaf**, with `SGA3_VIB_3_10` and
`GeomConnOfRationalPoint` (the two opens agree by `DictModels.SGA7Pre.preimage_eq`). Both residue fields are
algebraically closed: `κ(O)` is perfect and separably closed, and `κ(O')` is algebraic over it
(`GapPersists.isAlgebraic_resMap`), hence perfect, and separably closed. -/
theorem SGA7_IX_3_3_SHcp_of_preAC (h : SGA7_IX_3_3_SHpreAC) (h3 : SGA3_VIB_3_10)
    (hG : AVGlue.GeomConnOfRationalPoint) : SGA7PersistsNF.SGA7_IX_3_3_SHcp := by
  intro K _ _ O _ _ hS K' _ _ _ O' _ hS' hO A hA 𝒩 h𝒩 𝒩' h𝒩' c hc hci U hU
  haveI : IsAlgClosed (IsLocalRing.ResidueField O) := isAlgClosed_of_SH_perfect hS
  haveI : PerfectField (IsLocalRing.ResidueField O') := by
    letI := (ReductGlue.resMap hO).toAlgebra
    haveI := GapPersists.isAlgebraic_resMap hO
    exact Algebra.IsAlgebraic.perfectField (IsLocalRing.ResidueField O)
  haveI : IsAlgClosed (IsLocalRing.ResidueField O') := isAlgClosed_of_SH_perfect hS'
  exact h K O hS K' O' hS' hO A hA 𝒩 h𝒩 𝒩' h𝒩' c hc hci U
    (hU.trans (DictModels.SGA7Pre.preimage_eq hO 𝒩 h3 hG).symm)

end DictModels.SGA7PreAC

namespace GapPersists

open ReductSplit ReductGlue CToPrinted in
/-- **`SemistablePersistsDVR` at characteristic 0 with perfect residue field, from `SGA7_IX_3_3cp`**:
`GapPersists.semistablePersistsDVR_of_printed` with `h7 : SGA7PersistsNF.SGA7_IX_3_3cp` (the only change:
`identityComponentBaseChangeDVRRangeCP_of` in place of `identityComponentBaseChangeDVRRange_of`). -/
theorem semistablePersistsDVRcp_of_cp (h3 : CToPrinted.SGA3_VIB_3_10) (h7 : SGA7PersistsNF.SGA7_IX_3_3cp)
    (hG : AVGlue.GeomConnOfRationalPoint) :
    ∀ (K : Type) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
      [PerfectField (IsLocalRing.ResidueField O)]
      (K' : Type) [Field K'] [Algebra K K'] [FiniteDimensional K K'] (O' : ValuationSubring K')
      [IsDiscreteValuationRing O'], O'.comap (algebraMap K K') = O →
      ∀ A : PkgI3.AbVar K, HasSemistableReduction A O → SemistableNeronModels (A.baseChange K') O' := by
  intro K _ _ O _ _ K' _ _ _ O' _ hO A hA 𝒩' h𝒩'
  obtain ⟨𝒩, h𝒩, hs⟩ := hA
  have hsN : (bcDVR hO 𝒩).IsSemistable := (isSemistable_bcDVR_iff hO (isAlgebraic_resMap hO) 𝒩).mp hs
  have gc := idCompSubgroup_of h3 hG
  let W : 𝒩.G.left.Opens := ⟨idCompSet 𝒩.G, h3 _ 𝒩.G⟩
  have hW : OpenSub.IsSubgroupOpen 𝒩.G W :=
    { one := fun s => idCompSet_one 𝒩.G s
      mul := (gc _ 𝒩.G).1
      inv := (gc _ 𝒩.G).2 }
  letI : GrpObj (OpenSub.G0 W) := OpenSub.grpG0 hW
  have hmon : IsMonHom (OpenSub.incl W) := OpenSub.isMonHom_incl hW
  have hoi : IsOpenImmersion (OpenSub.incl W).left := show IsOpenImmersion W.ι from inferInstance
  have hri : Set.range (OpenSub.incl W).left = idCompSet 𝒩.G := Scheme.Opens.range_ι W
  obtain ⟨j, hj, hjm⟩ := SGA7PersistsNF.identityComponentBaseChangeDVRRangeCP_of h3 h7 hG K O K' O' hO A
    ⟨𝒩, h𝒩, hs⟩ 𝒩 h𝒩 𝒩' h𝒩' (OpenSub.G0 W) (OpenSub.incl W) hoi hmon hri
  let g := Spec.map (CommRingCat.ofHom (comapHom hO))
  letI : GrpObj ((Over.pullback g).obj (OpenSub.G0 W)) := Functor.grpObjObj
  letI : GrpObj (bcO hO 𝒩.G) := Functor.grpObjObj
  let k := (Over.pullback g).map (OpenSub.incl W)
  haveI : IsOpenImmersion (OpenSub.incl W).left := hoi
  have hk : IsOpenImmersion k.left := ZInQ.H5Glue.isOpenImmersion_pullback_map _ _
  have hkm : IsMonHom k := inferInstance
  have hkmap : k.left = pullback.map (OpenSub.G0 W).hom g 𝒩.G.hom g (OpenSub.incl W).left (𝟙 _) (𝟙 _)
      (by simp) (by simp) := by
    apply pullback.hom_ext <;> simp [k, Over.pullback_map_left]
  have hrk : Set.range k.left = idCompSet (bcO hO 𝒩.G) := by
    rw [hkmap, Scheme.Pullback.range_map]
    have hid : Set.range ((𝟙 (Spec (CommRingCat.of O')) : Spec (CommRingCat.of O') ⟶ _) :
        Spec (CommRingCat.of O') → Spec (CommRingCat.of O')) = Set.univ :=
      Set.range_eq_univ.mpr (fun x => ⟨x, rfl⟩)
    rw [hid, Set.preimage_univ, Set.inter_univ, hri]
    exact idCompBaseChangeDVR_of h3 hG K O K' O' hO 𝒩.G
  exact hasSemiAbelian_transfer (Spec.map (CommRingCat.ofHom (algebraMap O' (ResBarO O'))))
    (bcO hO 𝒩.G) 𝒩'.G ((Over.pullback g).obj (OpenSub.G0 W)) k j hk hkm hrk hj hjm hsN

/-- **The consumer `semistablePersistsSHcp` (`ReductB.SemistablePersistsSHcp`) from `SGA7_IX_3_3cp`.** -/
theorem semistablePersistsSHcp_of_cp (h3 : CToPrinted.SGA3_VIB_3_10) (h7 : SGA7PersistsNF.SGA7_IX_3_3cp)
    (hG : AVGlue.GeomConnOfRationalPoint) : ReductB.SemistablePersistsSHcp :=
  fun K _ _ O _ _ _ K' _ _ _ O' _ hO A hA => semistablePersistsDVRcp_of_cp h3 h7 hG K O K' O' hO A hA

end GapPersists

namespace DictModels.SGA7PreAC

/-- `SGA7_IX_3_3cp` (the DVR form at characteristic 0 with perfect residue field) from the new leaf, by gt-sga7's
strict-henselization descent `SGA7PersistsNF.sga7_IX_3_3cp_of_SHcp`. -/
theorem sga7_IX_3_3cp_of_preAC (h : SGA7_IX_3_3_SHpreAC)
    (hN : GapSHPair.NeronBaseChangeStrictHenselization) (h3 : SGA3_VIB_3_10)
    (hG : AVGlue.GeomConnOfRationalPoint) : SGA7PersistsNF.SGA7_IX_3_3cp :=
  SGA7PersistsNF.sga7_IX_3_3cp_of_SHcp (SGA7_IX_3_3_SHcp_of_preAC h h3 hG) hN h3 hG

/-- **Consumer 1** (`TailZ41`): the field `semistablePersistsSHcp` from the new leaf. -/
theorem semistablePersistsSHcp_of_preAC (h3 : SGA3_VIB_3_10) (h : SGA7_IX_3_3_SHpreAC)
    (hN : GapSHPair.NeronBaseChangeStrictHenselization) (hG : AVGlue.GeomConnOfRationalPoint) :
    ReductB.SemistablePersistsSHcp :=
  GapPersists.semistablePersistsSHcp_of_cp h3 (sga7_IX_3_3cp_of_preAC h hN h3 hG) hG

/-- **Consumer 2** (`TailZ23`, through `TailZ33`): the field `semistableNeronBaseChange` (SS2) from the new leaf;
the term a fold uses in place of `CToPrinted.semistableNeronBaseChange_of_printed_full hB h3 h7 hE hG`. -/
theorem semistableNeronBaseChange_of_preAC (hB : BLR_1_2_4) (h3 : SGA3_VIB_3_10) (h : SGA7_IX_3_3_SHpreAC)
    (hN : GapSHPair.NeronBaseChangeStrictHenselization) (hE : EGAIV_8_10_5_openImm)
    (hG : AVGlue.GeomConnOfRationalPoint) : ZInQ.HeightSplit.SemistableNeronBaseChange :=
  SGA7PersistsNF.semistableNeronBaseChange_of_SHcp hB h3 (SGA7_IX_3_3_SHcp_of_preAC h h3 hG) hN hE hG

end DictModels.SGA7PreAC

end

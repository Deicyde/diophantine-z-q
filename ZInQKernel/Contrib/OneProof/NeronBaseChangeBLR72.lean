import ZInQKernel.Contrib.OneProof.StrictHenselizationPair

/-!
# `GapSHPair.NeronBaseChangeStrictHenselization` from BLR 7.2 Thm. 1 in its printed form (task dict-models)

The research field `neronBaseChangeStrictHenselization` is BLR §1.2 Prop. 2 ("Néron models commute with strict
henselization") stated over every extension `O ⊆ O₁` with `IsSHSep O O₁` (strictly henselian DVR, `K₁/K` separable
algebraic, ramification index 1, separable residue extension). Those hypotheses pin `O₁` to `O^sh` only through
EGA IV₄ 18.8.8 (the universal property of the strict henselization), which the 11-16 dictionary pass counted
against the row: the Lean statement is BLR 1.2/2 transported along an isomorphism of bases that is itself a theorem.

BLR §7.2 Thm. 1 is printed, as recalled, for extensions of discrete valuation rings of ramification index 1 with
separable residue extension, with no reference to strict henselizations. Its Lean form over the chain's genuine
objects is reduct-glue's `ReductGlue.NeronBaseChangeUnramifiedDVR` (`ZInQKernel/OneProof/H/TailZ14.lean`), and the
field is its specialization to strictly henselian `O₁` (gt-shpair's
`GapSHPair.neronBaseChangeStrictHenselization_of_unramified`): every clause of `IsSHSep` other than "strictly
henselian" is a hypothesis of the 7.2 form, so no pinning is needed.

* `DictModels.NeronBLR72.BLR_7_2_1 : Prop` — the new LEAF (by definition the chain's
  `ReductGlue.NeronBaseChangeUnramifiedDVR`; no new statement);
* `DictModels.NeronBLR72.neronBaseChangeStrictHenselization_of_BLR72 : BLR_7_2_1 →
    GapSHPair.NeronBaseChangeStrictHenselization` — the field, exactly.
-/

noncomputable section

namespace DictModels.NeronBLR72

open ReductSplit ReductGlue

/-- **LEAF `BLR_7_2_1`** (Bosch–Lütkebohmert–Raynaud, *Néron models*, Springer 1990, §7.2 Thm. 1; number and
hypotheses recalled, UNVERIFIED, no network). *Printed* (as recalled): `R → R'` a local homomorphism of discrete
valuation rings of ramification index 1 (a uniformizer of `R` is a uniformizer of `R'`) whose residue extension
`k'/k` is separable, `K'/K` the fraction fields; if a smooth `K`-group scheme of finite type `X_K` has a Néron model
`X` over `R`, then `X ⊗_R R'` is a Néron model of `X_K ⊗_K K'`.

*Lean form*: the chain's `ReductGlue.NeronBaseChangeUnramifiedDVR` (TailZ14), unchanged: `O ⊆ K`, `O' ⊆ K'` DVRs with
`O' ∩ K = O`, `K'/K` separable algebraic (a specialization: the print allows any `K'/K`, as recalled), every
uniformizer of `O` irreducible in `O'`, `κ(O')/κ(O)` separable; `X_K = A` an abelian variety (a specialization);
the base change `bcDVR hO 𝒩` of a Néron model is a Néron model. *Reading risk* (reduct-glue §5): if the print
covers only étale maps, strict henselization and completion, this form exceeds it, and the restricted form is the
old leaf `GapSHPair.NeronBaseChangeStrictHenselization` together with EGA IV₄ 18.8.8. -/
def BLR_7_2_1 : Prop := ReductGlue.NeronBaseChangeUnramifiedDVR

/-- **The field `neronBaseChangeStrictHenselization`, exactly**, from BLR 7.2 Thm. 1 (specialization to
strictly henselian `O₁`). -/
theorem neronBaseChangeStrictHenselization_of_BLR72 (h : BLR_7_2_1) :
    GapSHPair.NeronBaseChangeStrictHenselization :=
  GapSHPair.neronBaseChangeStrictHenselization_of_unramified h

end DictModels.NeronBLR72

end

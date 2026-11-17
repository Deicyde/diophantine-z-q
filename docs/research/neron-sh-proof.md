# neron-sh-proof: `neronBaseChangeStrictHenselization` proved outright (and BLR 7.2/1 with it)

**Verdict.** The research field `neronBaseChangeStrictHenselization`, statement
`GapSHPair.NeronBaseChangeStrictHenselization` (`ZInQKernel/Contrib/OneProof/StrictHenselizationPair.lean:1527`;
bundle field of `OpenResearchLeaves26`), is proved in Lean as stated, from Mathlib and theorems already proved
in the tree. The proof adds **no new leaf**. Every hypothesis of the statement is used except "strictly henselian".
So the proof also gives the stronger chain statement `ReductGlue.NeronBaseChangeUnramifiedDVR`
(`ZInQKernel/OneProof/H/TailZ14.lean:1502`, the BLR 7.2 Thm. 1 form that dict-models proposed as the new leaf
`BLR_7_2_1`). The result holds for every field, in every characteristic, with any residue field, and for any
separable algebraic `K'/K`, finite or not (VERIFIED, compiled).

* `NeronSH.neronBaseChangeStrictHenselization_proof : GapSHPair.NeronBaseChangeStrictHenselization`
* `NeronSH.neronBaseChangeUnramifiedDVR_proof : ReductGlue.NeronBaseChangeUnramifiedDVR`

Both depend only on `[propext, Classical.choice, Quot.sound]` (VERIFIED, `#print axioms`). File:
`ZInQKernel/Contrib/OneProof/NeronBaseChangeStrictHenselization.lean` (56 KB). It imports
`ZInQKernel.Contrib.OneProof.StrictHenselizationPair` (where the statement is defined) and
`ZInQKernel.Contrib.OneProof.BLRLocalizes` (gt-blr's lemmas). It does not import `Main`.

Target met: the field is removed (−1) with no new leaf.

## 1. The checks (all VERIFIED)

| check | outcome |
| --- | --- |
| `lake build +ZInQKernel.Contrib.OneProof.NeronBaseChangeStrictHenselization` | built (68 s; `Main` and `Discharges` already up to date) |
| `#discharges` (`scratch/neron-sh-proof/Discharges.lean`, output `discharges.txt`) | `DISCHARGES [OpenResearchLeaves26.neronBaseChangeStrictHenselization] by NeronSH.neronBaseChangeStrictHenselization_proof`, `still assumes: []`, axioms `[propext, Classical.choice, Quot.sound]` (56 open hypotheses, 2965 theorems checked) |
| verbatim statements (`scratch/neron-sh-proof/Statements.lean`) | copies of `NeronBaseChangeStrictHenselization`, `IsSHSep` and `NeronBaseChangeUnramifiedDVR` are `rfl`-equal to the originals and proved by the two theorems |
| autofold spec `scratch/neron-sh-proof/autofold.json`, `--dry-run` | strict count 34/11 on 45 → 33/11 on 44; strictest 34/11 → 33/11 (`autofold-dryrun.txt`) |
| the dry-run fold module (`scratch/neron-sh-proof/FoldCheck.lean`, the dry run minus its first line) | compiles; `HDec.HSyn.sixContactMin_of_open36` depends on the standard axioms only |

The spec discharges the field with `_root_.NeronSH.neronBaseChangeStrictHenselization_proof` and adds no leaves.

## 2. The proof

The setting is that of `NeronBaseChangeUnramifiedDVR`:

* `O ⊆ K` and `O' ⊆ K'` are DVRs (valuation subrings) with `O' ∩ K = O`;
* `K'/K` is separable algebraic;
* every irreducible element of `O` stays irreducible in `O'`;
* `κ(O')/κ(O)` is separable;
* `𝒩` is a Néron model of `A` over `O` (`GroupModelO.IsNeronModel`).

To show: `bcDVR hO 𝒩 = 𝒩 ×_O O'` is a Néron model of `A_{K'}`.

### Part A: `O'` is ind-étale over `O` (commutative algebra, Mathlib only)

`NeronSH.exists_etale_subalgebra`: every finite subset `s ⊆ O'` lies in an `O`-subalgebra `B ⊆ O'` with
`Algebra.Etale O B`.

1. Let `L = K(s) ⊆ K'`. It is finite and separable over `K`.
2. Let `D` be the integral closure of `O` in `L`. It is finite over `O`, Dedekind, and flat
   (`IsIntegralClosure.finite`, `integralClosure.isDedekindDomain`, and torsion-free over a Dedekind domain).
   `D ⊆ O'`, because `O'` is integrally closed.
3. Let `𝔫 = 𝔪' ∩ D`. Then `D_𝔫` is a DVR, and `ψ : D_𝔫 → O'` is a local homomorphism.
4. `D_𝔫` is unramified over `O` (`Algebra.FormallyUnramified.of_map_maximalIdeal`):
   * a uniformizer `π` of `O` is irreducible in `D_𝔫`, by `Irreducible.of_map` along `ψ`, so `𝔪_O D_𝔫 = 𝔪_{D_𝔫}`;
   * `κ(D_𝔫)` embeds in `κ(O')` over `κ(O)`, so it is separable over `κ(O)`.
5. So `D` is étale at `𝔫` (`Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat`), and there is `f ∉ 𝔫` with `D[1/f]`
   étale over `O` (`Algebra.exists_etale_of_isEtaleAt`).
6. Each `x ∈ s` equals `c/t` with `c, t ∈ D` and `t ∉ 𝔫`. Write `x = a/b` with `a, b ∈ D`. Since `D_𝔫` is a
   valuation ring, `b ∣ a` there. The other case, `a ∣ b`, forces the quotient to be a unit, because `ψ` is local.
7. `B` is the image of `D[1/(f ∏ t)]` in `O'`. It is isomorphic to that localization, hence étale.

Henselianity is never used: this is BLR's "an unramified extension is a filtered colimit of étale ones".

### Part B: Néron models commute with ind-smooth base change

`NeronSH.isNeronModelOver_indSmooth` has three hypotheses:

* `IndSmooth R R₁`: every finite subset of `R₁` lies in an `R`-subalgebra smooth over `R`;
* `R₁ ↪ K₁`;
* `Spec K₁ = Spec R₁ ×_R Spec K`, given as an `IsPullback`.

Under them, `CToPrinted.IsNeronModelOver R K X → IsNeronModelOver R₁ K₁ (X ×_R R₁)`. This is gt-blr's
localization argument (`GapBLR.isNeronModelOver_localization`), with the opens `Spec R[1/s]` replaced by the
smooth subalgebras `B ⊆ R₁`:

1. The smooth subalgebras form a directed set (by `IndSmooth`, since each is finitely generated), and
   `Spec R₁ = lim Spec B` (`specConeIsLimit`).
2. A smooth affine `V → Spec R₁` is `W ×_{Bᵢ} R₁` for a smooth, qc, qs `W → Spec Bᵢ` (`exists_spread`). This uses
   EGA IV 8.8.2 (ii) and 17.7.8 (ii), proved in `ZInQKernel/Contrib/CloudW01Spread`.
3. Over the subalgebras `Bⱼ ⊇ Bᵢ`:
   `V_{K₁} = V ×_R K = lim_j (Spec Bⱼ ×_{Bᵢ} W) ×_R K`.
   This uses the pullback square, `Over.pullback` (a right adjoint), and `Over.forget` (which preserves connected
   limits). The transition maps are affine (`isAffineHom_pullback_map_left`, a base change). Mathlib's
   `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation` (Stacks 01ZC) then descends the given
   `V_{K₁} → X_K` to some stage.
4. That stage `Wⱼ = Spec Bⱼ ×_{Bᵢ} W` is smooth over `R`, since it is smooth over `Spec Bⱼ`, which is smooth over
   `R`. The Néron property of `X` over `R` (`GapBLR.neron_ext`) extends the descended morphism to `Wⱼ → X`, and
   composing with `V → Wⱼ` gives the extension on `V` (`descend_ext`).
5. Uniqueness and gluing over an affine cover are gt-blr's `GapBLR.uqA` and `GapBLR.glue_cover`
   (`glue_ext`, `isNeronModelOver_indSmooth`).

### Part C: assembly

* `isLocalization_K'`: `K'` is the localization of `O'` at the image of `O ∖ 0`. A uniformizer of `O` is
  irreducible in the DVR `O'`, hence a uniformizer there, so every `z ∈ K'` is `u⁻¹ π^{-n}`.
* By Mathlib's `Algebra.isPushout_of_isLocalization`, `CommRingCat.isPushout_iff_isPushout` and
  `isPullback_SpecMap_of_isPushout`, this gives `Spec K' = Spec O' ×_O Spec K` (`isPullback_spec`).
* `GroupModelO.IsNeronModel` is `IsNeronModelOver` up to composition with the isomorphism `gen`
  (`isNeronModelOver_of_groupModelO`, and the same step backwards for `bcDVR`, whose scheme is
  `(Over.pullback (gD hO)).obj 𝒩.G`).
* The residue-field hypothesis, stated with `(resMap hO).toAlgebra`, is moved to Mathlib's
  `ResidueField` algebra instance by `Algebra.algebra_ext`.
* `neronBaseChangeStrictHenselization_proof` is `GapSHPair.neronBaseChangeStrictHenselization_of_unramified`
  applied to `neronBaseChangeUnramifiedDVR_proof`.

## 3. Leaves, glue, ratings

* **New leaves: none.**
* Theorems of the tree used, all proved:
  * `ZInQ.Contrib.SpreadOut.EGAIV_8_8_2_ii_proof` and `EGAIV_17_7_8_ii_proof` (CloudW01Spread);
  * `GapBLR.uqA`, `GapBLR.glue_cover`, `GapBLR.neron_ext` (BLRLocalizes);
  * `GapSHPair.neronBaseChangeStrictHenselization_of_unramified`;
  * `ReductGlue.comapHom_isLocalHom`, `ReductGlue.resMap_residue`.
* No narrowing was needed, so the consumers (`UnipotentForward`, `SGA7PersistsNF`, `PersistsDVR`,
  `StrictHenselizationPair`) need no check: the statement is proved exactly.
* The reading risk that dict-models recorded for `BLR_7_2_1` (the print may cover only étale maps, strict
  henselization and completion) is now moot, because the 7.2/1 form is a Lean theorem.

## 4. For the integrator

* Fold with `scratch/neron-sh-proof/autofold.json`. It discharges `neronBaseChangeStrictHenselization` with no
  leaf; counts 34/11 on 45 → 33/11 on 44.
* dict-models (`wip/dict-models`) has a spec that discharges the same field through the new leaf
  `DictModels.NeronBLR72.BLR_7_2_1`. Use this one instead: it removes the row without adding a leaf. Fold the
  other three fields of dict-models without its `neronBaseChangeStrictHenselization` entry.
* Namespace `NeronSH`. It is new in the tree, and its declaration names do not clash with `GapBLR` (checked by
  the dry-run fold compile, which imports `TailZ42` and the new file together).

## 5. Files

* `ZInQKernel/Contrib/OneProof/NeronBaseChangeStrictHenselization.lean`: the deliverable (Parts A, B, C).
* `scratch/neron-sh-proof/`:
  * `PartA.lean`, `PartB.lean`: the parts as developed;
  * `Full.lean`: the combined file;
  * `Statements.lean`: verbatim copies and `rfl` checks;
  * `Discharges.lean`, `discharges.txt`: the `#discharges` run;
  * `autofold.json`, `autofold-dryrun.txt`, `FoldCheck.lean`: the fold spec, its dry run and its compile check;
  * `log.md`: the results log.

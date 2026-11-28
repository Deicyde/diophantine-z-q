# cmj-reroute: `cmjDegreePrint` removed by a sub-order class-number bound

`cmjDegreePrint` (`HDec.CMBranch.CMjBridges.CMjDegreePrint`; Fowler, Math. Proc. Cambridge Philos.
Soc. 180 (2026), section 2·1, p. 613: a singular modulus of discriminant Δ has degree h(Δ) over ℚ)
leaves the hypotheses of `ZInQ.OneProof.frozenTarget` without a replacement: 33 → 32. The fold is
`OneProof/H/TailZ114.lean` (generation `OpenResearchLeaves85`, top `sixContactMin_of_open107`).

## Where the row was read

`TailZ98` turns the row into the field `cmjDegree : CMBranch.CMjDegree`
(`CMjBridges.cmjDegree_of_print_closed`), which the bundles carry down to the CM-branch package
`CMBranch.CMInputs3` and from there to `CMBranch.cmBranchOut_of`. Its only reader is
`CMBranch.faltingsHeight_le_bcm`: `card Pic(R) ≤ [L:ℚ] ≤ D` for the geometric endomorphism order `R`
of the matrix-unit curve `E/L` of a CM fibre, then Fowler's Prop. 2·7 at `n = D`.

## The replacement (no new row)

* `exists_suborder_card_pic_le_324` (`Descent.lean`): an order `R₀ ≤ R` of the CM field `k` with
  `card Pic(R₀) ≤ 324`. `R₀` is the image in `End(E)` of the order `R' = q⁻¹(𝒪)` of the CM point
  `(K, q, κ)` at the fibre point, which acts centrally on the fibre surface and hence on `E`
  (`Dictionary.lean`, `CMPoint.lean`, `Restrict.lean`, `MatrixUnitRestrict.lean`,
  `Assemble.lean`). `card Pic(R') ≤ 324`: the `Aut(ℂ/κK)`-orbit of the fibre point has at least
  `[H_{R'} : K] = card Pic(R')` points (Shimura's reciprocity law at CM points, as printed in the row
  `deligneCanonicalModelY3EveryPrint`, with the kernel of `C_K → Pic(R')`, `RingClassKernel.lean`,
  and `OrbitBound.lean`), and it stays in one fibre of `Y₃ → P¹_j` over the rational value `J(u)`,
  which has at most 324 points (`y3ToP1j`; `WitnessMatch.lean` matches the moduli witnesses).
* `faltingsHeight_le_bcm_of_sub` (`Consumer.lean`): Fowler's Prop. 2·7 at `n = 324` for `R₀`, with
  `|Δ_R| ≤ |Δ_{R₀}|` (the conductor of `R` divides that of `R₀`) and `324 ≤ D`.
* `SplitBL.lean`: `CMFibreSplitBL`, the CM split with the bound, from the proof of
  `FibreSplit.cmFibreSplit_of` with the fibre point, the model and the curve data kept;
  `LiveBL.lean`: its supplier from the six inputs of `cmFibreSplit_of_liveInputs_nos`;
  `BranchBL.lean`: `cmBranchOut_of_bl` (no `CMjDegree`) and `CMInputs3BL`.

Statements read: `Y3RouteA.Y3FullThreeRepZ30` and `Y3Hodge.DeligneCanonicalModelY3EveryPrint`, both derived
fields of the chain (filled by the conversions of `TailZ111` and, since y3-milne-1128, `TailZ116` from their rows;
the map `Y₃ → P¹_j` is derived from these two), and the row `fowlerProp27PrintCanonical`; the live CM split already
reads all of them.

## What the reroute reads from `Y3Hodge.DeligneCanonicalModelY3EveryPrint`

Since the Deligne fold the statement is not a row: `TailZ112`'s conversion proves it by
`DelignePS.deligneCanonicalModelY3EveryPrint_of_prints` from `voightQMComplexModuliPrint`,
`cornutVatsalCMReciprocityPrint` and `fineModuliCanonicalModelGlue`, and the copy of that conversion in `Chain4.lean`
applies the same term. Since y3-milne-1128 (`TailZ116`) the live route passes through neither: that fold's top
`sixContactMin_of_open109` enters the copy chain at `sixContactMin_of_open104_cmj` (`Chain3.lean`), and its
conversion `openResearchLeaves83CMJ_of_OpenResearchLeaves87` fills the field by
`DelignePSMilne.deligneCanonicalModelY3EveryPrint_of_milne` from `voightQMComplexModuliPrint`,
`boutotCarayolPolarizationPrint`, `boutotCarayolRepresentabilityPrint`, `milneShimuraFamilyPrint` and
`milneCanonicalModelPrint`; the same fold removed `cornutVatsalCMReciprocityPrint` and `fineModuliCanonicalModelGlue`
from the rows. One call site, `exists_deligneCore` (`WitnessMatch.lean`), takes the statement at the printed witness
of `y3FullThreeRepZ30` and transports to the CM branch's witness the clauses it then uses:

| clause of `Y3Hodge.DeligneBodyAtPM` / `ModuliAtUnitsHP` | where | how |
| --- | --- | --- |
| onto | `Assemble.lean`, `DeligneCore.exists_rep_units` | the base change of the `ℚ̄`-point is some `Ψ(z, g)` |
| fibres, `DCRelPM → equal` | the same | moving to an upper representative, then to one at a unit `u ∈ 𝒪̂^×` |
| moduli at units | `Assemble.lean`, `exists_cmOrder_card_pic_le_324` | the QM pair at that `(τ, u)` |
| fibres, `equal → DCRelPM` | `OrbitBound.lean`, `artin_trivial_of_eq` | at the CM point `τ`, between `Ψ(τ, u)` and `Ψ(τ, q̂(s)^ε u)` |
| reciprocity | `OrbitBound.lean`, `artin_trivial_of_galPt_fix`, `card_gal_le_ncard` | at the CM point `τ` of an imaginary quadratic `q`, at `g = u` |

Holomorphy (both clauses) is not read.

## Files

| file | content |
| --- | --- |
| `Restrict.lean`, `MatrixUnitRestrict.lean` | restriction of central endomorphisms to the matrix-unit curve |
| `Dictionary.lean`, `DictionaryProved.lean`, `CMPoint.lean` | the CM dictionary for every order `q⁻¹(𝒪)` |
| `WitnessMatch.lean`, `OrbitBound.lean`, `RingClassKernel.lean` | witness matching, orbit bound, ring-class kernel |
| `Assemble.lean`, `Descent.lean` | `exists_suborder_card_pic_le_324` |
| `Consumer.lean` | `faltingsHeight_le_bcm_of_sub` |
| `Axioms.lean` | `#print axioms` of the lemmas above |
| `SplitBL.lean`, `LiveBL.lean`, `BranchBL.lean` | the split with the bound, its supplier, the CM branch without `CMjDegree` |
| `Chain1.lean`–`Chain4.lean` | the generated copy chain (below) |
| `FoldCheck.lean` | `frozenTarget` over the copied bundle, without `cmjDegreePrint` |
| `gen_cmj.txt`, `walk_cmj.txt` | the generator and its dependency walk |

## The copy chain (generated)

`gen_cmj.txt` (Python) runs `walk_cmj.txt` (a scratch Lean file, run with `lake env lean` on the
built world): from `frozenTarget`, every reached declaration that depends on `CMjDegreePrint`,
`CMjDegree` or `CMFibreSplit` is dirty. The copy set is the closure from the root along dirty
dependencies; copyable declarations lie in generated chain files (blocks starting with
`-- copied from`) or in generation files `OneProof/H/TailZ<n>.lean`, and every other dirty dependency
must be one of a fixed list of replaced constants (`CMInputs3`, `cmBranchOut_of`,
`cmjDegree_of_print_closed`, `cmFibreSplit_of_liveInputs_nos` and the three seeds), or the generator
stops. A block whose declarations are all copied is copied whole; otherwise (another reroute already
replaced some of them) only its copied declarations, in the block's namespace. Edits (each counted
and checked):

* suffix `CMJ` for copied structures, `_cmj` for copied theorems;
* fields `cmjDegreePrint` and `cmjDegree` deleted from the copied bundles, with their assignments
  and the component `r.cmjDegree` of the anonymous `CMInputs3` constructor;
* field type `CMFibreSplit` → `CMjReroute.CMFibreSplitBL`, filled at the existing switch by
  `CMjReroute.cmFibreSplitBL_of_liveInputs_nos` (the same six arguments);
* `CMInputs3` → `CMjReroute.CMInputs3BL`;
* at the base (`sixContactMin_of_open4_cm_u_c8_y3c_nos_ds`) the binder `hJ : CMjDegree` and its use
  deleted, `cmBranchOut_of` → `CMjReroute.cmBranchOut_of_bl`.

At this fold the walk reaches 128344 constants, 556 of them dirty (108 owners). The copy set has 92
declarations: 58 from `DS965Reroute/Chain2`–`Chain5` (the bundle generations
`OpenResearchLeaves63NOSDS`–`OpenResearchLeaves77DS` and the 30 theorems that carry `c : CMInputs3`
down to the base), 18 from `VpDualMerge/Chain.lean`, and 16 from the generations `TailZ105`–`TailZ108`
and `TailZ111`–`TailZ113` (`TailZ109` and `TailZ110` are off the live route since `TailZ111` builds on
`OpenResearchLeaves80`; `TailZ112`'s conversion is copied with its assignment of
`deligneCanonicalModelY3EveryPrint` unchanged); 51 whole blocks, 25 single declarations and 16 generation
declarations, in four files. Edit counts: 20 fields and 19 assignments deleted, 1 anonymous-constructor component, 1
argument, 1 binder, 30 `CMInputs3BL`, 4 `CMFibreSplitBL`, 1 supplier, 1 branch. The copied top is
`HDec.HSyn.sixContactMin_of_open106_cmj (r : OpenResearchLeaves84CMJ) (t : OpenTextbookLeaves18)
(l : OpenAddedLeaves31) : ZInQ.SixContactMin`, where `OpenResearchLeaves84CMJ` is
`OpenResearchLeaves84` without `cmjDegreePrint` (26 fields, each of the live type).

## The fold

`gen_cmj.txt --fold` also writes `OneProof/H/TailZ114.lean`: `OpenResearchLeaves85` (the 26 fields
of `OpenResearchLeaves84CMJ`, with the docstrings of `OpenResearchLeaves84`), the field-by-field
conversion `openResearchLeaves84CMJ_of_OpenResearchLeaves85`, and
`sixContactMin_of_open107 r t l := sixContactMin_of_open106_cmj (conversion r) t l`; and it edits
`Main.lean` (import, bundle and top of `frozenTarget`, one paragraph). The records (kinds.tsv,
reviews.tsv to reviews-retired.*, the blueprint chapter text) are edited by hand.

## Checks

* `FoldCheck.frozenTarget_without_cmjDegreePrint` is `frozenTarget`'s statement over
  `OpenResearchLeaves84CMJ` (the other five binders and the conclusion unchanged), and
  `openResearchLeaves84CMJ_ofLive` gives that bundle from the live one by projections alone.
* After the fold, the constants of the `ZInQKernel.OneProof` modules (`scratch/one-proof/DumpCompact.lean`):
  only `frozenTarget` changed, and the 34 added constants are all in `TailZ114`.
* `#print axioms` of `frozenTarget`, `sixContactMin_of_open107` and the theorems in `FoldCheck.lean`:
  `[propext, Classical.choice, Quot.sound]`.

## Regenerating on a newer main

If another fold lands first, the top theorem and the live chain move. On the newer main, with this
directory but without `Chain*.lean` and `FoldCheck.lean`, and without the fold commit's edits to
`OneProof/` and the records:

1. `lake build +ZInQKernel.OneProof.Main +ZInQKernel.Contrib.OneProof.CMjReroute.BranchBL
   +ZInQKernel.Contrib.OneProof.CMjReroute.LiveBL`.
2. `python3 ZInQKernel/Contrib/OneProof/CMjReroute/gen_cmj.txt --repo . --out
   ZInQKernel/Contrib/OneProof/CMjReroute --scratch <dir> --fold`: the walk reads the top from
   `frozenTarget`, and the fold takes the next free numbers.
3. `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges
   +ZInQKernel.Contrib.OneProof.CMjReroute.FoldCheck`, then the records and the renders.

The generator stops with the list of declarations it cannot copy if a newer chain uses another file
format.

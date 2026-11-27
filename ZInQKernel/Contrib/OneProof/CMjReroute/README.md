# cmj-reroute: `cmjDegreePrint` removed by a sub-order class-number bound

`cmjDegreePrint` (`HDec.CMBranch.CMjBridges.CMjDegreePrint`; Fowler, Math. Proc. Cambridge Philos.
Soc. 180 (2026), section 2·1, p. 613: a singular modulus of discriminant Δ has degree h(Δ) over ℚ)
leaves the hypotheses of `ZInQ.OneProof.frozenTarget` without a replacement: 29 → 28. The fold is
`OneProof/H/TailZ111.lean` (generation `OpenResearchLeaves83`, top `sixContactMin_of_open104`).

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

Rows read: `y3FullThreeRepZ30` (through the derived field below `TailZ110`'s conversion),
`deligneCanonicalModelY3EveryPrint` (the map `Y₃ → P¹_j` is derived from these two in the chain) and
`fowlerProp27PrintCanonical`; the live CM split already reads all of them.

## What the reroute reads from `deligneCanonicalModelY3EveryPrint`

One call site, `exists_deligneCore` (`WitnessMatch.lean`), takes the row at the printed witness of
`y3FullThreeRepZ30` and transports to the CM branch's witness the clauses it then uses:

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
| `Chain1.lean`–`Chain3.lean` | the generated copy chain (below) |
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

At this fold the walk reaches 127818 constants, 523 of them dirty (104 owners). The copy set has 88
declarations: 58 from `DS965Reroute/Chain2`–`Chain5` (the bundle generations
`OpenResearchLeaves63NOSDS`–`OpenResearchLeaves77DS` and the 30 theorems that carry `c : CMInputs3`
down to the base), 18 from `VpDualMerge/Chain.lean`, and 12 from the generations `TailZ105`–`TailZ108`
and `TailZ110` (`TailZ109` is off the live route since `TailZ110` builds on `OpenResearchLeaves80`);
51 whole blocks, 25 single declarations and 12 generation declarations, in three files. Edit counts:
19 fields and 18 assignments deleted, 1 anonymous-constructor component, 1 argument, 1 binder, 30
`CMInputs3BL`, 4 `CMFibreSplitBL`, 1 supplier, 1 branch. The copied top is
`HDec.HSyn.sixContactMin_of_open103_cmj (r : OpenResearchLeaves82CMJ) (t : OpenTextbookLeaves18)
(l : OpenAddedLeaves30) : ZInQ.SixContactMin`, where `OpenResearchLeaves82CMJ` is
`OpenResearchLeaves82` without `cmjDegreePrint` (23 fields, each of the live type).

## The fold

`gen_cmj.txt --fold` also writes `OneProof/H/TailZ111.lean`: `OpenResearchLeaves83` (the 23 fields
of `OpenResearchLeaves82CMJ`, with the docstrings of `OpenResearchLeaves82`), the field-by-field
conversion `openResearchLeaves82CMJ_of_OpenResearchLeaves83`, and
`sixContactMin_of_open104 r t l := sixContactMin_of_open103_cmj (conversion r) t l`; and it edits
`Main.lean` (import, bundle and top of `frozenTarget`, one paragraph). The records (kinds.tsv,
reviews.tsv to reviews-retired.*, the blueprint chapter text) are edited by hand.

## Checks

* `FoldCheck.frozenTarget_without_cmjDegreePrint` is `frozenTarget`'s statement over
  `OpenResearchLeaves82CMJ` (the other five binders and the conclusion unchanged), and
  `openResearchLeaves82CMJ_ofLive` gives that bundle from the live one by projections alone.
* After the fold, the constants of the `ZInQKernel.OneProof` modules (`scratch/one-proof/DumpCompact.lean`):
  only `frozenTarget` changed, and the 31 added constants are all in `TailZ111`.
* `#print axioms` of `frozenTarget`, `sixContactMin_of_open104` and the theorems in `FoldCheck.lean`:
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

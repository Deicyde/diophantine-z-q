# fold34-ht: `hodgeTateDecompAbVar` folded (strict GLUE 18 → 17)

Task fold34-ht (integration), 2026-11-16. Base `wip/leaf-fold33b` c0f3d085c (= origin/main, which had not moved).
Log: `scratch/fold34-ht/log.md`. Replay: `scratch/fold34-ht/REPLAY.md`.

## Result

The open research field `hodgeTateDecompAbVar` (`ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar`,
`ℂ_p ⊗ V_p(A) ≅ ℂ_p(1)^g ⊕ ℂ_p^g`, GLUE/GLUE) is removed from `ZInQ.OneProof.frozenTarget`. It is replaced by
hodgetate-from-dr's printed-form leaf `HodgeTateFromPairing.HodgeTateDecompExists` (Fontaine 1982, both exponents
left unnamed), which is LEAF/LEAF with the flag *"unread: new printed leaf (...); locator UNVERIFIED"*. Counts
(render_open, VERIFIED): **35 open hypotheses (29 H, strictest 12/17, 6 others)**. Before the fold: 35 (29 H,
strictest 11/18). Strict and strictest go 11/18 → 12/17 on 29 fields.

```
theorem ZInQ.Contrib.HodgeTateFromPairing.hodgeTateDecompAbVar_of_open (hHT : HodgeTateDecompExists)
    (hM : AvSplit.MumfordTorsionAlgClosed) (h1 : T09Pic.PicRepresentableAbVar)
    (hK : PicFix.KleimanPicZeroProper) : ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
```

(`ZInQKernel/Contrib/OneProof/HodgeTatePairingCharZero.lean`; axioms `[propext, Classical.choice, Quot.sound]`,
VERIFIED). Its three other inputs were already open fields of this base: `mumfordTorsionAlgClosed` (textbook),
`picRepresentableAbVar` and `kleimanPicZeroProper` (added). So the fold adds no new GLUE and no field other than the leaf.

## Adapting hodgetate-from-dr to this base

hodgetate-from-dr's `hodgeTateDecompAbVar_of_printed` was written against leaf-fold32b. It reads `T09Pic.PicZeroAbVar`,
`PicFix.MumfordKLFiniteSectionAC`, `PicDict.MumfordPhiSurjectiveAC` and `T09Pic.WeilPairingMumford`, which this base
has proved, rerouted or replaced. It still compiles here, but its hypotheses are not fields, so it cannot be folded.
Its core, `hodgeTateDecompAbVar_of_leaves`, takes T9 over every field (`T09_SymmIsogenyExists`) and applies it only at
the base field `F`. `F` is finite over `ℚ_p`, so it has characteristic `0` (the proof already derives `CharZero F`).
Three new modules, each a verbatim copy with T9 in characteristic `0`:

| module | content |
| --- | --- |
| `Contrib/OneProof/HodgeTatePairingWeil0.lean` (imports `TailK`) | `tatePairingZl_field0`, `tateGSp_field0`: `HodgeTatePairingWeil.lean` with `h9` of the type of `PicZeroChar0.T09_SymmIsogenyExists0` (written out, so the module imports only `TailK`; the linear algebra times out in later environments) and `[CharZero K]` |
| `Contrib/OneProof/HodgeTatePairingCore0.lean` | `hodgeTateDecompAbVar_of_leaves0`: Core with the characteristic-`0` T9 |
| `Contrib/OneProof/HodgeTatePairingCharZero.lean` | `t09SymmIsogenyExists0_of_open` (from `picRepresentableAbVar`, `kleimanPicZeroProper`, T5: `PicZeroChar0.picZeroAbVar0_of_leaves` with `PicLFT.picLocFinType_proof` and `IdCompLFT.identityComponentLFT_proof`, then `PhiSurj.t09SymmIsogenyExists0_of_four0` with phisurj's `phiAmpleIsogeny0_of_open`, `weilPairingMumford0_of_open`); `hodgeTateDecompAbVar_of_open` |

The characteristic-`0` T9 statement is a consequence of the general one (`t09SymmIsogenyExists0_of`), never stronger.
Tate's theorems, Ax–Sen–Tate and the isogeny quasi-inverse come from contributions that are already folded, as in
hodgetate-from-dr.

## The fold and its checks (all VERIFIED)

* `#discharges` (`scratch/fold34-ht/Discharges-output.txt`): `OpenResearchLeaves31.hodgeTateDecompAbVar` is discharged
  by `hodgeTateDecompAbVar_of_open`, which still assumes `[HodgeTateDecompExists, MumfordTorsionAlgClosed,
  PicRepresentableAbVar, KleimanPicZeroProper]`, with the standard axioms.
* Autofold `scratch/fold34-ht/autofold.json` wrote `ZInQKernel/OneProof/H/TailZ56.lean`: `OpenResearchLeaves32`,
  `sixContactMin_of_open49`. It also switched Main.lean and changed the kinds.tsv rows: hodgeTateDecompAbVar dropped,
  hodgeTateDecompExists added (published, LEAF/LEAF, flag_class `unread,unverified-locator`). claims.tsv has no row for
  the field.
* `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges` plus the new modules: 14235 jobs, ok.
  `#print axioms ZInQ.OneProof.frozenTarget` gives `[propext, Classical.choice, Quot.sound]`.
* Closure check (271666 constants): no bundle field has type `HodgeTateDecompAbVar`. It appears only as the statement
  proved by `hodgeTateDecompAbVar_of_open`. `sorryAx` is absent, and so are the leaf-fold32b T9 Props and
  `hodgeTateDecompAbVar_of_printed`.
* Hash guard against the base dump (Main at c0f3d085 rebuilt): 15751 → 15783 constants. Nothing is removed, 32 are
  added (all in TailZ56), and only `ZInQ.OneProof.frozenTarget` changed.
* OpenStatements: 35. `render_open.py` and `--check`: ok. `frontier_crosswalk.py` and `--check`: ok (232 IDs, 25
  matched). `DischargesTest` rerun. `autoform check blueprint`: OK (781 articles, 2343 dependencies).

## Merge hygiene

`scratch/hodgetate-from-dr/AutofoldDry.lean` redeclares HDec.HSyn bundles, so it was renamed `.lean.txt`. A host path
was removed from `scratch/hodgetate-from-dr/log.md`. The merged branch has no vendored code.

## Notes

* The leaf's rating is hodgetate-from-dr's: Fontaine's printed decomposition with bases chosen and no dimension used.
  Its locator is UNVERIFIED (no network). The `locators.md` row that hodgetate-from-dr proposed is still not added,
  since that file belongs to another task.
* Replay on a later head: `scratch/fold34-ht/REPLAY.md`. It needs the Contrib commits 301197af6 and 9a7266d8a, then
  autofold of the spec. If `kleimanPicZeroProper` or `picRepresentableAbVar` has been proved by then, put its proof
  term in the spec in place of the field.
* The Main.lean module docstring was not extended for TailZ54–56 (leaf-fold33 did not extend it for 54–55 either).

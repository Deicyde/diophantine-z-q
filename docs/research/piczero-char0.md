# piczero-char0: `picZeroAbVar` is used only in characteristic 0, so it is discharged from three LEAF statements (strict GLUE −1)

Task piczero-char0. Base: wip/leaf-fold33b 0e3c31258 (top `sixContactMin_of_open41`, TailZ48). `origin/main`
(c1e4ed1b8) is already an ancestor, so no merge was needed. Build: a reflink copy of leaf-fold33b's `.lake/build`.

## 1. Verdict

1. **Every use of the field `picZeroAbVar : T09Pic.PicZeroAbVar` in `ZInQ.OneProof.frozenTarget`'s closure is at a
   field of characteristic 0, or is dead.** VERIFIED by a field-level taint of the closure (§2).
2. **The characteristic-0 form is proved from the LEAF statements alone.** It needs neither `PicZeroSmoothPosChar`
   nor any other characteristic-p input:
   `PicZeroChar0.picZeroAbVar0_of_leaves : PicLocFinType → IdentityComponentLFT → KleimanPicZeroProper → PicZeroAbVar0`.
   Cartier's theorem is supplied by `cartierSmooth_proof`. VERIFIED: compiled, standard axioms.
3. **The chain is rerouted to read `PicZeroAbVar0` instead.** Generated module, VERIFIED compiled:
   `HDec.HSyn.sixContactMin_of_open41_pz` proves `ZInQ.SixContactMin` from
   `OpenResearchLeaves29`, `OpenTextbookLeaves15` and `OpenAddedLeaves20PZ`. `OpenAddedLeaves20PZ` is
   `OpenAddedLeaves20` with `picZeroAbVar` weakened to characteristic 0.
4. **Fold.** `FoldCheck.lean` compiles `ZInQ.OneProof.frozenTarget_pz`, on `[propext, Classical.choice, Quot.sound]`.
   It is `frozenTarget` with the added bundle replaced by `OpenAddedLeaves21`, which is `OpenAddedLeaves20` without
   `picZeroAbVar` and with three new fields `picLocFinType`, `identityComponentLFT` and `kleimanPicZeroProper`.

**Count change** (kinds.tsv H rows, computed with autofold.py's `counts`):

| | fields | strict LEAF/GLUE | strictest LEAF/GLUE |
|---|---|---|---|
| before (leaf-fold33b) | 33 | 13 / 20 | 13 / 20 |
| after this fold | 35 | 16 / 19 | 16 / 19 |

So strict GLUE goes from 20 to 19 (−1) and strictest GLUE also from 20 to 19 (−1). No new GLUE is added: the three
new fields are published leaves, flagged unread, and counted LEAF exactly as pic-fix and pic-smooth rated them (§5).

## 2. Step (1): the consumers of `picZeroAbVar`

Two analyses were run on the closure of `ZInQ.OneProof.frozenTarget`, which has 270,264 constants.

* `scratch/piczero-char0/Taint.lean` (output `taint_out.txt`) lists the declarations whose values depend on a
  `*.picZeroAbVar` projection.
* `scratch/piczero-char0/FieldTaint.lean` (output `fieldtaint_out.txt`) is a field-level forward taint. Through a
  bundle map `fun l => S.mk a₁ … aₙ`, only the fields `aᵢ` that read a tainted projection are tainted. Any other
  reader is reported as a terminal consumer.

Both are VERIFIED (run on this tree).

**Fields computed from `picZeroAbVar`, with the map that computes each:**

| map | field computed | reads |
|---|---|---|
| `openAddedLeaves19_of_OpenAddedLeaves20` (TailZ47) | `mumfordKLFiniteSectionAC` | `picZeroAbVar` (`PhiAmple.mumfordKLFiniteSectionAC_of_open`) |
| `openAddedLeaves18_of_OpenAddedLeaves19` (TailZ45) | `phiAmpleIsogeny` | `mumfordKLFiniteSectionAC` (`PicFix.phiAmpleIsogeny_of_printed`) |
| `addedLeaves12_of_open13` (TailZ24) | `t09SymmIsogenyExists` | `picZeroAbVar`, `phiAmpleIsogeny` (`T09Pic.t09SymmIsogenyExists_of_four`) |
| `openTextbookLeaves13_of_OpenTextbookLeaves14_hf` (homfree reroute, the copy of TailZ46's map that is in use) | `poincareComplement` | `picZeroAbVar`, `mumfordKLFiniteSectionAC` (`poincareComplement_of_open`) |
| `textbookLeaves4_of_open6_hf` | `t9` | `t09SymmIsogenyExists` (`t9_of_leaves5`) |
| `textbookLeaves6_of_open7_hf` | `t8` | `poincareComplement` |

**Terminal readers, and the fields `k` each one uses:**

* `HSyn.gluePieces_of_open4_hf` reads `t09SymmIsogenyExists` through `detTate_of_leaves4` and
  `tatePairingZl_of_leaves4`.
  * It is applied at `K` with `[NumberField K]` (TailK.lean:249-254).
  * Characteristic 0.
* `G0Galois.g8_g12_of_leaves3_hf` reads `t9`, which it passes to `g8_g12` and on to `g12`.
  * In `g12`, `t9` is used only as the antecedent of `hD : G12Det` (TailA.lean:2224).
  * `hD := g12Det_of …`, whose proof discards that antecedent (`intro _ _ K …`, TailA.lean:2449).
  * Dead.
* `HSyn.glueOutputs_of_leaves3_hf` reads `t8`, whose type is unchanged.
  * `t8` comes from `poincareComplement : AVB1.PoincareComplement`, and that statement is already
    `∀ k [Field k] [CharZero k]` (Contrib/AVB1/Poincare.lean:42).
  * `poincareComplement_of_open` applies `PicZeroAbVar` and `PhiAmpleIsogeny` only at that `k`
    (`exists_psi`, PoincareComplement.lean:210-258).
  * Characteristic 0.
* Inside the proofs:
  * `mumfordKLFiniteSectionAC_of_open` applies `PicZeroAbVar` at the algebraically closed field it is about.
  * `phiAmpleIsogeny_of_printed` applies its hypothesis at `AlgebraicClosure K`.
  * Both fields have characteristic 0 whenever `K` does.

The brief named three consumers (phi-ample, `t09SymmIsogenyExists`, poincare-proof). They are the three readers of the
field itself. Their only terminal uses are the ones listed above.

## 3. Step (2): the characteristic-0 proof and the reroute

### `ZInQKernel/Contrib/OneProof/PicZeroAbVarCharZero.lean`

Assembled by `scratch/piczero-char0/gen/build_char0.py`. It compiles with no errors or warnings in about 30 s.

* **Copied from pic-smooth.** §1 is pic-smooth's `PicZeroSmoothCartier.lean`, lines 35-142 (wip/pic-smooth), with
  only the namespace changed to `PicZeroChar0`. It contains `PicZeroAbVarAt`, `picZeroAbVarAt_of`,
  `picZeroAbVarAt_charZero_of_cartier`, and so on. `PicZeroSmoothPosChar` is not copied.
* **Characteristic-0 statements.** Each is the original statement with `[CharZero K]` added: `PicZeroAbVar0`,
  `MumfordKLFiniteSectionAC0`, `MumfordKLFiniteAC0`, `MumfordKLFinite0`, `PhiAmpleIsogeny0`,
  `T09_SymmIsogenyExists0`. The lemmas `*_of` show that each is a consequence of the original.
* **Main result.**
  `picZeroAbVar0_of_leaves (h1 : PicLocFinType) (h2 : IdentityComponentLFT) (h3 : KleimanPicZeroProper) : PicZeroAbVar0`.
* **The readers in characteristic 0:**
  * `mumfordKLFiniteSectionAC0_of_open`;
  * `phiAmpleIsogeny0_of_printed (hKL : MumfordKLFiniteSectionAC0) (h8 : MumfordPhiSurjectiveAC)`;
  * `t09SymmIsogenyExists0_of_four`;
  * `Poincare.poincareComplement_of_open0`.

  Their proof bodies are copied verbatim from phi-ample, pic-fix, pic-dict, TailZ24 and poincare-proof. Each
  `intro` pattern gained one `_` for the instance. `AlgebraicClosure K` gets characteristic 0 from Mathlib's
  instance.

### `ZInQKernel/Contrib/OneProof/PicZeroAbVarCharZeroReroute.lean`

Generated by `scratch/piczero-char0/gen/gen.py`, on the model of homfree-noemb's T6 reroute. It is 101 declarations
copied verbatim, renamed `X ↦ X_pz` (structures `XPZ`):

* **Carriers.** The carriers of the five tainted fields: `OpenAddedLeaves4, 6, 7, 8, 9, 12 … 20` and
  `TextbookLeavesHF`, `OpenTextbookLeaves2HF … 4HF`.
* **Typed on them.** Every tainted or carrier-typed declaration on the route: 83 + 16, from `taint2_out.txt`.
* **Field types swapped:**
  * `picZeroAbVar ↦ PicZeroAbVar0`;
  * `mumfordKLFiniteSectionAC ↦ MumfordKLFiniteSectionAC0`;
  * `phiAmpleIsogeny ↦ PhiAmpleIsogeny0`;
  * `t09SymmIsogenyExists ↦ T09_SymmIsogenyExists0`.
* **The four reader maps** call the characteristic-0 proofs instead.
* **The dead field `t9` is dropped**, together with copies of `G12Det`, `g12`, `g8_g12_hf` and `g12Det_of` without
  that antecedent. In the `g12Det_of` copy the only change is `intro _ K` for `intro _ _ K`.
* **`detTate_of_leaves4` and `tatePairingZl_of_leaves4`** are copied with `h9 : T09_SymmIsogenyExists0`. The proofs
  are unchanged: `NumberField K` provides `CharZero K`.

**Compile.**

* **Final run:** `lake env lean` is clean in 9 s. `#print axioms sixContactMin_of_open41_pz` gives
  `[propext, Classical.choice, Quot.sound]`. `lake build +…Reroute +Main +Discharges` succeeds (14167 jobs).
* **First run, fixed.** It hit a heartbeat timeout because homfree's copy library re-emitted the copied
  file-level `open` lines once per block (766 lines). The generator now emits each one once.

**Closure check** (`ClosureCheck.lean`, `closurecheck_out.txt`, VERIFIED):

* **Absent.** The closure of `sixContactMin_of_open41_pz` (241,677 constants) contains none of
  `T09Pic.PicZeroAbVar`, `PicDict.PicZeroSmooth`, `PicFix.MumfordKLFiniteSectionAC`, `T09Pic.PhiAmpleIsogeny`,
  `HDec.WeilPairing.T09_SymmIsogenyExists`, `HDec.LeafPush.T09_WeilPairing`, `G0Galois.G12Det` or `sorryAx`.
* **Present.** It does contain the four characteristic-0 forms.
* **Control.** The closure of the original `sixContactMin_of_open41` contains the old ones.

**`#discharges`** (`Discharges.lean`, `discharges.txt`):

```
#discharges: 43 open hypotheses, 8898 theorems checked, 67 discharge one
```

* No line credits a theorem of this task with discharging `picZeroAbVar`. My theorems prove `PicZeroAbVar0`, not the
  field's statement, and `#discharges` cannot express a reroute (as in homfree-noemb).
* The 18 lines `DISCHARGES [OpenAddedLeaves20.x] by HDec.HSyn.OpenAddedLeavesNPZ.x` are projections of the copied
  bundles. They are spurious: each assumes its bundle.
* The pre-existing lines for `picZeroAbVar` (`PicDict.picZeroAbVar_of_leaves`, `PicFix.picZeroAbVar_of_printed`)
  still assume `PicZeroSmooth`.
* The fold itself is checked by `FoldCheck.lean`.

### The fold (manual; spec in `scratch/piczero-char0/fold-spec.md`)

`FoldCheck.lean` defines the following, compiled with standard axioms:

* `OpenAddedLeaves21`, with 6 fields: `picRepresentableAbVar`, `weilPairingMumford`, `mumfordPhiSurjectiveAC`,
  `picLocFinType`, `identityComponentLFT`, `kleimanPicZeroProper`;
* `openAddedLeaves20PZ_of_OpenAddedLeaves21`, which sets `picZeroAbVar := picZeroAbVar0_of_leaves …`;
* `sixContactMin_of_open42_pz`;
* `frozenTarget_pz`;
* the check map `openAddedLeaves20PZ_of_20`, which shows that `OpenAddedLeaves20PZ` differs from `OpenAddedLeaves20`
  only by the weakened field.

The integrator's TailZ49 is the `HDec.HSyn` part of FoldCheck.lean. Main then switches to `OpenAddedLeaves21` and
`sixContactMin_of_open42_pz`. `kinds-rows.tsv` and `locators-rows.md` give the new rows.

If another fold lands first and changes a carrier, rerun `Taint2.lean`, `FieldTaint.lean` and `gen.py`. The
generator stops with an error if one of its edit targets has changed.

## 4. Step (3): characteristic p

**`PicZeroSmoothPosChar` is not needed and was not proved.** It says that `Pic⁰` of an abelian variety is smooth in
characteristic `p`, which is Mumford §13: `dim T₀ Pic = h¹(𝒪_A) = g`. It remains true, and it remains open as a
statement, but nothing in `frozenTarget` uses it any more. pic-smooth's assessment of what would be needed to prove it
is unchanged:

* one print over an arbitrary field, in fppf identity-component form (BLR 8.4, FGA Explained 9.5, Milne 1986 §10), or
* Lean infrastructure that is not available: tangent spaces of group schemes, and `H¹(A, 𝒪_A)`.

Locators UNVERIFIED.

## 5. New leaves: printed form?

All locators are UNVERIFIED: there is no copy of BLR, Kleiman or SGA 3 on the host. The ratings are those of pic-dict
and pic-fix, unchanged; the statements are their Lean definitions, unchanged.

| leaf | source | printed form? | reason |
|---|---|---|---|
| `picLocFinType` (`PicDict.PicLocFinType`) | BLR, *Néron models*, 8.2 Thm 3 (Murre 1964, Oort 1962); Kleiman 9.4.8 | yes | `Pic_{X/k}` exists and is locally of finite type for `X` proper over a field. The leaf is the statement for every representing object, which follows by Yoneda uniqueness. |
| `identityComponentLFT` (`PicDict.IdentityComponentLFT`) | SGA 3, VI_A 2.4; Stacks 0B7R | yes | For group schemes locally of finite type over a field, `G⁰` is open, a subgroup, and geometrically irreducible. |
| `kleimanPicZeroProper` (`PicFix.KleimanPicZeroProper`) | Kleiman, *The Picard scheme*, Thm 9.5.4 | yes | If `X` is proper and geometrically normal over a field, then `Pic⁰_{X/K}` is proper. The print's existence hypotheses become quantifiers over representing objects. |

* **Flags.** Each is flagged unread: published, counted LEAF, awaiting a statement check.
* **No GLUE.** No new Prop counted GLUE is introduced. The characteristic-0 forms `PicZeroAbVar0` and the others are
  not fields: they are proved, or they are internal to the rerouted chain.
* **Other fields unchanged.** `picRepresentableAbVar`, `weilPairingMumford` and `mumfordPhiSurjectiveAC` keep their
  statements.

## 6. Files

* **Contributions:**
  * `ZInQKernel/Contrib/OneProof/PicZeroAbVarCharZero.lean` (hand-assembled; the final theorem
    `PicZeroChar0.picZeroAbVar0_of_leaves`);
  * `ZInQKernel/Contrib/OneProof/PicZeroAbVarCharZeroReroute.lean` (generated). Neither imports `OneProof.Main`.
* **Analysis**, in `scratch/piczero-char0/`: `Taint.lean`, `FieldTaint.lean`, `Taint2.lean` and their outputs.
* **Generators**, in `scratch/piczero-char0/`: `gen/build_char0.py`, `gen/char0_template.lean`, `gen/gen.py`,
  `gen/copylib.py`, `gen/header.lean`, and pic-smooth's source copy.
* **Checks**, in `scratch/piczero-char0/`: `FoldCheck.lean`, `ClosureCheck.lean`, `Discharges.lean` and their outputs.
* **Fold**, in `scratch/piczero-char0/`: `fold-spec.md`, `kinds-rows.tsv`, `locators-rows.md`.
* **Log:** `scratch/piczero-char0/log.md`.

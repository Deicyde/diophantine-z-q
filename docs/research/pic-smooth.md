# pic-smooth: `PicZeroSmooth` from Cartier's theorem in characteristic 0. The characteristic-p case remains, so no −1

Task pic-smooth. Base: wip/pic-fix be79cb5b. `git merge origin/main` was already up to date (main 2880fef1e is in
the base). I also merged `origin/cloud-b3/w16-h98` (4fa17fc59), the only branch that has
`ZInQKernel/Contrib/OneProof/CartierSmooth.lean` (`cartierSmooth_proof : AVGlue.CartierSmooth`). That merge
adds 68 files and modifies none, so there were no conflicts.

## 1. Verdict

**The −1 target is not reachable as stated.** `PicDict.PicZeroSmooth`, and the bundle field
`picZeroAbVar : T09Pic.PicZeroAbVar` it serves, quantify over **every** field `K`:

```lean
def PicZeroSmooth : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (V : P.left.Opens),
    letI := picardFunctorCommGrpObj A.X.hom rep
    (V : Set P.left) = identityComponent P → Smooth (V.ι ≫ P.hom)
```

Cartier's theorem needs `CharZero K`. In characteristic `p` the statement is still true, but it is a genuine
theorem about abelian varieties, not a consequence of Cartier:

* group schemes such as `μ_p` are locally of finite type and not smooth (STANDARD);
* `Pic⁰` of a general smooth proper variety can be non-reduced (Igusa 1955, STANDARD, locator UNVERIFIED);
* for abelian varieties smoothness is Mumford §13 (`dim Â = h¹(𝒪_A) = g`; locator UNVERIFIED).

**What is proved (VERIFIED: compiled, standard axioms):**

* **Characteristic 0.** `PicZeroSmooth` holds at every field of characteristic 0, from Cartier's theorem and
  `PicLocFinType` alone.
* **`PicZeroAbVar` in characteristic 0 from LEAF leaves only.** At every field of characteristic 0 it follows from
  the three LEAF statements `PicLocFinType`, `IdentityComponentLFT` and `KleimanPicZeroProper`.
* **The full `PicZeroAbVar`.** It follows from those three and one strictly smaller Prop,
  `PicSmooth.PicZeroSmoothPosChar`: `PicZeroSmooth` restricted to fields of characteristic `p > 0`. That Prop is
  GLUE, pending reading.

**Fold counts** (dry runs on this base, re-rated):

| spec | change | net |
|---|---|---|
| `autofold.json`: `picZeroAbVar` alone | `34/11 on 45 -> 37/11 on 48` | 0 |
| `autofold-both.json`: with pic-fix's `phiAmpleIsogeny` | `34/11 on 45 -> 39/10 on 49` | −1, all from `phiAmpleIsogeny`, as in pic-fix |

The one GLUE under `picZeroAbVar` is now only the characteristic-`p` case.

## 2. The Cartier statement and the hypotheses available

`AVGlue.CartierSmooth` (`ZInQKernel/OneProof/H/TailP.lean:305`, VERIFIED read):

```lean
∀ (k : Type) [Field k] [CharZero k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G],
  LocallyOfFiniteType G.hom → Smooth G.hom
```

How each hypothesis is met for a representing object `P` of `Pic_{A/K}`:

| hypothesis | status | supplier |
|---|---|---|
| `GrpObj P` | available | `picardFunctorCommGrpObj A.X.hom rep` gives `CommGrpObj P`; the instance path to `GrpObj` works (it compiled) |
| `LocallyOfFiniteType P.hom` | available | `PicLocFinType` |
| `CharZero K` | **not available** in `PicZeroSmooth` | — |
| universe, base | match | `Type`, `Over (Spec (CommRingCat.of K))` |

`IdentityComponentLFT` is **not** needed for smoothness in characteristic 0: every open subscheme of the smooth
`P` is smooth. It is still used, as before, to make `V` a subgroup and geometrically irreducible.

## 3. Files and theorems

Everything below is VERIFIED: `lake build` succeeds (12880 jobs), and `#print axioms` gives
`[propext, Classical.choice, Quot.sound]` (`scratch/pic-smooth/axioms.txt`). No `sorry`, and neither file imports
`ZInQKernel.OneProof.Main`.

### `ZInQKernel/Contrib/OneProof/PicZeroSmoothCartier.lean`

Namespace `PicSmooth`. It imports only `ZInQKernel.Contrib.OneProof.PicZeroAbVar` (pic-fix), so it builds without
the h98 files; `AVGlue.CartierSmooth` comes from `TailP` through the chain. Cartier's theorem is a hypothesis here.

* `PicZeroSmoothAt K`, `PicZeroProperAt K`, `PicZeroAbVarAt K`: the three statements at one field.
  `picZeroSmooth_iff` and `picZeroAbVar_iff` are `Iff.rfl`.
* `picZeroAbVarAt_of (h1 : PicLocFinType) (h2 : IdentityComponentLFT) (K) (h3a : PicZeroSmoothAt K) (h3b : PicZeroProperAt K) : PicZeroAbVarAt K`.
  This is pic-dict's proof of `picZeroAbVar_of_leaves` verbatim, with `K` fixed.
* `picard_smooth_of_cartier (hC) (h1) (K) [CharZero K] A P rep : Smooth P.hom`.
* `picZeroSmoothAt_charZero (hC) (h1) (K) [CharZero K] : PicZeroSmoothAt K`.
* `picZeroAbVarAt_charZero_of_cartier (hC) (h1) (h2) (h3b : KleimanPicZeroProper) (K) [CharZero K] : PicZeroAbVarAt K`.
* `def PicZeroSmoothPosChar : Prop := ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p], PicZeroSmoothAt K`.
* `picZeroSmooth_of_cartier (hC) (h1) (hp : PicZeroSmoothPosChar) : PicZeroSmooth`. It splits on `ringChar K`,
  which is prime or 0.
* `picZeroAbVar_of_cartier (h1) (h2) (hC) (hp) (h3b) : PicZeroAbVar`.

### `ZInQKernel/Contrib/OneProof/PicZeroAbVarCartier.lean`

It imports the file above and `ZInQKernel.Contrib.OneProof.CartierSmooth`.

```lean
theorem PicSmooth.picZeroAbVar_of_printed2 (h1 : PicLocFinType) (h2 : IdentityComponentLFT)
    (hp : PicZeroSmoothPosChar) (h3b : KleimanPicZeroProper) : PicZeroAbVar
theorem PicSmooth.picZeroAbVarAt_charZero (h1 : PicLocFinType) (h2 : IdentityComponentLFT)
    (h3b : KleimanPicZeroProper) (K : Type) [Field K] [CharZero K] : PicZeroAbVarAt K
```

### `#discharges`

The scratch file is `scratch/pic-smooth/Discharges.lean`; the full output is in `scratch/pic-smooth/discharges.txt`.

```
DISCHARGES [OpenAddedLeaves17.picZeroAbVar] by PicSmooth.picZeroAbVar_of_cartier
  still assumes: [PicDict.PicLocFinType, PicDict.IdentityComponentLFT, AVGlue.CartierSmooth,
 PicSmooth.PicZeroSmoothPosChar, PicFix.KleimanPicZeroProper]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenAddedLeaves17.picZeroAbVar] by PicSmooth.picZeroAbVar_of_printed2
  still assumes: [PicDict.PicLocFinType, PicDict.IdentityComponentLFT, PicSmooth.PicZeroSmoothPosChar,
 PicFix.KleimanPicZeroProper]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenTextbookLeaves12.cartierSmooth] by ZInQ.Contrib.OneProof.CartierSmooth.cartierSmooth_proof
#discharges: 56 open hypotheses, 3085 theorems checked, 21 discharge one
```

### Autofold

All three dry runs below compile against `TailZ42` to `HDec.HSyn.sixContactMin_of_open36`, with the standard
axioms.

* `scratch/pic-smooth/autofold.json` (**recommended once `CartierSmooth.lean` is on main**).
  * Discharged field: `picZeroAbVar`.
  * Proof: `PicSmooth.picZeroAbVar_of_printed2`.
  * Leaves: `picLocFinType`, `identityComponentLFT`, `kleimanPicZeroProper` (flagged unread, count LEAF) and
    `picZeroSmoothPosChar` (flag "pending reading: …", counts GLUE).
  * Dry run: `34/11 on 45 -> 37/11 on 48`.
* `scratch/pic-smooth/autofold-both.json`: the same, plus pic-fix's `phiAmpleIsogeny` discharge.
  * Dry run: `34/11 on 45 -> 39/10 on 49`.
* `scratch/pic-smooth/autofold-cartierleaf.json`: for a main without `CartierSmooth.lean`.
  * Imports only `PicZeroSmoothCartier`.
  * Cartier's statement is repeated as an added-bundle leaf `cartierSmoothPic : AVGlue.CartierSmooth`, flagged
    unread. Autofold's `{n}` cannot reach the textbook field `cartierSmooth`.
  * Dry run: `34/11 on 45 -> 38/11 on 49`.

## 4. Leaves: printed form?

All locators are UNVERIFIED (no copies of the sources on the host).

| leaf | source | printed form? | reason |
|---|---|---|---|
| `picLocFinType` | BLR 8.2 Thm 3 / Murre–Oort; Kleiman 9.4.8 | yes (unchanged from pic-fix) | — |
| `identityComponentLFT` | SGA 3 VI_A 2.4; Stacks 0B7R | yes (unchanged) | — |
| `kleimanPicZeroProper` | Kleiman, *The Picard scheme*, 9.5.4 | yes (unchanged from pic-fix) | — |
| `AVGlue.CartierSmooth` | Cartier 1962; Oort 1966; Mumford §11; Milne 2017 Thm 3.23 | yes (textbook LEAF field of the chain) | proved by `cartierSmooth_proof` on cloud-b3/w16-h98; `cartierSmoothPic` in the fallback spec is the same statement |
| `picZeroSmoothPosChar` (new) | Mumford §13 over `k̄`; BLR 8.4 / FGA Explained 9.5 / Milne 1986 §10 to read | **no, pending reading** | Mumford §13 is over `k̄` and about Mumford's dual. Identifying it with the identity component of the fppf `Pic_{A/K}` and descending to `K` are theorem steps (the 11-16 dictionary ruling). The restriction to characteristic `p` is a consequence of `PicZeroSmooth`, not stronger. |

## 5. What remains, and how to get the −1

1. **A print in characteristic `p`.** One print, over an arbitrary field, of "`Pic⁰_{A/K}` is smooth (an abelian
   variety)" for the fppf Picard scheme clears `picZeroSmoothPosChar`. Candidates: BLR 8.4, FGA Explained 9.5,
   Milne 1986 §10. Then `autofold.json` gives −1 for `picZeroAbVar`, and `autofold-both.json` −2.
2. **Or restrict the consumers to characteristic 0.** `picZeroAbVar` is read only by
   `T09Pic.t09SymmIsogenyExists_of_four` (TailZ24.lean:807). Its target `WeilPairing.T09_SymmIsogenyExists` is ∀
   fields; it feeds:
   * `detTate_of_leaves4` (target `G0Galois.DetTate`, over `NumberField K` only);
   * `t9_of_leaves5` (`LeafPush.T09_WeilPairing`, ∀ fields, which reaches `G12Det`, a statement over number fields
     that takes T9 as an antecedent).

   So a consumer-restricted refactor may need only characteristic 0. That refactor would thread a char-0 variant
   through pinned modules (maintainer work; see the weaker-leaf-bypass recipe), and it is not done here. Not
   verified that every use is in characteristic 0. After it, `picZeroAbVarAt_charZero` discharges the restricted
   field from LEAF leaves only.
3. `CartierSmooth.lean` (68 files from cloud-b3/w16-h98) must land on main before `autofold.json` can fold. Until
   then, `autofold-cartierleaf.json` works on the current main.

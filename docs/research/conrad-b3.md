# conrad-b3: Tate 1967 off the C8 route; one Conrad App. B leaf (p. 32 + Prop. B.3)

Task conrad-b3, 2026-11-17. Base: `origin/wip/c8-conrad3` `7289ef659`; `origin/wip/ht-merge` `027f637cd` merged for the
joint-fold count and dry run (merge commit `0558eeb57`). Results log: `scratch/conrad-b3/log.md`. This is model work;
nobody has reviewed it.

**VERIFIED** means compiled, computed, or read in a named file on this host. **STANDARD** means published, with the
reference given. **SPECULATIVE** means not checked. Theorem numbers from memory are marked UNVERIFIED (no network).
Conrad App. B is known on this host only through the page read of 11-17 forwarded in the task text (pp. 32-34 quoted
there); I did not read the preprint myself.

## 0. Main result

1. **`LocAlgExponentEqWeight` is proved from Conrad's Prop. B.3** (VERIFIED, compiled; §3):
   `HDec.G0Galois.C8Conrad.locAlgExponentEqWeight_of_conradPropB3 : ConradPropB3Qp → LocAlgExponentEqWeight`
   (`ZInQKernel/Contrib/OneProof/C8ConradB.lean`). The leaf `ConradPropB3Qp` is Prop. B.3 for the base field `L = ℚ_p`,
   stated in Conrad's own conventions (arithmetic Artin map; `χ_cyc` of weight `+1`). The exponent-sign and weight-sign
   translations are definitional and proved (`isLocallyAlgebraic_iff_conrad`, `htMult_eq_conradHTMult_neg`, the latter
   `rfl`).
2. **One Conrad leaf** (§4): `ConradAppB := ConradAppBQp ∧ ConradPropB3Qp`, App. B pp. 32-33 for `L = ℚ_p`, exactly
   the manuscript's citation (L760-762). Every consumer takes the merged statement.
3. **`TateTwistInvariantsInertia` is off the route** (§2, §5). Its only consumers were the C8 derivation and the C8
   input structures. `C8Inputs` (C8Poincare) and `C8Leaves` (C8Printed) now carry `conradAppB` instead of
   `conradAppBQp` and `tateTwistInvariantsInertia`. The definition and `locAlgExponentEqWeight_of_tateInertia` stay in
   `C8LocAlg.lean`, unused by the fold.
4. **Count** (VERIFIED, `scratch/conrad-b3/count.py`, output `count_out.txt`; same rule as autofold and ht-merge's
   `count.py`):

   **H strict LEAF/GLUE: 5/24 on 29 before (main `5f1fac790`), 5/24 on 29 after** (joint fold of C8 + Poincaré +
   ht-merge's consumer-(iii) swap, with PR #86's `poincareComplement_proof` filling Poincaré).

   Without conrad-b3 the same joint fold is 5/25 on 30. So the joint-fold GLUE is **one lower** (the target), and the
   joint fold becomes count-neutral against main. Without PR #86: 5/25 on 30 (conrad-b3) against 5/26 on 31 (ht-merge's
   spec).
5. **Manuscript check** (§6): L763-764, "removing its integral local Hodge–Tate weight", is supported by the cited
   source: Prop. B.3 says the Hodge–Tate weight of a locally algebraic character is its exponent. No known issue (§8).

## 1. What compiles (summary; details §9)

`lake build ZInQKernel.Contrib.OneProof.C8Printed` succeeds on the merged tree (13414 jobs), the joint dry run
`scratch/conrad-b3/CBDryRun.lean` compiles with standard axioms for its tops, and `#discharges` runs (30 open
hypotheses, 16 discharge one, none from the C8 files, as expected for a copy reroute).

## 2. Part (1): consumers of `TateTwistInvariantsInertia` (VERIFIED by grep)

Grep over every `.lean`, `.json`, `.py`, `.tsv` file of the worktree (`.lake` excluded), and `git grep` over
`origin/main` and `origin/wip/ht-merge`:

| place | what |
|---|---|
| `C8LocAlg.lean` L90 | the definition |
| `C8LocAlg.lean` L98 | `locAlgExponentEqWeight_of_tateInertia` |
| `C8CFT.lean` L506 | `c8TwistFinite_of_leaves (… hC hTT …)`, which uses `hTT` only through L98 (L515) |
| `C8Poincare.lean` L35, L43 | field of `C8Inputs`; `g12DetPZ_of_inputs` passes it to `c8TwistFinite_of_leaves` |
| `C8Printed.lean` L28, L33, L41, L47 | field of `C8Leaves`; `c8Inputs_of_leaves`, `c8TwistFinite_of_printed`, `g12DetPZ_of_printed` |

There is no other Lean consumer. `origin/main` has none (the C8 files are not on main). `origin/wip/ht-merge` has the
same five C8 files (identical to the base) and scratch copies only: `scratch/c8-conrad2/`, `scratch/c8-conrad3/`,
`scratch/ht-abvar/HTDryRun.lean`, `scratch/ht-merge/HTMergeDryRun.lean` (they read `C8Leaves` / `OpenAddedLeaves28HM`).
So the task's list is complete; `C8CFT.lean` L506 is a theorem with the leaf as a hypothesis, not a structure.

## 3. Part (2): Conrad Prop. B.3 for `L = ℚ_p` and `LocAlgExponentEqWeight`

### 3.1 Conrad's conventions and the project's (sign chain)

| | Conrad (page read 11-17) | project (Lean) |
|---|---|---|
| Artin map | arithmetic normalization (p. 32) | Tau Ceti's `artinMap` through `IsArtinLift`: uniformizers go to arithmetic Frobenius (`TauCeti.ClassFieldTheory.isArithFrobeniusLift_of_mk_eq_artinMap_uniformizer`, `Local/Unramified.lean` L465), and `χ_cyc(Art u) = u⁻¹` for `u ∈ ℤ_p^×` (`localCyclotomicCharacter_artinMap_padic`, `ExplicitCyclotomicSymbol/ArtinMap.lean` L295; `cyc_of_isArtinLift`) — VERIFIED, read; the same normalization |
| locally algebraic, exponent | near 1, `ψ ∘ r_L = x ↦ ∏_τ τ(x)^{-n_τ}` (p. 33); for `L = ℚ_p` one `τ`: `x^{-n_C}` | `IsLocallyAlgebraic p ψ n_L`: `ψ(Art u) = u^{n_L}` on `1 + p^kℤ_p` |
| Hodge–Tate weight | `ℂ_L ⊗ V = ⊕ V_σ`, `V_σ = ℂ_L(w_σ)` (p. 33): `χ_cyc` has weight `+1` | `htMult w = dim_{ℚ_p} H_{−w} / [E:ℚ_p]`, `H_i = Hom_{G}(V, ℂ_p(i))`: `χ_cyc` has weight `−1` |
| Prop. B.3 | `w_σ = n_i` (p. 33, proof pp. 33-34) | — |

Check of the Conrad convention in the project's terms: `H_i(ℚ_p(1)) ≠ 0` iff `i = 1` (the docstring of `htMult`, by
Tate's theorem), so `χ_cyc` has Conrad weight `+1` when the Conrad weight `w` is read off `H_w`. And `χ_cyc ∘ r = x^{-1}`
(arithmetic normalization), so `n_C(χ_cyc) = 1 = w_C(χ_cyc)`, as Prop. B.3 predicts.

Chain: `n_L = −n_C` (exponent sign), `w_C = n_C` (Prop. B.3), `w_L = −w_C` (weight sign); hence `n_L = w_L`, which is
`LocAlgExponentEqWeight`.

### 3.2 Lean statements (`C8ConradB.lean`)

```lean
def IsLocallyAlgebraicConrad {E : Type*} [Field E] [Algebra ℚ_[p] E] (ψ : PkgI4.GQp p →* Eˣ) (n : ℤ) : Prop :=
  ∃ k : ℕ, ∀ u : ℤ_[p]ˣ, PadicInt.toZModPow k (u : ℤ_[p]) = 1 → ∀ σ : PkgI4.GQp p,
    IsArtinLift p σ (unitsQp p u) → ((ψ σ : Eˣ) : E) = (algebraMap ℚ_[p] E ((u : ℤ_[p]) : ℚ_[p])) ^ (-n)

def conradHTMult … (ρ : PkgI4.GQp p →* GL (Fin m) E) (w : ℤ) : ℕ :=
  finrank ℚ_[p] (PkgI4.htSpace p ρ w)

def ConradPropB3Qp : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E]
    (ψ : PkgI4.GQp p →* Eˣ) (n : ℤ), Continuous (fun σ => (((ψ σ : Eˣ) : E) : PadicAlgCl p)) →
    IsLocallyAlgebraicConrad p ψ n → conradHTMult p (charRep ψ) n = finrank ℚ_[p] E

def ConradAppB : Prop := ConradAppBQp ∧ ConradPropB3Qp
```

All objects are the project's existing ones (`IsArtinLift`, `unitsQp`, `charRep`, `PkgI4.htSpace`, Tau Ceti's Artin map);
nothing was invented for the purpose. `conradHTMult` is only a name for `finrank ℚ_[p] (htSpace p ρ w)`.

### 3.3 Proof of `LocAlgExponentEqWeight` (VERIFIED, compiled)

Given `HasHTWeights p (charRep ψ) {w}` and `IsLocallyAlgebraic p ψ n`:
1. `isLocallyAlgebraic_iff_conrad` gives `IsLocallyAlgebraicConrad p ψ (−n)` (unfold, `neg_neg`).
2. Prop. B.3 gives `conradHTMult p (charRep ψ) (−n) = [E:ℚ_p]`.
3. `htMult_eq_conradHTMult_neg` (`rfl`): `htMult n = conradHTMult (−n) / [E:ℚ_p] = 1` (`Nat.div_self`, `[E:ℚ_p] > 0`).
4. `HasHTWeights {w}` says `htMult n = count n {w}`, which is `0` unless `n = w`. Hence `n = w`.

No Tate theorem is used in the Lean proof; the single-weight multiplicity step is step 4.

### 3.4 Rating of the new leaf `ConradPropB3Qp`: consequence, not verbatim printed form

* The hypothesis is the print's for `L = ℚ_p` (one embedding, one exponent). "Near 1" is read on the open subgroups
  `1 + p^kℤ_p`, a basis of neighbourhoods of `1` in `ℚ_p^×` — equivalent.
* The conclusion `dim_{ℚ_p} H_n = [E:ℚ_p]` is the print's "`w_σ = n` for every `σ`" read through the definition of
  Hodge–Tate multiplicities by invariants: if `ℂ_p ⊗_{ℚ_p} V ≅ ⊕_σ ℂ_p(w_σ)` with every `w_σ = n` (`[E:ℚ_p]` lines),
  then `H_n = Hom_G(V, ℂ_p(n)) = Hom_{ℂ_p,G}(ℂ_p ⊗ V, ℂ_p(n)) ≅ (ℂ_p^{G_{ℚ_p}})^{[E:ℚ_p]} = ℚ_p^{[E:ℚ_p]}`. The last step is
  Ax–Sen–Tate over `ℚ_p`, which is proved in the tree (`ZInQ.Contrib.CloudB3W11.axSenTate_proof`); the rest is linear
  algebra. This bridge is not formalized, so the leaf is a **consequence** of the print (never stronger), not verbatim
  printed form.
* Flag: CITED (L760-762, Conrad App. B p. 33 Prop. B.3); AI page read 11-17; unrefereed preprint, the manuscript's own
  citation.

## 4. Part (3): merge into one leaf `ConradAppB` — merged

`ConradAppBQp` (C8Conrad.lean L78, p. 32) and `ConradPropB3Qp` (p. 33) are both from App. B pp. 32-33, which the
manuscript cites as one citation (L761). Consumers of either, all of which take the merged statement:

| consumer | uses |
|---|---|
| `C8ConradB.c8TwistFinite_of_conradB` | `hC.1` (p. 32) and `hC.2` (via `locAlgExponentEqWeight_of_conradAppB`) |
| `C8ConradB.locAlgExponentEqWeight_of_conradAppB` | `hC.2` |
| `C8Poincare.C8Inputs` (field `conradAppB`), `g12DetPZ_of_inputs` | through `c8TwistFinite_of_conradB` |
| `C8Printed.C8Leaves` (field `conradAppB`), `c8Inputs_of_leaves`, `c8TwistFinite_of_printed`, `g12DetPZ_of_printed` | the same |
| the fold top (`scratch/conrad-b3/CBDryRun.lean`: `OpenAddedLeaves27CB.conradAppB`) | through `c8Inputs_of_leaves` |

`C8CFT.c8TwistFinite_of_leaves` still takes `ConradAppBQp` and `TateTwistInvariantsInertia`; it is c8-conrad2's route,
kept in the tree and no longer on the fold route. The merged leaf's rating is bounded by the weaker part: the p. 32 part
was rated GLUE/GLUE by the strict leaf review (queue28, consequence with two unproved bridges), and it keeps that flag in
the merged row.

## 5. Part (4): structures, fold spec, dry run, count

**Consumer statements changed** (named, as the rules require): `C8Inputs` (C8Poincare: fields `conradAppBQp`,
`tateTwistInvariantsInertia` replaced by `conradAppB : ConradAppB`), `C8Leaves` (C8Printed: same), and the signatures of
`c8TwistFinite_of_printed` and `g12DetPZ_of_printed` (`hC : ConradAppB` instead of `hC : ConradAppBQp`,
`hTT : TateTwistInvariantsInertia`). Why: the task asks to remove Tate 1967 from the C8 input structures; these
structures exist only on the C8 branches (not on main) and their only readers are the dry runs, whose copied body takes
`c8 : C8Inputs` and reads it only through `g12DetPZ_of_inputs`, whose signature is unchanged. No statement of the chain
or of main is changed.

**Spec** `scratch/conrad-b3/autofold.json`: c8-conrad3's hand-fold spec with the new leaf row `conradAppB` (kind
`consequence`, class CITED, flag "pending review …; AI page read 11-17; unrefereed preprint, the manuscript's own
citation …") in place of `conradAppBQp` and `tateTwistInvariantsInertia`; `proved_glue` gains
`locAlgExponentEqWeight_of_conradPropB3`. `"discharges": []` as before: no bundle field of `frozenTarget` is discharged
(the reroute is a copy reroute, to be folded jointly with consumer (iii)).

**Dry run** `scratch/conrad-b3/CBDryRun.lean`: ht-merge's joint dry run (`scratch/ht-merge/HTMergeDryRun.lean`)
verbatim, with the top's added bundle `OpenAddedLeaves27CB = {conradAppB, scholzeH1AbVar, t10TateDuality}` in place of
`OpenAddedLeaves28HM = {conradAppBQp, tateTwistInvariantsInertia, scholzeH1AbVar, t10TateDuality}`, new tops
`sixContactMin_of_open73CB` and `ZInQ.OneProof.frozenTarget_cb`. Outcome in §9.

**Count** (`count_out.txt`, both against main `5f1fac790`'s kinds.tsv and the merged tree's; identical):

| H rows (strict LEAF/GLUE on N) | without PR #86 | with PR #86 |
|---|---|---|
| main (before) | 5/24 on 29 | 5/24 on 29 |
| joint fold, ht-merge's spec (c8-conrad3's two C8 leaves) | 5/26 on 31 | 5/25 on 30 |
| **joint fold, conrad-b3 (one Conrad leaf)** | **5/25 on 30** | **5/24 on 29** |

Rows removed at the joint fold: `picRepresentableAbVar`, `kleimanPicZeroProper954SiteQ`, `hodgeTateDecompOr`. Rows added
(all GLUE at entry): `conradAppB`, `scholzeH1AbVar`, `t10TateDuality`, and `poincareComplement` unless PR #86 fills it.

**PR #86** (branch `proof/poincare-complement-native-20261117` at `8050603bc`; read with `git show`, not merged, not
compiled): `ZInQKernel/Contrib/CloudR2Poincare/FinalUnconditional.lean` L24
`theorem poincareComplement_proof : ZInQ.Contrib.AVB1.PoincareComplement`; `AVB1/Poincare.lean` is identical to this
tree's (empty diff). So it fills `OpenTextbookLeaves19HM.poincareComplement` as is, and the count can be stated without
merging it.

## 6. Manuscript check (L763-764)

L760-764 (paraphrase): local algebraicity [Conrad App. B pp. 32-33] and class field theory over `ℚ` make the twisting
character a finite character times an integral power of the cyclotomic character; "removing its integral local
Hodge–Tate weight" leaves finite inertia. The step needs: the exponent of the locally algebraic character equals its
Hodge–Tate weight (so that the weight comparison of L765-767 fixes the power). That is Prop. B.3 (p. 33, as read
11-17), within the cited page range. **Confirmed: L763-764 is now supported by the cited source**, and the route
follows the manuscript's citation instead of Tate 1967. The manuscript's convention is Tate's (`χ_cyc` of weight `−1`,
L755), Conrad's is the opposite; the translation is definitional (§3.1) and is not an issue.

## 7. On-the-spot steps

None new. The two translations are definitional (proved). The bridge from the print's decomposition to the
dimension statement (§3.4) is a dictionary step using Ax–Sen–Tate, proved in the tree.

## 8. Known issues

* **None found in the manuscript's use of Conrad App. B at C8.** The p. 32 normalization agrees with Tau Ceti's
  (arithmetic); Prop. B.3 covers the weight step for the base field `ℚ_p` that C8 uses (`ℓ = 5`).
* Inherited, not new: the source is an unrefereed author preprint (the manuscript's own citation); the p. 32 part keeps
  its queue28 flag (two unproved bridges, GLUE/GLUE).
* The page read is an AI read forwarded in the task text; I did not see the preprint.

## 9. What compiles (VERIFIED, 11-17, Lean 4.35.0, Mathlib v4.35.0, merged tree `0558eeb57` + conrad-b3)

| check | outcome |
|---|---|
| `lake env lean ZInQKernel/Contrib/OneProof/C8ConradB.lean` | no errors, no warnings |
| `lake build ZInQKernel.Contrib.OneProof.C8Printed` | Build completed successfully (13414 jobs): C8ConradB, C8Poincare, C8Printed built |
| `lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges ZInQKernel.Contrib.OneProof.ScholzeH1AbVar` | Build completed successfully (15983 jobs) |
| `scratch/conrad-b3/Discharges.lean` (output `discharges_out.txt`) | `#discharges: 30 open hypotheses, 11466 theorems checked, 16 discharge one`; none from the C8 files (no bundle field is discharged by this reroute); `#print axioms` `[propext, Classical.choice, Quot.sound]` for `isLocallyAlgebraic_iff_conrad`, `htMult_eq_conradHTMult_neg`, `locAlgExponentEqWeight_of_conradPropB3`, `locAlgExponentEqWeight_of_conradAppB`, `c8TwistFinite_of_conradB`, `g12DetPZ_of_inputs`, `c8Inputs_of_leaves`, `c8TwistFinite_of_printed`, `g12DetPZ_of_printed` |
| `scratch/conrad-b3/CBDryRun.lean` (output `dryrun_out.txt`) | no errors; `ZInQ.OneProof.frozenTarget_cb`, `HDec.HSyn.sixContactMin_of_open73CB`, `sixContactMin_of_open72_hm` and the C8 theorems: `[propext, Classical.choice, Quot.sound]`; `TateTwistInvariantsInertia` is not a hypothesis of any top (the source names it only in comments) |
| `scratch/conrad-b3/count.py` (output `count_out.txt`) | §5 table |

One compile fix: `Module.finrank_pos` for `↥E` (an `IntermediateField`) timed out on `IsTorsionFree ℚ_[p] ↥E`;
`finrank_pos_intermediateField` uses `finrank_pos_iff_of_free` with `Module.Free.of_divisionRing` instead.

Build note: the merged tree's `.lake/build` was reflink-copied from `~/dzq-wt/ht-merge` (same ZInQKernel sources as
`origin/wip/ht-merge`); the base build is kept as `.lake/build-old-base` (not deleted; no `rm -rf`).

## 10. Files

* New: `ZInQKernel/Contrib/OneProof/C8ConradB.lean` (`IsLocallyAlgebraicConrad`, `conradHTMult`,
  `isLocallyAlgebraic_iff_conrad`, `htMult_eq_conradHTMult_neg`, `finrank_pos_intermediateField`, leaf
  `ConradPropB3Qp`, merged leaf `ConradAppB`, `locAlgExponentEqWeight_of_conradPropB3`,
  `locAlgExponentEqWeight_of_conradAppB`, `c8TwistFinite_of_conradB`).
* Changed (named in §5): `ZInQKernel/Contrib/OneProof/C8Poincare.lean` (`C8Inputs`, `g12DetPZ_of_inputs`'s proof),
  `ZInQKernel/Contrib/OneProof/C8Printed.lean` (`C8Leaves`, `c8Inputs_of_leaves`, `c8TwistFinite_of_printed`,
  `g12DetPZ_of_printed`).
* `scratch/conrad-b3/`: `log.md`, `autofold.json`, `count.py`, `count_out.txt`, `kinds_origin_main_5f1fac790.tsv`,
  `CBDryRun.lean` + `dryrun_out.txt`, `Discharges.lean` + `discharges_out.txt`.

## 11. What remains

* Review of the new merged row `conradAppB` (a human read of Conrad p. 33 Prop. B.3 would clear the AI-read flag of
  that half; the p. 32 half keeps queue28's two bridges).
* The fold itself (integrator): jointly with ht-merge's consumer-(iii) swap and PR #86, re-based onto main's current top
  (main moved from `sixContactMin_of_open72` to `open76` through count-neutral folds since ht-merge's base).
* Optional cleanup after the fold: `C8LocAlg.TateTwistInvariantsInertia`, `locAlgExponentEqWeight_of_tateInertia` and
  `C8CFT.c8TwistFinite_of_leaves` are off the route and could be deleted.

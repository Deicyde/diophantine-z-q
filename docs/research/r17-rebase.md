# r17-rebase: Carayol's printed leaf for `r17`, rebased on main (leaf-fold33) as a fold candidate

Task r17-rebase, branch `wip/r17-rebase`. It starts from origin/wip/r17-print 785e3f29 with origin/main c0f3d085
merged (leaf-fold33; top `sixContactMin_of_open48` in `TailZ55`), merge commit 09ec5c5b. 2026-11-17.
Marks: **VERIFIED** (compiled, or read in the named file), **STANDARD** (published, reference given),
**SPECULATIVE**. Theorem numbers from memory are **UNVERIFIED** (no network).

## 0. Result

**On current main, `r17 : LadicCond.CarayolR17'` is replaced by one printed leaf, `CarayolPrinted.CarayolThmAIrr`, and the
fold compiles.** On main's `kinds.tsv` the strict and the strictest counts both go from 11 LEAF / 18 GLUE to
12 / 17, on 29 H fields: **GLUE −1**. This holds with the leaf flagged `unread`, the contributor kit's flag for a new
printed leaf. The reading risk is in the flag (§4): the conductor clause is a theorem step beyond Théorème (A) as
printed. All VERIFIED:

* **Builds on main.** r17-print's `CarayolPrinted.lean` builds on the merged tree with no edits, together with what it
  imports that main lacks (`NewformDict.lean`, `CarayolLevel.lean`).
* **New contribution, `ZInQKernel/Contrib/OneProof/CarayolPrintedIrr.lean`** (no warnings, `lake build` OK). It
  proves the **Burnside step**: Burnside's form of absolute irreducibility follows from Ribet's printed word
  "irreducible" together with oddness. So the leaf is stated in printed form:
  `CarayolThmAIrr → CarayolThmA` (`carayolThmA_of_irr`), and
  `carayolR17'_of_printedIrr : CarayolThmAIrr → DSCoeffExt.EigenformCoeffFieldFinite → LadicCond.CarayolR17'`.
* **`#discharges` against main** (`scratch/r17-rebase/discharges.txt`):
  `DISCHARGES [OpenResearchLeaves31.r17] by CarayolPrinted.carayolR17'_of_printedIrr`, still assuming
  `[CarayolPrinted.CarayolThmAIrr, DSCoeffExt.EigenformCoeffFieldFinite]`, with axioms
  `[propext, Classical.choice, Quot.sound]`. The same holds for r17-print's `carayolR17'_of_printed` and for the
  split form `carayolR17'_of_split` (§4).
* **Fold dry run** of `scratch/r17-rebase/autofold.json`: `strict count: 11/18 on 29 -> 12/17 on 29; strictest
  11/18 -> 12/17`. The generated module compiles, with `sixContactMin_of_open49` on the standard axioms. So does a
  frozenTarget variant: main's `frozenTarget` over `OpenResearchLeaves32` (`r17` dropped, `carayolThmAIrr` added),
  `ZInQ.OneProof.frozenTarget_r17rebase`, with axioms `[propext, Classical.choice, Quot.sound]`.
* **No name clash.** The 243 top-level Contrib modules of main elaborate together with `CarayolPrintedIrr`. Main
  has 244 such modules; the one left out clashes with HDecomp on main already, independently of this task (§2).
* **Scenario F.** The leaf also supersedes modular-split's `CarayolRealization`:
  `carayolRealization_of_printed : CarayolThmA → EigenformCoeffFieldFinite → ModularSplit.R17.CarayolRealization`,
  standard axioms.

## 1. Step 1: building on the merged tree (VERIFIED)

`git merge origin/main` merged with no conflicts. `lake build ZInQKernel.Contrib.OneProof.CarayolPrinted` (10691
jobs) succeeded. No technical breakage, so nothing in r17-print's three files was changed. `DSCoeffExt.lean` is
already on main. The field statement on main is identical to r17-print's copy (`scratch/r17-rebase/R17Statement.lean.txt`,
compared with `diff` against `ZInQKernel/HDecomp/Conductor/LadicCond.lean`).

## 2. Step 2: name clashes (VERIFIED)

* `lake build` of every top-level module under `ZInQKernel/Contrib/` succeeded: 244 modules, i.e. those not imported
  by another Contrib module (`scratch/r17-rebase/tops.py`, list in `contrib-tops.txt`), together with
  `+ZInQKernel.OneProof.Main` and `+ZInQKernel.OneProof.Discharges`. That was 14354 jobs, with no errors.
* `AllContrib.lean` imports all 244 together with the new modules. It fails on a clash that **predates this task**:
  `PkgI6.TraceContainsRamificationIdx` is declared both by `ZInQKernel.Contrib.Different.Local` and by
  `ZInQKernel.HDecomp.Textbook.Different`.
  * The first is only in the closure of the old aggregate module `ZInQKernel.Contrib.AllContrib`.
  * The second is in the closure of every OneProof contribution.

  So that aggregate cannot be imported together with any OneProof contribution on main, this one included.
* Dropping that one module (`clashloop.sh`), `AllContrib2.lean` elaborates: 243 tops plus `CarayolPrintedIrr`.
* For the dropped module: `NewNames.lean` lists the 71 constants declared in the four new modules
  (`CarayolPrintedIrr`, `CarayolPrinted`, `NewformDict`, `CarayolLevel`). `DroppedTopCheck.lean` imports
  `ZInQKernel.Contrib.AllContrib` and finds none of the 71. The positive control,
  `PkgI6.TraceContainsRamificationIdx`, is found.

## 3. Step 3: the fold (VERIFIED)

`scratch/r17-rebase/autofold.json` (field `r17`):

* new leaf `carayolThmAIrr : _root_.CarayolPrinted.CarayolThmAIrr`, kind `published`;
* flag `unread: new printed leaf (packaged form); reading risk: …`, with the full risk text of §4;
* proof `_root_.CarayolPrinted.carayolR17'_of_printedIrr {n}.carayolThmAIrr {n}.eigenformCoeffFieldFinite`.

Dry-run variants, all against main's `kinds.tsv`:

| spec | leaves | strict | strictest | dry-run module |
| --- | --- | --- | --- | --- |
| `autofold.json` (recommended) | `carayolThmAIrr` (published, unread + risk) | 11/18 on 29 → **12/17 on 29** | 11/18 → **12/17** | compiles, standard axioms; frozenTarget variant compiles |
| `autofold-burnside.json` | r17-print's `carayolThmA` (Burnside form) | 11/18 → 12/17 | 11/18 → 12/17 | (same module shape) |
| `autofold-split.json` | `carayolExistence` (published, unread) + `carayolConductor` (composite) | 11/18 on 29 → 12/18 on 30 | 11/18 → 12/18 | compiles, standard axioms |
| `autofold-pending.json` | `carayolThmAIrr` flagged pending reading | 11/18 → 11/18 | 11/18 → 11/18 | (count only) |

`AutofoldDryRun.lean` is the dry-run output with its first line stripped. `FrozenTargetDryRun.lean` adds main's imports
and main's `frozenTarget` with `OpenResearchLeaves32` and `sixContactMin_of_open49`.

## 4. Step 4: rating against the print

The leaf (`CarayolPrintedIrr.lean`, unchanged objects from r17-print) is defined as follows. For a Tau Ceti
`Newform N 2` with `K_f` a number field and `λ ∣ ℓ` a place of `K_f`, there is a continuous
`ρ : G_ℚ →* GL₂(K_{f,λ})` (Mathlib's `adicCompletion`) with five properties:

* **irreducible:** every `ρ(G_ℚ)`-stable `K_{f,λ}`-subspace of `K_{f,λ}²` is `⊥` or `⊤`;
* **odd:** `∃ c, c * c = 1 ∧ det ρ(c) = -1`;
* **unramified** at `p ∤ Nℓ`;
* **trace:** the arithmetic Frobenius has trace `a_p(f)`;
* **conductor:** `condExp (ρ ∘ decomp p) = v_p(N)` for every prime `p ≠ ℓ`.

| clause | printed? | how handled |
| --- | --- | --- |
| existence, continuity, unramified, trace `a_p` | yes: Shimura 1971 Thm 7.14 (weight 2), Deligne 1971; Carayol (A) at unramified `p` (UNVERIFIED numbers) | leaf |
| irreducible over `K_{f,λ}` | yes: Ribet, LNM 601 (1977) Thm 2.3 (UNVERIFIED number), in its plain form (no stable subspace) | leaf |
| odd | yes, as a consequence of the print: `det ρ_{f,λ} = ψ·χ_ℓ` (Deligne; DDT 1997 Thm 3.1, UNVERIFIED). In weight 2, `ψ(−1) = 1` and `χ_ℓ(c) = −1` for complex conjugation `c` | leaf |
| **Burnside form** (the image spans `M₂(K_{f,λ})`), r17-print's clause | **no: a theorem step beyond the print** (absolutely irreducible ⇔ Burnside is Burnside's theorem; Ribet prints "irreducible") | **proved in Lean** from irreducible + odd: `adjoin_eq_top_of_irreducible_odd` (§5) |
| **conductor `v_p(N)` at `p ≠ ℓ`** | **not in Théorème (A) as printed.** (A) is local–global compatibility of `ρ_{f,λ}|G_{ℚ_p}` with `π_{f,p}`. The equality needs Casselman, Math. Ann. 201 (1973) (`a(π_p) = v_p(N)` for newforms), the conductor compatibility of the local correspondence, and the Weil–Deligne / Serre–Tate dictionary. The locator audit read Carayol and rates the equality a CONSEQUENCE of these (VERIFIED: `docs/research/locators.md` row R17, the column "combine the local correspondence with newform conductor `a(pi_p)=v_p(N)`"). A packaged print ("`ρ_{f,λ}` has conductor `N` away from `ℓ`") is quoted from DDT 1997 Thm 3.1 or Carayol §0.8: UNVERIFIED, nobody has read either | **not provable in Lean today.** `π_p`, the local Langlands correspondence and Casselman's newform theory of `GL₂(ℚ_p)` are not definable in Mathlib v4.35. **Split off** as `CarayolConductor` with its own citation (§4.1). The leaf keeps the packaged clause, and the flag records the risk |

**Verdict on the leaf.** `CarayolThmAIrr` is the published statement in its packaged form, and a consequence of the
prints, never stronger. Four of its five clauses are printed. The fifth, the conductor clause, is printed only if the
packaging in DDT 1997 Thm 3.1 or Carayol §0.8 is (UNVERIFIED). The audit's reading of Carayol's primary text
classifies that clause as Carayol (A) with Casselman 1973. The flag is therefore `unread` with the risk stated, as the
task specifies and as the kit prescribes for a new printed leaf. This gives **GLUE −1**. The −1 is conditional on a
statement check confirming the packaging. If the check finds it unprinted, there are two options:

* re-flag the leaf `pending reading`: count-neutral (`autofold-pending.json`, 11/18);
* fold the split (`autofold-split.json`, 12/18 on 30): one printed LEAF (existence) and one composite GLUE
  (conductor).

Either way the Lean transport stays proved.

### 4.1 The split (in `CarayolPrintedIrr.lean`, proved)

* `CarayolExistence` (published; Eichler–Shimura–Deligne + Ribet): some continuous, irreducible, odd `ρ` that is
  unramified with Frobenius traces `a_p`.
* `CarayolConductor` (composite: Carayol (A) + Casselman 1973): **every** continuous, irreducible, odd `ρ` that is
  unramified with traces `a_p` has `condExp = v_p(N)` at `p ≠ ℓ`. By Chebotarev and Brauer–Nesbitt such a `ρ` is
  isomorphic to Carayol's realization or its contragredient. So this is the conductor statement for `ρ_{f,λ}`, with no
  extra content.
* `carayolThmAIrr_of_split : CarayolExistence → CarayolConductor → CarayolThmAIrr` and `carayolR17'_of_split`,
  standard axioms.

The split cannot go further over genuine definitions. Carayol's (A) and Casselman's theorem are both statements about
`π_p`, which cannot be stated in Lean today. `CarayolConductor` is therefore the smallest Lean form of "(A) +
Casselman".

### 4.2 Statement check, what to read

1. DDT 1997 Thm 3.1 and the text after it: is the conductor equality `N(ρ_{f,λ}) = N` (prime to `ℓ`) stated? Are
   irreducibility and `det = ψ χ_ℓ` stated?
2. Carayol 1986 §0.8 p. 411: is the conductor equality stated for `ρ_λ`?
3. Ribet 1977 Thm 2.3: "irreducible" for weight 2 with nebentypus. Absolute irreducibility is no longer needed.

Proposed `locators.md` row (not added; the file belongs to other tasks):
`R17 (packaged, r17-rebase) | Carayol 1986 Théorème (A), §0.8; Casselman 1973; Ribet 1977 Thm 2.3; DDT 1997 Thm 3.1
| — | UNVERIFIED | ρ_{f,λ} over K_{f,λ}: irreducible, odd, traces a_p, conductor exponent v_p(N) at p ≠ ℓ; check that
the conductor packaging is printed for ρ_{f,λ}`.

## 5. The Burnside step (new Lean, VERIFIED)

`adjoin_eq_top_of_irreducible_odd`. Let `M : ι → M₂(K)` with `2 ≠ 0` in `K`. Suppose every `M`-stable subspace is
`⊥` or `⊤`, and the span `A` contains a `C` with `C² = 1` and `det C = −1`. Then `A = M₂(K)`. The proof has four
steps:

1. `e = (1+C)/2` and `f = (1−C)/2` are complementary idempotents in `A`.
2. Both are nonzero: otherwise `C = ±1`, whose determinant is `1`, not `−1`.
3. `exists_mul_mul_ne_zero` gives `a, b ∈ A` with `e a f ≠ 0` and `f b e ≠ 0`. Otherwise `range f` (or `range e`)
   is a nonzero proper stable subspace.
4. `e, f, e a f, f b e` are linearly independent: sandwich a relation between `e·_·e`, `f·_·f`, `e·_·f` and `f·_·e`.
   So `finrank A = 4 = finrank M₂(K)`.

In the leaf, `2 ≠ 0` holds in `K_{f,λ}` because it contains `K_f`. The involution `C = ρ(c)` comes from `c * c = 1`.

## 6. Step 5: count change and fold recipe

**Count on main's `kinds.tsv` (dry run, VERIFIED).** The strictest count goes from 11/18 on 29 H fields to 12/17 on
29 with the recommended spec, as expected for a LEAF. It is unchanged (11/18) if the leaf is rated GLUE (pending
reading).

**Scenario F.** It replaces `r17` by modular-split's `CarayolRealization` (a consequence, GLUE). The printed leaf
supersedes that split. `scratch/r17-rebase/ScenarioF.lean` copies `CarayolRealization` verbatim (diff-identical to
`scratch/modular-split/R17.lean` L127). It proves `carayolRealization_of_printed`
(`CarayolThmA → EigenformCoeffFieldFinite → CarayolRealization`) and the `CarayolThmAIrr` variant, both on the standard
axioms. So Scenario F's row for `r17` can take this leaf in place of `CarayolRealization`.

**Fold recipe for the integrator:**

1. `git merge origin/wip/r17-rebase`. It adds four files under `ZInQKernel/Contrib/OneProof/`: `NewformDict.lean`,
   `CarayolLevel.lean`, `CarayolPrinted.lean` and `CarayolPrintedIrr.lean`. No other file under `ZInQKernel/` is
   touched.
2. `python3 scripts/one_proof/autofold.py scratch/r17-rebase/autofold.json`. It writes `TailZ56` with
   `OpenResearchLeaves32` (`r17` removed, `carayolThmAIrr` added) and `sixContactMin_of_open49`, and switches
   `Main.lean`. The proof term uses `{n}.eigenformCoeffFieldFinite`. If a fold has meanwhile removed that field from
   the research bundle, substitute that fold's proof term.
3. Run the usual checks:
   * `lake build +ZInQKernel.OneProof.Main`;
   * `#print axioms ZInQ.OneProof.frozenTarget`;
   * `DumpCompact` + `cmp_hashes.py`;
   * `OpenStatements.lean`, `render_open.py`, `render_open.py --check`;
   * add the locators row of §4.2.
4. Add the statement-check item of §4.2. If the check rejects the conductor packaging, re-flag the row
   `pending reading` (or fold `autofold-split.json` instead).

`autofold-burnside.json` (r17-print's leaf) is superseded by `autofold.json`. It has the same count, but its leaf
carries the unprinted Burnside clause.

## 7. Files

* `ZInQKernel/Contrib/OneProof/CarayolPrintedIrr.lean` (new, 20 KB).
* `scratch/r17-rebase/`:
  * the fold: `autofold.json`, `autofold-burnside.json`, `autofold-split.json`, `autofold-pending.json` and their
    `*-dryrun.txt`; `AutofoldDryRun.lean`, `AutofoldDryRunSplit.lean`, `FrozenTargetDryRun.lean` and their
    compile outputs;
  * the discharge: `Discharges.lean`, `discharges.txt`; `ScenarioF.lean`, `scenarioF.txt`;
  * the clash check: `AllContrib.lean`, `AllContrib2.lean`, `tops.py`, `closure.py`, `clashloop.sh`,
    `clashloop-out.txt`, `NewNames.lean`, `new-names.txt`, `DroppedTopCheck.lean`, `dropped-top-check.txt`,
    `build-all-summary.txt`;
  * `R17Statement.lean.txt` and `log.md`.

## 8. What remains

* The statement check of §4.2 (DDT 1997 Thm 3.1, Carayol §0.8, Ribet 1977 Thm 2.3). It decides between −1 and 0.
* The fold itself (integrator), and the pre-existing clash `ZInQKernel.Contrib.AllContrib` ↔
  `HDecomp.Textbook.Different` (not this task's).
* Separately, `eigenformCoeffFieldFinite` (composite, pending reading). The discharge uses it only at `k = 2`
  (Diamond–Shurman Thm 6.5.1, UNVERIFIED), as r17-print noted.

# r16-shimura73: `r16CoreY` along the manuscript's own sources (Li 1975, Shimura 1973 Thm 1)

Task r16-shimura73 (2026-11-17). Scratch: `scratch/r16-shimura73/` (log `log.md`). Lean:
`ZInQKernel/Contrib/OneProof/R16ShimuraLi.lean` (namespace `R16ShimuraLi`).

## Known issues (for the lead, to raise with Jack)

1. **The manuscript's inference at diophantine_zq.tex L770-773 has the gap the review recorded, and this re-route
   reaches it.** The manuscript passes from "Li's Fricke formula makes the span of the coefficient conjugates
   Fricke-stable" and "Shimura's quotient construction and Euler-factor identity" to "`r_5` is a constituent of the
   Tate module of `A_f`". What Shimura 1973 Thm 1 gives (per the locator audit, row R16 of
   `docs/research/locators.md`, which read pp. 526-527) is the `ℚ`-rational quotient `A_f` of `J₁(N)`, the action of
   `K_f`, `dim A_f = [K_f : ℚ]`, and, under the Fricke-stability premise, the equality of the zeta function of `A_f`
   with `∏_σ L(s, f^σ)` (up to finitely many Euler factors). In Lean (`EulerIdentity`): the characteristic polynomial
   of Frobenius on all of `V_ℓ(A)` is `∏_{ι : K_f → ℂ} (X² − ι(a_p) X + ι(χ(p)) p)`.
   **What is missing.** That identity is a statement about the total characteristic polynomial; it does not mention
   the `K_f`-action at all, so it cannot say which `ι`-component of `V_ℓ(A)` carries which conjugate. Concretely
   (ON THE SPOT, a two-line remark, not built on): if `θ` is an action with the per-embedding property, `θ ∘ τ` for
   `τ ∈ Aut(K_f/ℚ)` satisfies the same Euler identity but its `ι`-component carries `ι(τ(a_p))`; and the multiset
   equality `⋃_ι {roots of the ι-component} = ⋃_ι {α_ι, β_ι}` does not split per `ι`. "`r_5` is a constituent of
   `V_5(A_f)` with traces `ι_5(a_p)`" (what L774-794 then use at `ℓ = 3, 5`) needs a per-embedding statement.
   **Which statement the chain would need.** `R16ShimuraLi.ShimuraTotalToComponents` (named, not proved, not
   repaired): for a quotient `π : J₁(N) ↠ A` of dimension `[K_f : ℚ]` whose Euler factors are Shimura's, some action
   `θ'` of `K_f` makes every `ι`-component of `V_ℓ(A)` carry trace `ι(a_p)` and determinant `ι(χ(p)) p` at every
   `p ∤ Nℓ`. The printed statement that supplies it is the Eichler-Shimura relation on `A_f` with `θ` the Hecke action
   (Shimura 1971 Thm 7.9 with Thms 7.11/7.14; Diamond-Shurman Thm 9.6.5 at `k = 2`, i.e. the Diamond-Shurman row
   `afCharpolyDS965` this task replaces); neither is cited at L768-773. With `∀ θ` instead of `∃ θ'` the needed
   statement is false (the `θ ∘ τ` remark).
2. **Shimura 1973 Thm 1 as the manuscript uses it is weaker than the use.** Besides item 1, the print's Euler-factor
   clause holds up to finitely many Euler factors (the exceptional set is UNVERIFIED here; the leaf takes an
   unspecified finite set, the weakest reading). The chain needs every `p ∤ Nℓ`; with a nonempty exceptional set that
   also needs good reduction of `A` outside `N` and Chebotarev (folded into `ShimuraTotalToComponents`).
3. **Step not covered by the two citations: Li's formula is applied to every conjugate `f^σ`**, which needs the
   conjugates to be newforms (`ConjNewform`: Shimura 1971 Thm 3.52 with the Galois stability of the new space,
   numbers UNVERIFIED). Small and standard, but uncited at the step.

Verdict: the re-route compiles as a reduction (`r16CoreY_of_shimura_li`), but it ends in the known gap. The two
printed leaves plus `ConjNewform` prove `R16CoreYTotal` (the per-embedding clause replaced by Shimura's total Euler
identity) with no other input; `r16CoreY` itself needs `ShimuraTotalToComponents`, which no cited source gives.
**Recommendation: do not fold before Jack rules on item 1.** The autofold spec is written and dry-run (section 5) so
that the fold is ready either way.

## 1. Where `r16CoreY` sits on leaf-fold33b (VERIFIED, grep and reading)

* `r16CoreY` is no longer a top field. It is filled in `openResearchLeaves40_of_OpenResearchLeaves41_cf`
  (`ZInQKernel/OneProof/H/TailZ74.lean:802`) by
  `AfTateLam.r16CoreY_of_ds965 n.heckeJ1DS n.afShimura n.afCharpolyDS965 n.igusaGL2DS mumfordTorsionAlgClosed_proof`.
  The top bundle `OpenResearchLeaves48` carries heckeJ1DS, afShimura, afCharpolyDS965 and igusaGL2DSGalSome
  (turned into igusaGL2DS at TailZ74.lean:1355). None of the four is read anywhere else under `ZInQKernel/OneProof/`.
* `dsThm965Printed` is read elsewhere (`panBerger_of_printedPV`, TailZ74.lean:709), so it stays.
* `r16CoreY` is read only through `R16Split.r16_of_printed`, which gives the field `r16` (`R16_EichlerShimuraJ1'`).

## 2. The leaves (Lean: `ZInQKernel/Contrib/OneProof/R16ShimuraLi.lean`)

| name | what it states | kind | printed form? |
| --- | --- | --- | --- |
| `LiFrickePrinted` | for a newform `g ∈ S₂(Γ₁(N))` (kernel `IsNewform`), `g ∣₂ W_N = λ · ḡ`, with `ḡ ∈ S₂(Γ₁(N))` the form with coefficients `conj(a_n(g))` (`W_N = TauCeti.frickeGL ℝ N`, Mathlib's slash) | published | **Yes, printed form**: Li 1975 p. 296 (manuscript's locator, UNVERIFIED) specialized to `k = 2`, `|λ| = 1` dropped; the normalization of `W_N` and of the slash only rescales `λ`, which is existential. Rests on the kernel's `IsNewform` dictionary (its docstring). |
| `ShimuraThm1Printed` | `K_f` finite; `∃ A, π : J₁(N) ↠ A, θ : K_f → End⁰(A)` with `dim A = [K_f : ℚ]`; and `FrickeStable N f → EulerIdentity N χ f A` (charpoly of Frobenius on `V_ℓ(A)` = `∏_{ι : K_f → ℂ} (X² − ι(a_p) X + ι(χ(p)) p)`, `p` outside a finite set, `p ∤ Nℓ`) | published | **Yes, printed form, weakened**: `A` existential (the print's `A = J/I_f J` with the Hecke action has no non-Diamond-Shurman Lean object), the Euler clause's exceptional set unspecified. The Euler factor is read on `V_ℓ(A)` (Weil's identification of the Frobenius of the reduction with Frobenius on the Tate module: standard, not a separate leaf here). Locator: pp. 526-527 per the audit; Euler-clause wording UNVERIFIED. |
| `ConjNewform` | a cusp form in `S₂(Γ₁(N))` with coefficients `σ(a_n(f))`, `f` a newform, is a newform | consequence (GLUE) | **Not** printed form at this step: not cited by the manuscript; Shimura 1971 Thm 3.52 + Galois stability of the new space (UNVERIFIED). |
| `ShimuraTotalToComponents` | the known-issue statement (Known issues, item 1) | consequence (GLUE) | **No**: no print, and the manuscript does not state it. |

Definitions (no new structures, all over Mathlib/kernel objects): `IsConjOf` (coefficients `σ(a_n(f))`), `conjSpan`,
`FrickeStable` (generator form; equivalent to stability of the span since the slash by `W_N`, `det > 0`, is
`ℂ`-linear), `EulerIdentity`, `R16CoreYTotal`.

## 3. The derivation (following L768-773)

1. `frickeStable_of_li : LiFrickePrinted → ConjNewform → IsNewform f χ → FrickeStable N f` (proved): for a conjugate
   `g = f^σ`, Li gives `g ∣ W_N = λ ḡ`, and `ḡ` is the conjugate `f^{c∘σ}`. Uses `ConjNewform` (Known issues 3).
2. `r16CoreYTotal_of_shimura_li : ShimuraThm1Printed → LiFrickePrinted → ConjNewform → R16CoreYTotal` (proved).
   This is everything the two citations give.
3. Steps the two cited statements do not cover, for `R16CoreY`:
   * per-embedding traces and determinants: **not given** by Shimura's Thm 1 (Known issues 1). The task asked
     whether Thm 1 gives `V_ℓ(A_f)` free of rank two over `K_f ⊗ ℚ_ℓ`: per the locator audit it does not
     ("individual-embedding rank-two Tate realization ... must still be supplied"). That freeness is in any case
     not the missing piece: the kernel proves the rank-two clause from `dim A = [K_f : ℚ]` and Mumford §19 Thm 4
     (`R16Split.rank_two_of_dim`), so `r16` needs only `R16CoreY`. Even with rank two, the total identity does not fix
     the per-`ι` traces (the `θ ∘ τ` remark), so the missing statement is the Frobenius-Hecke relation, not freeness.
   * all `p ∤ Nℓ` from Shimura's cofinite identity (Known issues 2).
   * conjugates are newforms (Known issues 3).
4. `r16CoreY_of_total : R16CoreYTotal → ShimuraTotalToComponents → R16CoreY` and
   `r16CoreY_of_shimura_li` (composition). The chain stops at `ShimuraTotalToComponents` as instructed.

## 4. Consumers of `r16CoreY` (VERIFIED: TailA.lean:3404-3453, R16Split.lean:549-576, R16Used.lean:7-13)

`r16CoreY → r16` (`r16_of_printed`; `dim A` is used only to derive the rank-two clause) has one consumer on the route,
`G0ModNewform.g13 → commonConstituent_of_attached` (TailA.lean:3404), at `ℓ = 5` and the single embedding
`embOf 5 ι_C ι_5`. It uses: `π` surjective, rank two of that one `ι`-component, and the trace identity
`tr(Frob_p) = ι(a_p)` on it at every `p ∤ 5N` outside a finite set (fed to `c9_core`: Brauer-Nesbitt and Frobenius
density). It does not use the determinant clause, `[K_f : ℚ] < ∞`, other `ℓ`, or other embeddings.
Compared with the manuscript's use at L770-794 (`r_5` a constituent of `V_5(A_f)` with its modular traces at five
for `p ∉ T ∪ {3,5}` away from the level; the modular Tate representation at three for `r_3`): the Lean consumer needs
the same per-embedding trace at `ℓ = 5` (the clause the known gap leaves open), and **nothing at `ℓ = 3`** (the Lean
route does not use `r16` at three). `R16CoreY` itself asks more than either: the determinant clause (unused), every
`ℓ` and every embedding, and `dim A = [K_f : ℚ]` (used only for rank two). A narrower field (trace only, one `ℓ`)
would not avoid the gap: the trace at one embedding is exactly what the Euler identity does not give.

## 5. Fold: autofold spec, dry run, rows

The autofold script discharges fields of the top bundles only, and `r16CoreY` is not one now. So the fold is two
steps:
* **Step 1** (`scratch/r16-shimura73/gen_r16_restore.py` → `TailZ75R16.lean`, to go in as
  `ZInQKernel/OneProof/H/TailZ75.lean`): copies `OpenResearchLeaves41CF`-`46CF`, `48` and their conversions from
  TailZ74 with heckeJ1DS, afShimura, afCharpolyDS965, igusaGL2DS(GalSome) replaced by the single field `r16CoreY` (their
  consequence), top `sixContactMin_of_open68 (r : OpenResearchLeaves49)`; Main switched (three-line diff); kinds.tsv:
  the four rows replaced by one `r16CoreY` row (consequence, GLUE).
* **Step 2** (`scratch/r16-shimura73/autofold.json`): discharges `r16CoreY` by
  `R16ShimuraLi.r16CoreY_of_shimura_li` with leaves `shimuraThm1Printed`, `liFrickePrinted`, `conjNewform`,
  `shimuraTotalToComponents`.
* Dry run (on a temporary tree `/tmp/r16af` with step 1 applied; nothing in the worktree written):
  `strict count: 4/24 on 28 -> 4/27 on 31; strictest 4/24 -> 4/27` (needs `--allow-rise` relative to step 1; against
  the base, 4/27 on 31 before and after: no rise). Output `scratch/r16-shimura73/autofold-dryrun.txt`.
* **Rows that disappear**: heckeJ1DS, afShimura, afCharpolyDS965, igusaGL2DSGalSome. dsThm965Printed stays (read by
  `panBerger_of_printedPV`). Proofs already folded (igusa-gal's `igusaGL2DS_of_igusaGL2DSGalSome`, the
  AfTateLam/HeckePin files) stay in the tree, unused by the new top.
* **kinds rows** (as in the spec):
  * `shimuraThm1Printed` — published; flag "unread: new printed leaf ...; locator UNVERIFIED" (GLUE until read).
  * `liFrickePrinted` — published; flag "unread: new printed leaf ...; locator UNVERIFIED" (GLUE until read).
  * `conjNewform` — consequence; flag "pending reading: not cited by the manuscript at this step ..." (GLUE).
  * `shimuraTotalToComponents` — consequence; flag "pending review: known issue at L770-773 ...; do not fold before
    the owner rules" (GLUE).
* `#discharges`: see section 6.

## 6. Compile outcomes (VERIFIED, 2026-11-17)

* `lake env lean ZInQKernel/Contrib/OneProof/R16ShimuraLi.lean`: no errors, no warnings (after renaming a bound `ι`,
  a reserved token here, and dropping `open Polynomial`). `lake build ZInQKernel.Contrib.OneProof.R16ShimuraLi
  ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges`: success (16216 jobs); `frozenTarget` standard axioms.
* `scratch/r16-shimura73/FoldCheck.lean` (imports TailZ74 and R16ShimuraLi; contains the step-1 module and the
  step-2 dry-run module verbatim): compiles; `sixContactMin_of_open68`, `sixContactMin_of_open69`,
  `r16CoreY_of_shimura_li`, `r16CoreYTotal_of_shimura_li` depend on `[propext, Classical.choice, Quot.sound]`
  (`FoldCheck-output.txt`).
* `#discharges` (`scratch/r16-shimura73/DischargesCheck.lean`, output `DischargesCheck-output.txt`): "36 open
  hypotheses, 15748 theorems checked, 19 discharge one"; **none by `R16ShimuraLi`**, as expected: `r16CoreY` is not an
  open hypothesis of the current `frozenTarget` (it sits below the top, section 1). The discharge against the step-1
  top is checked by FoldCheck instead (open69 fills `r16CoreY := R16ShimuraLi.r16CoreY_of_shimura_li ...`).

## 7. What remains

* Jack's ruling on Known issues 1 (and 2). If the ruling is to keep the manuscript's sources, a reader of Shimura 1973
  pp. 523-529 should check whether Thm 1 (or §0, or Thm 2) states the Frobenius-Hecke relation or a per-factor Euler
  identity; then `ShimuraTotalToComponents` could be replaced. Otherwise the Diamond-Shurman route (afCharpolyDS965)
  stays, and this fold should not be applied.
* Readings: Li 1975 p. 296 (statement, normalization of `W_N` and `\bar f`), Shimura 1973 Thm 1 (the Euler clause's
  premise and exceptional set), a print for `ConjNewform`.

## 8. Proposed locator rows (for `docs/research/locators.md`; not edited here, it is another task's file)

| leaf | source | locator | status |
| --- | --- | --- | --- |
| `liFrickePrinted` | W.-C. W. Li, Newforms and functional equations, Math. Ann. 212 (1975), 285-315 | p. 296, before Lemma 6 (manuscript's locator) | UNVERIFIED (not read; no network) |
| `shimuraThm1Printed` | G. Shimura, On the factors of the jacobian variety of a modular function field, J. Math. Soc. Japan 25 (1973), 523-544 | Theorem 1, pp. 526-527 (locator audit row R16) | page read by the audit; the Euler clause's premise/exceptional set UNVERIFIED |

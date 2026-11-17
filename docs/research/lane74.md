# lane74: Route K out, the manuscript's pole polynomial back, headline H + PC (fork issues #76-#79)

**Result.** The headline is now

    theorem ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_poleCompleteness
        (hH : SixContactMin) (hPC : PoleCompleteness) : FrozenTarget

(`ZInQKernel/MainGreenTao.lean`), with axioms `[propext, Classical.choice, Quot.sound]`, and

    theorem ZInQ.OneProof.frozenTarget
        (r : HDec.HSyn.OpenResearchLeaves48) (t : HDec.HSyn.OpenTextbookLeaves18)
        (l : HDec.HSyn.OpenAddedLeaves27) (hPC : ZInQ.PoleCompleteness) : ZInQ.FrozenTarget

with the same three axioms. `PoleCompleteness` is the manuscript's Theorem 5.2 for the manuscript's own
pole polynomial `Q_pole` (`diophantine_zq.tex` lines 976-982, curves `y² = x(x - ℓ)(x + 3ℓ)`; Theorem 5.2 at
lines 1001-1004). `h21S`, `hCM`, `h33c`, `hBFH`, `hGZss` are gone. VERIFIED (compiled; see the check list).

The work is in four commits on `wip/lane74`: #77 (deletion), #76 (polynomial), #78 (headline), #79 (board).
The status of each check is in section 5 and in `scratch/lane74/log.md`.

## 1. #77: tag and deletion

* Tag `route-k-final` on `bf691da2236b494bb429caabc2f907d4ea428c4d`, taken from
  `grep LANDED ~/dzq-runs/landed.txt | tail -1 | cut -d' ' -f1` (chk-w104 green, main fast-forward). The tag
  exists locally; `git push origin refs/tags/route-k-final` failed (CONNECT tunnel 403) and was not retried.
  **Lead: push it** (`scratch/lane74/TAG.md`).
* Import graph of all 7145 tracked `ZInQKernel` modules (`scratch/lane74/graph.py`, `delset.py`): the named set
  (`RouteK/**`, `Contrib/{TYZChain,TYZDecomp,TYZGenus,GZDecomp,GZStatements,GZTheta,HeckeFE}`, `MainLiterature`,
  `Hypotheses/{CertifiedRank,CR3Literature,TYZInputs}`, `OneProof/{TYZSplit,TopChain}`, and the 130
  `Contrib/OneProof` modules in the import closure of `OneProof/Main`'s TYZ/GZ imports that the H chain does not
  import), closed under importers (forced: `GaussFE/Headline`, `PSide/*` except `TYZInputsIff`, three
  `NonVacuous`/`OptimalUnique` files, `TYZGenusFold/QI`, `TYZSquareOddness`, `TYZThm21PairsOne`): 298 modules.
* **Deleted: 220 files, 70 475 lines** (`scratch/lane74/deleted-files.txt`). VERIFIED.
* Import lists edited: root `ZInQKernel.lean` (23 imports: the deleted modules and the Route K/CR3 modules now
  reached only through the H chain), `Contrib/AllContrib.lean` (51), `scripts/print_axioms.lean` (Route K, CR₃,
  literature and Proposition N lines replaced by the new headlines; 463 declarations, all standard).

### Importer findings (not deleted)

1. **The H chain imports 78 of the named files** (27 831 lines; `scratch/lane74/kept-h-reach.txt`). One entry
   point: `OneProof/H/TailZ34.lean` imports `Contrib/OneProof/RayClassShimura.lean`, which imports
   `Contrib/TYZGenus/ShimuraModFn.lean` (and `Contrib/OneProof/RingClassLattice.lean`, also on the H path,
   imports `TYZGenus.ShimuraModFn` and `TYZGenus.ShimuraMain`). From there the closure reaches
   `TYZGenus.{ShimuraField, ShimuraZn, ShimuraRecip, RingClassBridge, Package, RingClass, ...}` →
   `TYZDecomp.Leaves` → `HeckeAll.Provider` → `{GaussFE.FunctionalEquation5, HeckeAll.Continuation}` →
   `HeckeFE.Basic` → `{RouteK.Rank.LFunctionCd, Hypotheses.CR3Literature}`; `TYZDecomp.Leaves` →
   `PSide.TYZInputsIff` → `RouteK.PropN`; `TYZGenus.RingClass` → `RouteK.Rank5b.Sec3.RedeiStatement`,
   `RouteK.Redei.FourRank`, `Hypotheses.TYZInputs`; and with them `RouteK.{Slots, System, Selmer.*,
   Assembly.Realize, Rank.*, Rank5b.*, Redei.*}` and `Hypotheses.CertifiedRank`. VERIFIED (BFS path).
   None of these is used by the new headline; they stay only because the H chain's import of
   `RayClassShimura` pulls them in. To delete them, `RayClassShimura`/`RingClassLattice` must stop importing
   `TYZGenus.ShimuraModFn` (move the declarations they read into an H-side file); that edits H Contrib files,
   which this task may not do.
2. `Density/CharSum.lean` (Proposition D, on the headline's path through `MainGreenTao`) imports
   `RouteK/Selmer/CharSum.lean` (character sums over finite fields, Mathlib only). Kept in place.
3. `scratch/contrib-check/Check.lean` (the chain's CONTRIB-CHECK step) imports deleted modules and states
   `contribCheck_headline` over the deleted literature headline. A copy with those imports and lines removed is
   `scratch/lane74/contrib-check-Check.lean` (other tasks' scratch is not edited); **lead: replace the chain's
   file with it, or drop the step.**
4. **blueprint/ references 199 deleted declaration names in 59 articles** (`main` 10, `rank` 38, `rank-5b` 7,
   `route-k` 4; list in `scratch/lane74/autoform-check-leanroot-final.txt`, per article in `scratch/lane74/blueprint-dangling-articles.txt`). `autoform check blueprint`
   passes; `autoform check blueprint --lean-root .` and `render --require-declarations` fail until those
   articles are removed or rewritten. blueprint/ is not editable here: **for #81** (Jack's docs session).

## 2. #76: the manuscript's pole polynomial

* `ZInQ.polePoly` (`Hypotheses/Pole.lean`) and `poleT1`/`poleT2` (`Syntax/Templates/Core.lean`) are back to
  `A + 3e` and `Az² + 3eH`. `Parity.lean`, `Assembly/Local/PoleObstruction.lean` and `Core.lean` are restored
  byte for byte from `b570b14ee` (= `git rev-parse 2d8a1fe51^`); they use upstream's
  `ZInQ.ValuationObstruction.poleSystem_no_negative_odd_valuation` (`lean/ZInQ/PoleValuation.lean`). The Route K
  copies `Mult.poleSystem`, `congruentCurve_rhs_nonzero_and_valuation` and the `x + ℓ` lemma are gone.
* One definition: `ZInQ.Manuscript.polePoly`, `PoleSoluble`, `PoleCompleteness` (`Hypotheses/PoleManuscript.lean`)
  are now `abbrev`s of `ZInQ.polePoly`, `ZInQ.PoleSoluble`, `ZInQ.PoleCompleteness`, and
  `Manuscript.polePoly_eq` checks by `rfl` that it is the manuscript's `Q_pole` written out.
  `Manuscript.curve`, `AnalyticRankOne`, `RestrictedConverse` (Theorem 5.3 schema) are unchanged.

## 3. #78: headline and frozenTarget

* `Main.lean`: the CR₃ headlines are gone; kept `..._of_poleCompleteness (hH) (hPC) (h22)`; added
  `..._of_poleCompleteness_goodPrimeAP` and `..._of_poleCompleteness_greenTaoDense` (the former `_of_goodPrimeAP`,
  `_of_greenTaoDense` with PC in place of CR₃).
* `MainGreenTao.lean`: `..._of_poleCompleteness_goodPrimeDensity` and the headline
  `..._of_sixContactMin_poleCompleteness (hH : SixContactMin) (hPC : PoleCompleteness) : FrozenTarget`, by
  route AP with `greenTaoDense` and `Density.goodPrimeDensity` (as `..._of_sixContactMin_certifiedRank` did).
* `OneProof/Main.lean`: imports `OneProof.H.TailZ74` and `MainGreenTao` only; `frozenTarget` as above.
* On-the-spot clause: no new mathematical statement. The new theorems are the old variants with PC (the
  manuscript's Theorem 5.2) in place of CR₃; `polePoly_eq` is `rfl`. Nothing is labelled on-the-spot.

## 4. #79: the board

* `docs/one-proof/kinds.tsv`: the five TYZ/GZ rows removed, one row `hPC` (bundle `frozenTarget`, kind
  `manuscript hypothesis`, GLUE/GLUE, flag "ELLIOT: Theorem 5.3 route in progress (#83)", flag class `note`,
  source the manuscript's Theorem 5.2, lines 1001-1004, area issue `Deicyde/diophantine-z-q#83`).
* `scripts/one_proof/render_open.py`: the count line names the manuscript hypotheses outside the H part; the
  section "Tian–Yuan–Zhang and Gross–Zagier hypotheses" is now "Manuscript hypotheses outside the H part".
  `autofold.py` needs no change: its parser reads the `HDec.HSyn` binders, the
  `(HDec.HSyn.sixContactMin_of_openN r t l)` call and the `TailZ` import, which the new `Main.lean` keeps.
* `open-statements.json` regenerated by `OpenStatements.lean`; OPEN.md, pages-wanted.md, the STATUS.md count
  block regenerated by `render_open.py`.

## 5. Checks (each VERIFIED on this host, warm build copied from ~/dzq-check2 at 74395dcf)

| check | after #77 | after #76 (final Lean) | after #79 |
| --- | --- | --- | --- |
| `lake build ZInQKernel` | OK (9923 jobs) | OK (9923 jobs, 7 min) | (no Lean change) |
| `lake build +OneProof.Main +OneProof.Discharges Contrib.AllContrib` | OK | OK (16104 jobs, 35 min: the H chain rebuilt, `RouteK.Slots.Basic` on the H path imports `Pole.lean`) | |
| every tracked `Contrib/*.lean` (CONTRIB-BUILD) | OK (15533 jobs) | OK (15533 jobs) | |
| `#print axioms ZInQ.OneProof.frozenTarget` | standard | standard | |
| `scripts/print_axioms.lean` + `check_target.py` | 463 decls, 0 nonstandard | 463 decls, 0 nonstandard, target ok | |
| `scratch/lane74/contrib-check-Check.lean` | | compiles, 117 decls, 0 nonstandard | |
| `render_open.py --check` | fails (board stale) | fails (board stale) | ok, 32 open hypotheses |
| `autoform check blueprint` | OK | OK | OK |
| `autoform check blueprint --lean-root .` | 199 dangling names | 199 | 199 (blueprint/ not editable: #81) |

Not run (the lead runs the full chain): `scratch/h-decomposition/Leaves.lean`, autoform audit/render, mkdocs,
site check. `render --require-declarations` will fail on the same 199 names until #81 lands.

## 6. For the lead

1. Push the tag: `git push origin refs/tags/route-k-final` (local tag on `bf691da2`).
2. Replace `scratch/contrib-check/Check.lean` with `scratch/lane74/contrib-check-Check.lean` before the chain
   (the old file imports deleted modules, so CONTRIB-CHECK fails).
3. The site's `--lean-root` check and render fail until #81 removes or rewrites the 59 blueprint articles in
   `scratch/lane74/blueprint-dangling-articles.txt`. So the land request should wait for #81, or come with it.
4. Finding 1 (78 Route K/TYZ files kept because `OneProof/H/TailZ34` → `RayClassShimura` imports
   `TYZGenus.ShimuraModFn`): an H-side follow-up can cut that import, and then delete the 78 files
   (`scratch/lane74/kept-h-reach.txt`).
5. `scratch/contrib-kit/DischargesTest-output.txt` is stale (36 hypotheses, now 32). It is only a note in
   `render_open --check`.

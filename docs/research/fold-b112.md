# fold-b112: five folds on wip/leaf-fold33b (bost-gr9, sz-raynaud, row edits, y3-route-a + carirr-refold, r3prime)

Task fold-b112, 2026-11-17. Base: wip/leaf-fold33b d435851d, which is fork main after lane74. Its H top was
`sixContactMin_of_open72` (TailZ79, `OpenResearchLeaves53`).
- Counts before: 30 open; H 29; strict and strictest 5/24.
- Branch wip/fold-b112 is the base plus this task's commits, so it fast-forwards from d435851d.
- Results log: `scratch/fold-b112/log.md`.
- Replay: `scratch/fold-b112/REPLAY.md`.

This is model work; no person has reviewed it.

**No manuscript step was found to be an error** (no "error" verdict in any Manuscript check below).

## 1. Result

**All the folds are in: 1, 2, 4a, 4b and 5, plus the row edits of 3. Each one builds; `frozenTarget` uses only the
standard axioms; every check passes, including `scratch/lane74/gate.sh` with GATE=ok after each fold.** Every fold is
count-neutral: the integrator queued them as count-neutral, and none changes a rating.

| fold | effect | new top | open | H strict / strictest |
| --- | --- | --- | --- | --- |
| base | | `sixContactMin_of_open72` (TailZ79, `OpenResearchLeaves53`) | 30 | 5/24 on 29 |
| 1 bost-gr9 | `bostLowerBoundAnSS` → `gaudronRemondSec9LowerAnSS` (weaker-leaf bypass) | `sixContactMin_of_open73` (TailZ80, `OpenResearchLeaves54`) | 30 | 5/24 on 29 |
| 2 sz-raynaud | `raynaudSemistableSHOr` → `silverbergZarhinThm35` (autofold) | `sixContactMin_of_open74` (TailZ81, `…55`) | 30 | 5/24 on 29 |
| 3 row edits 62, 64b | done inside fold 1 (62 was already on the base; 64b applied) | — | 30 | 5/24 on 29 |
| 4a y3-route-a | `y3FineModuliAbP` → `y3FullThreeRepZ30` (autofold) | `sixContactMin_of_open75` (TailZ82, `…56`) | 30 | 5/24 on 29 |
| 4b carirr-refold | `carayolThmAIrr` → `carayolThmAFrob` (autofold) | `sixContactMin_of_open76` (TailZ83, `…57`) | 30 | 5/24 on 29 |
| 5 r3prime-etale + r3prime-bc | R3′ proved; caveat removed from 3 flags; no field change | unchanged | 30 | 5/24 on 29 |

**The task's acceptance rule.** The rule says a fold goes in only if it lowers the strict GLUE count or removes a
field. No fold here does either. They went in anyway because the integrator's instructions name each of them and
call them count-neutral (inbox 59, 64a, 67, 68). Fold 5 changes no Lean statement at all; it is the integrator's
inbox-68 flag update.

### Fold 1: bost-gr9, regenerated on this head

- **Base drift.** bost-gr9 replaced the field `bostLowerBoundAn` on d67ea55f. On this base that field had become
  `bostLowerBoundAnSS`: semistab-assembly (fold-b105) put Bost's bound over `IsAnStableHeightSS`, with
  semistability as printed.
- **New Contrib file** `ZInQKernel/Contrib/OneProof/GaudronRemondSection9SS.lean`, committed separately from the
  fold, so that the sibling rows keep their printed semistability:
  - `ZInQ.BostGR9.GaudronRemondSec9LowerAnSS`: bost-gr9's leaf, verbatim, over `IsAnStableHeightSS`, the change
    semistab-assembly made to Bost and to GR Thm 1.4;
  - `gaudronRemondSec9LowerAn_of_ss`: it gives bost-gr9's leaf, so bost-gr9's proved route to R21 is reused
    unchanged;
  - `gaudronRemondSec9LowerAnSS_of_bostLowerBoundAnSS`: the replaced field implies the new leaf, so the leaf is
    never stronger than the field.

  All three use the standard axioms (VERIFIED). This is GR14 §9, the manuscript's own citation, not an on-the-spot
  statement.
- **Generator** `scratch/fold-b112/gen_gr9_fold.py`, regenerated from bost-gr9's `gen_bypass.py`:
  - its closure metaprogram runs from Main's current top and finds 90 declarations: TailZ79 3, TailZ74 10,
    TailZ69 1, EichlerBoundCopy 76;
  - the EichlerBoundCopy part is identical to bost-gr9's list;
  - the 89 declarations below the top bundle are copied verbatim into `HDec.HSyn.GR9`;
  - the field's type is weakened at each generation (`HeightSplit.BostLowerBound` → `GRBostBound`);
  - the reader becomes `BostGR9.grBostBound_of_sec9Printed (BostGR9.sec9Printed_of_an
    (BostGR9.gaudronRemondSec9LowerAn_of_ss n.gaudronRemondSec9LowerAnSS) _) _ _
    ChevFree.semiAbelianDescendsPerfect_proof`, and `r21_of_leaves'` becomes `r21_of_grBost'`;
  - the top bundle becomes `HDec.HSyn.OpenResearchLeaves54` (27 fields).
- **Closure check.** None of `BostLowerBoundAnSS`, `R3Residual.BostLowerBoundAn`, `HeightFix.BostLowerBoundPrinted`
  or `HeightSplit.BostLowerBound` is in the closure of `frozenTarget`. `#discharges` cannot show the field, because
  this is a bypass: the leaf is weaker than the field.
- **Kinds row** `gaudronRemondSec9LowerAnSS`:
  - kind published, GLUE/GLUE, flag_class pending-reading;
  - the flag begins "pending reading (GR p. 2098 normalization)" and contains "cited inside a proof (Lemme 9.1 …)",
    R3′ (removed in fold 5) and "provenance cited";
  - packet, label, tier and area_issue come from the old row.
- **Javanpeykar docstring (inbox 62).** The corrected semistability phrase is in the new structure's
  `javanpeykarThm111An` field doc, and autofold carries it to generations 55-57. JavanpeykarAnRetype.lean, TailZ78
  and TailZ79 are not rebuilt by any fold here, so they are not edited.

### Row edits (3), done in fold 1

- **62:** both replacement texts in the `javanpeykarThm111An` row were already present on the base (VERIFIED).
- **64b:** the phrase to replace, "Berger survey IV.5.1, cited print", is **not** in the `bergerSurveyF` row on this
  base (VERIFIED by grep).
  - I replaced the leading survey citation of the source column with the lead's text (Brinon–Conrad Thm 9.3.5, the
    manuscript's citation; the survey "not in the manuscript's bibliography").
  - I kept the survey sections the Lean form uses, the Inventiones numbering and the Lean pointers
    (`row_edits_64b.py`).
  - Rating unchanged.

### Folds 2, 4a, 4b: autofolds

Each fold used the branch's own spec, unchanged and copied into `scratch/fold-b112/`, and was regenerated on this
line (TailZ81-83, not the branches' numbers). `#discharges` on each preceding head lists the field as DISCHARGED:
- by `SZRaynaud.raynaudSemistableSHOr_of_sz35`;
- by `Y3RouteA.y3FineModuliAbP_of_z30`;
- by `CarayolRefold.carayolThmAIrr_of_frob`.

Each still assumes only its new leaf, and all three use the standard axioms.
- **sz-raynaud:** `ElliotWildInertiaTrivial` is not in the spec, so no row with nothing discharged is added (inbox
  64a).
- **carirr-refold:** the audit's `carayolThmAIrr` row moved from reviews.tsv to reviews-retired.tsv, because
  render_open's row check required it.
- **New rows:**
  - `silverbergZarhinThm35`: published, LEAF/LEAF, as was `raynaudSemistableSHOr`;
  - `y3FullThreeRepZ30`: consequence, ELLIOT, GLUE;
  - `carayolThmAFrob`: published, unread, GLUE.

### Fold 5: r3prime-etale + r3prime-bc

- **Merged** with no conflicts; HolChartSerre and HolChartBC build.
- **`#discharges`** (`DischargesR3-output.txt`): 15 discharges, none by `ZInQ.R3Etale` or `ZInQ.R3BC`. That is
  expected, since R3′ was a step inside the height predicate, not a field.
- **Axioms.** `translationAnHol`, `isHolChart_iff_isSerreChart'`, `isSerreMetricSq_iff`,
  `isHolChart_iff_isBCSerreChart` and `ptsHomeomorph` all use the standard axioms.
- **Flags edited** by `scratch/fold-b112/r3prime_flags.py`. The R3′ caveat is replaced by "R3′ closed by
  r3prime-etale + r3prime-bc (…)" in:
  - `gaudronRemondSec9LowerAnSS`, which is what bost-gr9 leaves of `bostLowerBoundAnSS`;
  - `gaudronRemondThm14AnSS`;
  - `javanpeykarThm111An`.

  Each row keeps another unread or pending marker, so all three stay GLUE.
- **On-the-spot item:** `ZInQ.R3Etale.translationAnHol`. It states that left translation by a complex point is
  holomorphic for Serre's sheaf, and it is proved. It is in neither the manuscript nor its bibliography (GAGA §2 and
  SGA 1 XII are not cited). The R3′ identifications themselves (`isHolChart_iff_isSerreChart'`,
  `isHolChart_iff_isBCSerreChart`) are also on the spot, as both branches state. No other on-the-spot statement was
  added.
- **Hash guard:** 0 constants changed. Fold 5 adds no Lean module to Main's closure.

## 2. Provenance of every new statement

| statement | source | on-the-spot? |
| --- | --- | --- |
| `ZInQ.BostGR9.GaudronRemondSec9LowerAnSS` (fold-b112) | GR, Duke Math. J. 163 (2014) §9, proof of Lemme 9.1, p. 2098 (locators R21, AUDIT-READ); manuscript L894-895; over the printed semistability | no |
| `ZInQ.BostGR9.GaudronRemondSec9LowerAn` (bost-gr9, intermediate) | same print, over `IsAnStableHeight` | no |
| `SZRaynaud.SilverbergZarhinThm35` (sz-raynaud) | Silverberg–Zarhin, Ann. Inst. Fourier 45 (1995) Thm 3.5 p. 406; manuscript L816 | no |
| `Y3RouteA.Y3FullThreeRepZ30` (y3-route-a) | manuscript's own claim, L473-477 (ELLIOT) | the polarization-free reading (relative Lemma P) is on the spot, documented in the flag; nothing built on it |
| `CarayolRefold.CarayolThmAFrob` (carirr-refold) | consequence of DDT 1997 Thm 3.1 (proved implication); Carayol normalization L9784-9796 | no |
| `ZInQ.R3Etale.TranslationAnHol` (r3prime-etale, proved glue) | GAGA §2 / SGA 1 XII 1.1 (not in the bibliography) | **yes** (proved; listed as inbox 68 asks) |

## 3. Checks (VERIFIED, after each fold; outputs in scratch/fold-b112/)

- **Build:** `lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges` plus the new TailZ module (and the
  Contrib modules) succeeds. `#print axioms` of `frozenTarget` and of each new top theorem is `[propext,
  Classical.choice, Quot.sound]`.
- **Hash guard** (`cmp_fold{1,2,4a,4b,5}.txt`). Only `ZInQ.OneProof.frozenTarget` changed in folds 1-4b. Constant
  totals:
  - 18023 → 18882 (fold 1: 859 new, all in TailZ80);
  - → 18917 → 18952 → 18987 (35 new in each autofold);
  - fold 5: no change.
- **Closure** (`FoldCheck-fold*.txt`): no `sorryAx`; the removed Props are absent from the closure, or present only
  as the type of a proof; the new leaves and bundles are present. The field check shows exactly one field swapped
  per fold.
- **Other checks:**
  - OpenStatements: 30 after each fold;
  - render_open and `--check` pass;
  - DischargesTest was rerun;
  - frontier_crosswalk and `--check` pass;
  - autoform check: exit 0, 776 articles;
  - gate.sh: GATE=ok.

## 4. Manuscript check

One section per fold. The folds formalize or reroute these steps; none bypasses a manuscript step. No verdict is 'error'.

### Manuscript check (fold 1, bost-gr9)

| manuscript step | diophantine_zq.tex lines | verdict |
| --- | --- | --- |
| E4: general lower bound `h_F(Z) >= -(3/2) dim Z >= -2g`, "recorded in [gr2014, Section 9]" | L894-895 (bibitem gr2014 L11063-11066) | **OK** (correct as written, as mathematics: Bost's bound `h_F >= -(g/2) log(2 pi^2) = -1.4913.. g` implies it, proved in Lean as `gaudronRemondSec9LowerAnSS_of_bostLowerBoundAnSS`; the citation's content, an inequality inside the proof of GR Lemme 9.1 p. 2098, is AUDIT-READ only, its normalization warning unread: locator **unverified**) |
| `-(3/2) dim Z >= -2g` | L894 | OK when `dim Z <= 4g/3` (Z is a factor of the g-dimensional variety in the manuscript's use); not formalized here (the tree's R21 is `-(3/2) g <= h_F^st(A)` directly) |
| the tree's previous row (Bost, Deligne normalization, `-(g/2) log 2pi`) | not in the manuscript | replaced: it was stronger than the manuscript's citation (bost-gr9 K1) |

### Manuscript check (fold 2, sz-raynaud)

| manuscript step | diophantine_zq.tex lines | verdict |
| --- | --- | --- |
| D2: over `F = L_v(A[3])` (`A[5]` if `p = 3`), "Raynaud's criterion [silverbergzarhin, Theorem 3.5] gives semistable reduction there" | L814-817 (bibitem L11077) | **OK** (SZ Thm 3.5 as read from the page image on 11-17: `n >= 3` prime to the residue characteristic, `X_n` over an unramified extension, any discretely valued field; the manuscript's use is a direct instance). Formalized as the leaf `silverbergZarhinThm35`; the tree's field (SGA 7 IX 4.7 over a strictly henselian DVR, not in the bibliography) follows from it in Lean |
| "Its wild inertia acts trivially on each `V_ell(A)`, `ell != p`" | L817-818 | **unverified** in this fold (uncited sentence; sz-raynaud's ELLIOT leaf `ElliotWildInertiaTrivial` is not folded, since it would discharge nothing; the tree still reaches D2 through its r6 row) |

### Manuscript check (fold 4a, y3-route-a)

| manuscript step | diophantine_zq.tex lines | verdict |
| --- | --- | --- |
| A-steps: Buzzard Thm 2.1 / Cor. 2.3 at `V_1(5)` over `Z[1/30]`, full five-marking, `Isom_O(O/3O, A[3])`, free `G_5` action, quotient `X_35/G_5` and descent; "this quotient represents exactly the full-three moduli problem, so its generic fiber is `Y_3`" | L443-477 (conclusion L473-477) | **unverified** (the conclusion is taken as the ELLIOT leaf `y3FullThreeRepZ30`, the manuscript's own claim; its derivation L443-472 is not formalized, Buzzard locator UNVERIFIED). Two exposition points recorded by y3-route-a, not errors: the canonical principal polarization (L474-475) needs relative Lemma P (on the spot, not proved in the tree); "generic fiber is `Y_3`" (L476) uses the canonical-model identification, which the tree has as a separate leaf |
| generic fibre of the `Z[1/30]` model represents the problem over `Q` | L476-477 | **gap filled** (`Y3RouteA.y3RepresentableQ_of_z30`, base change of QM abelian schemes, proved) |

### Manuscript check (fold 4b, carirr-refold)

| manuscript step | diophantine_zq.tex lines | verdict |
| --- | --- | --- |
| D5: "Local-global compatibility for the weight-two modular representation therefore bounds the primitive level `N`" | L852-857 | **gap filled** (no citation in the manuscript at D5; the tree supplies Carayol 1986 Théorème (A) + Casselman 1973 through the packaged leaf `carayolThmAFrob`, a consequence of DDT 1997 Thm 3.1 (`frob_of_DDT31`); D5 needs only `v_p(N) <=` the conductor exponent, the leaf asserts equality). Leaf statement **unverified** against a page (flag "unread") |
| Carayol's normalization: arithmetic Frobenius on `rho_f` has polynomial `X^2 - a_q X + q chi(q)` | L9778, L9784-9796 (appendix, for Theorem 5.3) | **OK** as read by carirr-refold (VERIFIED by that task's reading; the leaf's Frobenius clause is in this normalization) |
| Casselman, `a(pi_{f,p}) = v_p(N)` | L9802-9806 | unverified (inside the packaged conductor clause; no Lean form of local Langlands) |
| oddness of `rho_{f,lambda}` | not in the manuscript at D5 | **gap filled** (`CarayolRefold.odd_of_frobDet`, proved from the determinant at Frobenius, one Chebotarev element) |

### Manuscript check (fold 5, r3prime-etale + r3prime-bc)

| manuscript step | diophantine_zq.tex lines | verdict |
| --- | --- | --- |
| none formalized: the manuscript uses the stable Faltings height of the literature (its archimedean metric on `A_tau(C)^an`) | L598, L872 | **OK** at the level the fold touches: R3′ shows that the tree's chart predicate `IsHolChart` gives exactly the complex structure of `A_tau(C)^an` (Serre's sheaf), so the tree's height predicate is the literature's. That identification is **on the spot** (`translationAnHol`, `isHolChart_iff_isSerreChart'`, `isHolChart_iff_isBCSerreChart`); it is not a manuscript step |

Row edits (3): no manuscript step (table text only).

## 5. Findings for the lead

1. **bost-gr9 on this base.** The field bost-gr9 targets became `bostLowerBoundAnSS` after bost-gr9's base. I folded
   the leaf over the printed semistability (`GaudronRemondSec9LowerAnSS`, new Contrib file) and not bost-gr9's
   `GaudronRemondSec9LowerAn`, which is over `IsSemistableRes`. The two differ only in the semistability clause, and
   the SS form is weaker (it implies the other). The kinds row is therefore named `gaudronRemondSec9LowerAnSS`, not
   `gaudronRemondSec9LowerAn` as inbox 59 wrote. If the lead prefers bost-gr9's exact leaf, run the generator with
   `NEWT`/`NEWF` changed and the reader without `gaudronRemondSec9LowerAn_of_ss`; that is the same bypass.
2. **Inbox 64b phrase absent.** The phrase "Berger survey IV.5.1, cited print" is not in the `bergerSurveyF` row on
   this base, so I applied the replacement to the source column's leading survey citation (section 1). Please check
   that this is the intended column text.
3. **Count-neutral folds versus the task rule.** No fold lowers the GLUE count or removes a field (section 1). The
   ratings that would move once readings land:
   - `gaudronRemondSec9LowerAnSS`: p. 2098 normalization (bost-gr9 K3);
   - `carayolThmAFrob`: statement check.
4. **Manuscript checks for lead-outbox.md.** lead-outbox.md is outside this repository (the notes repo), so the five
   Manuscript check sections are in section 4 of this report for the lead to copy.
5. **TailZ80 size.** The bypass adds 859 constants (89 copied declarations). Further folds that touch the bundles
   below `OpenResearchLeaves36EBCF` must now go through the `HDec.HSyn.GR9` copies, the way bost-gr9's own copy works.
   Generators that walk the chain by name (gen_igusa_drop-style) will see `GR9.*` names.

## 6. Files

- `ZInQKernel/Contrib/OneProof/GaudronRemondSection9SS.lean`: new, a separate commit.
- `ZInQKernel/OneProof/H/TailZ80.lean` … `TailZ83.lean`: new folds.
- `ZInQKernel/OneProof/Main.lean`: switched.
- docs/one-proof: kinds.tsv, reviews.tsv, reviews-retired.tsv, and the regenerated files.
- `scratch/fold-b112/`:
  - `log.md`, `REPLAY.md`;
  - generators `gen_gr9_fold.py`, `row_edits_64b.py`, `r3prime_flags.py`;
  - autofold specs `autofold-{sz,y3,car}.json`;
  - dry runs `*DryRun.lean.txt`;
  - `#discharges` files `Discharges*.lean` and their outputs;
  - checks `run_checks.sh`, `FoldCheck.lean`, `DumpCompact.lean`, `cmp_hashes.py`, `cmp_fold*.txt`,
    `FoldCheck-fold*.txt`, `OpenStatements-fold*.txt`, `autoform-check-fold*.txt`, `gate-fold*.txt`;
  - `GR9Closure.lean`, `gr9-closure.tsv`.

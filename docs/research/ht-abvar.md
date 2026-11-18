# ht-abvar: `hodgeTateDecompAbVar` from the manuscript's route, and the Picard rows off the proof

Task ht-abvar, 2026-11-17. Base `wip/ht-abvar` = `origin/wip/derham-scholze` (bfcab380) with `origin/main` merged
(d973b8e8d), then `origin/wip/c8-conrad2` and `origin/wip/c8-conrad3` merged for the C8/Poincaré inputs.
Results log: `scratch/ht-abvar/log.md`. This is model work; no person has reviewed it.

Labels: **VERIFIED** means compiled, computed, or read in a named file on this host. **STANDARD** means published,
with the reference given. **SPECULATIVE** means not checked. Locators given from memory are marked UNVERIFIED (no
network access).

## 0. Verdict

1. **derham-scholze's two leaves alone do not supply `hodgeTateDecompAbVar`** (VERIFIED by reading the statements,
   §2). `ScholzeDeRhamAlg` gives two things: `H¹_ét` is de Rham, and its Hodge jumps lie in `[0, 1]`
   (`Fil⁰ = D_dR`, `Fil² = 0`). `T10_TateDuality` gives the isomorphism `H¹ ≅ T_p^∨`. Neither one fixes the
   dimension of a graded piece, so the multiplicities `(a, b)` with `a + b = 2g` stay open. Those leaves yield
   `hodgeTateDecompOr` (some `(a, b)`), and nothing more.
2. **The smallest reroute is the manuscript's own, and it is done.** `lem:de-rham-descent` reads the weights off
   the Hodge numbers (diophantine_zq.tex L10996-10997: "The two Hodge numbers of `H¹_dR(A/F)` are `2,2`.
   Consequently the Tate module has weights `0,0,−1,−1`"). One new leaf states that sentence on the étale side of
   Scholze's filtered comparison:

   ```lean
   def DeRhamScholze.HTAbVar.HodgeNumberH1AbVar : Prop :=
     ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
       (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
       finrank ℚ_[p] (filD p (F := F) (rhoH A.X p 1) 1) = finrank ℚ_[p] F * g
   ```

   Everything else is proved in Lean, with the standard axioms (VERIFIED):

   ```lean
   theorem DeRhamScholze.HTAbVar.hodgeTateDecompAbVar_of_scholze (hS : ScholzeDeRhamAlg)
       (hT : T10Etale.T10_TateDuality) (hH : HodgeNumberH1AbVar) : ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
   ```

   The field's type is copied verbatim and checked with `Iff.rfl` against `TailS.lean` L347. The proof uses no
   Picard scheme, no dual abelian variety and no Weil pairing.
3. **The Picard rows leave the route** (VERIFIED, compiled dry run, §5). On top of c8-conrad2/c8-conrad3's copy
   reroute of consumers (i) C8 and (ii) Poincaré, consumer (iii) now reads this theorem. The dry-run top is
   `HDec.HSyn.sixContactMin_of_open73HT (r : OpenResearchLeaves53) (t : OpenTextbookLeaves19HT)
   (l : OpenAddedLeaves28HT)`, and it gives `ZInQ.OneProof.frozenTarget_ht` with the standard axioms. None of its
   hypotheses carries `picRepresentableAbVar` or `kleimanPicZeroProper954SiteQ`. A field-taint run from
   `frozenTarget_ht` finds no reader of either row. The research field `hodgeTateDecompOr` also leaves the route:
   its only flow goes into a field that the rerouted map ignores.
4. **Net change: the target "net GLUE ≤ 0" is not met.** On the kinds.tsv H rows the count goes from 5/24 on 29 to
   5/27 on 32, so GLUE rises by 3. Consumer (iii) accounts for +2 of that: `hodgeTateDecompOr` leaves, while
   `scholzeDeRhamAlg`, `t10TateDuality` and `hodgeNumberH1AbVar` enter. Consumers (i)+(ii) account for +1: two
   Picard rows leave, three C8/Poincaré leaves enter. **What blocks net GLUE ≤ 0** is precise (§6). Mathlib has no
   `H¹_dR` and no rigid-analytic spaces, so Scholze's comparison and the Hodge numbers can only be stated as
   *consequence* leaves, and autofold counts every consequence leaf as GLUE however it is read. The best case for
   (iii) is +1: merge the two consequence leaves into one abelian-variety leaf, and have Milne read so it counts
   LEAF.

## 1. The field and its current route (VERIFIED by reading the tree)

* **Field.** `hodgeTateDecompAbVar : ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar` (`ZInQKernel/OneProof/H/TailS.lean`
  L347). For every prime `p`, every finite `F/ℚ_p`, every `A : PkgI4.I3.AbVar F` and every `g` with `A.dim = g`,
  there is a `ℂ_p`-linear `e : ℂ_p ⊗_{ℚ_p} V_p(A) ≅ ℂ_p^g × ℂ_p^g` carrying `σ ⊗ ρ(σ)` to
  `(χ(σ)·σ, σ)` coordinatewise, i.e. `ℂ_p(1)^g ⊕ ℂ_p^g`.
* **Filled at** TailZ74 L381 (`openResearchLeaves35_of_OpenResearchLeaves36_eb_k954_cf`) by
  `hodgeTateDecompAbVar_of_open_k954 n.hodgeTateDecompExists t.mumfordTorsionAlgClosed l.picRepresentableAbVar
  l.kleimanPicZeroProper954` (TailZ69 L55):
  * `(a, b)` comes from `HodgeTateDecompExists`;
  * `a = b` comes from the Weil pairing of a symmetric isogeny `A → A^∨` (`t09SymmIsogenyExists0_of_open_k954`,
    built from the two Picard rows);
  * `a + b = 2g`.
* `n.hodgeTateDecompExists` comes from the open research field `hodgeTateDecompOr`
  (TailZ79, in `openResearchLeaves36EBCF_of_OpenResearchLeaves53`: `hodgeTateDecompExists := hodgeTateDecompExists_of_or n.hodgeTateDecompOr`). Its only live reader is
  the line above; EichlerBoundCopy L3795 and TailZ60 L71 belong to older generations that are not on the route.
* **Consumers.** `hodgeTateDecompAbVar` → `r10` (R10, the de Rham comparison with weights `0, −1` of multiplicity
  `g`), read by G9 (C3) and G11. This is consumer (iii) of c8-conrad §2.

## 2. Why `ScholzeDeRhamAlg` + `T10_TateDuality` are not enough

* `ScholzeDeRhamAlg` (DeRhamScholze.lean §3) says: `IsDeRhamFam` (`dim D_dR = [F:ℚ_p] dim W`) and
  `HodgeRange … i` (`Fil⁰ D_dR = D_dR`, `Fil^{i+1} D_dR = 0`).
* `T10_TateDuality` is an equivariant isomorphism.
* From these, derham-scholze's `DeRhamHodgeTate01` produces `Hom(V, ℂ_p) ≅ ℂ_p^a ⊕ ℂ_p(−1)^b` with
  `a = dim_{F} Hom_{G_F}(V, ℂ_p)`, `b = dim_F Hom_{G_F}(V, ℂ_p(1))` and `a + b = dim V`, and nothing pins `b`.
* Fontaine's `gr D_dR ≅ D_HT` turns `b` into `dim_F Fil¹ D_dR(V^∨)`, so a value of `b` needs a dimension of
  `Fil¹`. This is exactly the manuscript's input "the two Hodge numbers of `H¹_dR(A/F)` are `2,2`" (L10996). No
  statement in the two leaves mentions a dimension of `Fil¹`.

## 3. The reroute: one leaf, the rest in Lean

### 3.1 The leaf `HodgeNumberH1AbVar` (rating: consequence, not printed form)

* **What it says.** For an abelian variety `A` of dimension `g` over a finite `F/ℚ_p`,
  `dim_{ℚ_p} Fil¹ D_dR(H¹_ét(A_{F̄}, ℚ_p)) = [F:ℚ_p]·g`. Here `D_dR`, `Fil^j` and `H¹_ét` are exactly the objects of
  derham-scholze's `ScholzeDeRhamAlg`:
  * `H¹_ét` is Mathlib's pro-étale `EllAdicCohomology` tensored with `ℚ_p` (`HQ`, `rhoH`);
  * `Fil^j D_dR = D_dR ∩ (t^j B_dR^+ ⊗ W)` (`filD`).
* **Where it comes from.**
  * **ELLIOT.** L10996 states the Hodge numbers `2,2` of `H¹_dR(A/F)` for the abelian surface and cites nothing.
  * **CITED.** The filtered comparison `D_dR(H¹_ét) ≅ H¹_dR(A/F)` is Scholze, Forum Math. Pi 1 (2013), Cor. 1.8
    with Thms 9.1, 9.3: cited at L736-737, applied at L10953-10965, and L10958-10959 says Thm 9.1 identifies "the
    filtered de Rham hypercohomology".
  * Under it, `Fil¹ H¹_dR = H⁰(A, Ω¹)` (Hodge–de Rham degeneration) has dimension `h^{1,0} = g`. STANDARD; for
    example `Ω¹_A ≅ 𝒪_A^g`, Mumford, *Abelian varieties*, §4 (locator UNVERIFIED).
* **Why consequence and not printed form.**
  * (a) `H¹_dR` is not in Mathlib, so the Hodge number is stated on the étale side of the comparison, as
    derham-scholze did for the jump clause.
  * (b) The leaf states only `h^{1,0}`, which is weaker than "`2,2`". `gr⁰` then follows from de Rham.
  * (c) The manuscript has `g = 2`; the field and the leaf are for every `g`, with the same standard fact.

  The leaf says nothing beyond the print plus these dictionary steps. It is not a disguised form of the
  conclusion: the step from `dim Fil¹` to the Hodge–Tate multiplicities (Fontaine's `gr D_dR ≅ D_HT`, the
  manuscript's "Consequently", L10997) is proved in Lean (§3.2).

### 3.2 The glue proved in Lean (VERIFIED, standard axioms)

The Lean is split into two files, `HTAbVarScholzeDims.lean` (imports `DeRhamScholzeHT`) and
`HTAbVarScholze.lean` (imports Dims and `DeRhamScholzeT`).

| declaration | statement |
|---|---|
| `finrank_fil1_bounds` | Jumps in `[0,1]` give two bounds. First, `dim(D_dR ∩ Fil¹) ≤ dim Hom_{G_F}(V, ℂ_p(1))`: `gr¹` is injective because `Fil² = 0`. Second, `dim D_dR ≤ dim Hom_{G_F}(V, ℂ_p) + dim(D_dR ∩ Fil¹)`: `ker gr⁰ ⊆ Fil¹`. Both use derham-scholze's `gr0`, `gr1`, `gr1_mem`, `mem_filH1_of_gr0`, `mem_filH2_of_gr1`. |
| `hom_decomp_of_basis` | the coordinate isomorphism of the Tate–Sen basis is `G_F`-equivariant (the last step of `deRhamHodgeTate01_of_fontaineT`, for given bases) |
| `hodgeTate01_dims` | De Rham, jumps in `[0,1]` and `dim Fil¹ D_dR(V^∨) = [F:ℚ_p]·h` give a Hom-form decomposition `ℂ_p^a ⊕ ℂ_p(−1)^b` with `a + h = dim V` and `b = h`. Proof: `h ≤ b`, `dim V ≤ a + h`, and Tate–Sen (`linIndep_two`) gives `a + b ≤ dim V`. |
| `finrank_filD_dual` | `Fil¹` moves from `H¹_ét` to `V_p(A)^∨` along Milne's identification (`milneE`, `map_filD`) |
| `hodgeTateDecompAbVar_of_scholze` | **the field**. It uses `dim V_p(A) = 2g` (`finrank_V_of_tateModuleFree`, Mumford's torsion theorem proved in the tree), `hodgeTate01_dims` with `h = g`, and htdecomp-or's `dualEquiv` / `dualEquiv_map` (Hom form → tensor form, `(b, a) = (g, g)`). |

Engineering note (VERIFIED). In the environment of `DeRhamScholzeT` the instance search for
`StrongRankCondition ℚ_[p]` times out (in `isDefEq`), and `rw [Module.finrank_eq_rank]` on a let-bound submodule
ran for over ten minutes. This is the pitfall HodgeTatePairingDecomp's header warns about. The fix was to put the
dimension count in its own file that imports only `DeRhamScholzeHT`, and to prove the linear algebra as separate
lemmas in clean contexts.

### 3.3 Leaf tags (with line evidence)

| leaf | tag | evidence | rating |
|---|---|---|---|
| `hodgeNumberH1AbVar` (new) | **ELLIOT** (Hodge numbers, uncited) through **CITED** (Scholze filtered comparison) | L10996 (Hodge numbers), L10958-10959 (filtered de Rham via Thm 9.1), L736-737 (`\cite{scholze2013,scholze-erratum}`), bibitem L11010 | consequence, not printed form (§3.1) |
| `scholzeDeRhamAlg` (derham-scholze, reused) | **CITED** | L10955-10965, bibitem L11010, L11015 | consequence (derham-scholze §3.1) |
| `t10TateDuality` (t10-etale, reused) | **CITED** | L10966-10970 `\cite[Part I, Theorem 12.1(a)]{milne-av}`, bibitem L11024 | printed form with dictionary, unread (derham-scholze §3.2) |
| `conradAppBQp`, `tateTwistInvariantsInertia`, `poincareComplement` (c8-conrad3's handfold, reused) | CITED (L761) / DEPARTURE / ELLIOT (L865) | c8-conrad3 report | as rated there |

### 3.4 Faltings 1988 III Thm 4.1: CITED-as-remark, not used

* **What the manuscript does with it.** Faltings, JAMS 1 (1988), 255-299, is in the bibliography (L11087). It is
  cited once, at L11003-11006, to say that the Hodge–Tate comparison of Ch. III Thm 4.1 *alone would not prove the
  de Rham assertion*, and that the lemma uses the de Rham comparison instead. Tag: **CITED-as-remark**.
* **Would it fit as the supplier of the multiplicities? No:**
  1. It does not match the manuscript's use. The manuscript takes the multiplicities from the Hodge numbers
     through the *de Rham* comparison (L10996-10997), and the Faltings sentence is a remark, not a supply. The
     remark itself would not be violated, since using HT for the multiplicities is not inferring de Rham from HT.
     Still, supplying the step from a remark citation is a DEPARTURE in use.
  2. It does not save anything. Its decomposition `ℂ_p ⊗ H¹_ét ≅ (ℂ_p ⊗ H¹(A, 𝒪_A)) ⊕ (ℂ_p(−1) ⊗ H⁰(A, Ω¹))` (the
     theorem's content from memory, UNVERIFIED) gives the multiplicities as `h^{0,1}, h^{1,0}`. These still have
     to be shown equal to `g`: `h^{0,1} = g` is Mumford §13, UNVERIFIED. It also needs coherent cohomology and
     Kähler differentials of a scheme as Lean statements. That would be a larger new route.

  So it was not used.

## 4. Lean files, compile log, `#discharges`

| check | outcome (all 11-17, Lean 4.35.0 / Mathlib v4.35.0) |
|---|---|
| `lake build ZInQKernel.Contrib.OneProof.HTAbVarScholze` | built (12340 jobs) |
| `scratch/ht-abvar/Axioms.lean` (`axioms-output.txt`) | the verbatim copy of `HodgeTateDecompAbVar` is `Iff.rfl` with TailS's; `hodgeTateDecompAbVar_of_scholze`, `hodgeTate01_dims`, `finrank_fil1_bounds`: `[propext, Classical.choice, Quot.sound]` |
| `scratch/ht-abvar/Discharges.lean` (`discharges_out.txt`) | `#discharges: 34 open hypotheses, 16518 theorems checked, 25 discharge one`; none by `DeRhamScholze.HTAbVar.*`, as expected (`hodgeTateDecompAbVar` is not an open field); the five new theorems: standard axioms |
| `scratch/ht-abvar/HTDryRun.lean` (`dryrun_out.txt`) | compiles; `frozenTarget_ht`, `sixContactMin_of_open73HT`, `sixContactMin_of_open72_ht`: standard axioms |
| `scratch/ht-abvar/HTDryRunTaint.lean` (`dryrun_taint_out.txt`) | closure 304201; seeds `picRepresentableAbVar`, `kleimanPicZeroProper954SiteQ`, `hodgeTateDecompOr`; one edge (`openResearchLeaves36EBCF_of_OpenResearchLeaves53 : hodgeTateDecompExists ← hodgeTateDecompOr`), no terminal consumer |

Files. None has `sorry` or `#eval`/`run_cmd`, and neither imports `ZInQKernel.OneProof.Main`:
* `ZInQKernel/Contrib/OneProof/HTAbVarScholzeDims.lean`
* `ZInQKernel/Contrib/OneProof/HTAbVarScholze.lean`

Scratch copies are in `scratch/ht-abvar/`.

## 5. Dry run: the Picard rows off all three consumers

* **Body.** c8-conrad2's generated copy (`scratch/c8-conrad2/C8DryRun.lean` up to its handwritten top), verbatim.
  It is identical to the body of c8-conrad3's `C8FoldDryRun.lean` (diff empty). This copy reroutes:
  * (i) C8 to `C8Conrad.g12DetPZ_of_inputs`, here fed by c8-conrad3's `C8Leaves`;
  * (ii) Poincaré to the textbook leaf.
* **Top** (`scratch/ht-abvar/gen/`):
  * `openResearchLeaves35_of_OpenResearchLeaves36_eb_k954_cf_ht`: TailZ74 L378 verbatim except for
    `hodgeTateDecompAbVar := hHT`, and without the arguments `t`, `l`;
  * `openAddedLeaves18_ht` and `sixContactMin_of_open45_pz_eb_ht`: c8-conrad2's versions without the added bundle
    they never read;
  * `sixContactMin_of_open72_ht`: a copy of the current top `sixContactMin_of_open72` with the three swaps;
  * hand-fold shape: `OpenTextbookLeaves19HT = {poincareComplement}`, `OpenAddedLeaves28HT = {conradAppBQp,
    tateTwistInvariantsInertia, scholzeDeRhamAlg, t10TateDuality, hodgeNumberH1AbVar}`, and
    `sixContactMin_of_open73HT` with `frozenTarget_ht`.
* **Result.**
  * No hypothesis of `frozenTarget_ht` mentions a Picard row. It does not take `OpenAddedLeaves27`, and
    `OpenResearchLeaves53` has none of its 27 fields.
  * The taint run confirms nothing reads them.
  * `hodgeTateDecompOr` is passed only into `OpenResearchLeaves36EBCF.hodgeTateDecompExists`, which the rerouted
    map ignores, so the fold removes that research row too.
* **Count** (kinds.tsv H rows, autofold's rule: a consequence or unread row is GLUE):

| | rows | LEAF/GLUE |
|---|---|---|
| current top | 29 | 5/24 |
| remove `picRepresentableAbVar`, `kleimanPicZeroProper954SiteQ`, `hodgeTateDecompOr` | −3 | −0/−3 |
| add `poincareComplement`, `conradAppBQp`, `tateTwistInvariantsInertia` (c8-conrad3) | +3 | +0/+3 |
| add `scholzeDeRhamAlg`, `t10TateDuality`, `hodgeNumberH1AbVar` (this task) | +3 | +0/+3 |
| after | 32 | 5/27 |

Net GLUE: +3, of which consumer (iii) accounts for +2. If PR #86's native `poincareComplement_proof` lands
(c8-conrad3), the net is +2. The hand-fold spec is `scratch/ht-abvar/autofold.json`: `discharges: []` (no open
field is discharged), plus a `handfold` section with the (iii) swap and `new_leaves` with kind, class and flag. A
fold needs `--allow-rise` or a ruling.

## 6. What blocks net GLUE ≤ 0 (precise)

* For (iii), the route needs three inputs that cannot be proved in Lean today:
  * Scholze's comparison: rigid-analytic in print, stated algebraically here;
  * Milne's identification;
  * the Hodge number `h^{1,0} = g`.
* `H¹_dR` is not in Mathlib, so Scholze and the Hodge number can only enter as **consequence** leaves. Autofold
  counts a consequence leaf as GLUE however it is read (`strict = LEAF` only for `kind = published` with no unread
  marker). These replace the single GLUE row `hodgeTateDecompOr` and add +2.
* Two ways to bring (iii) down to +1, neither done here:
  * (a) merge `scholzeDeRhamAlg` and `hodgeNumberH1AbVar` into one abelian-variety leaf ("`H¹_ét(A)` is de Rham with
    `Fil⁰ = D_dR`, `Fil² = 0`, `dim Fil¹ = [F:ℚ_p] g`"). This saves a row but mixes a cited print with an uncited
    fact;
  * (b) have Milne Thm 12.1(a) read, so `t10TateDuality` becomes LEAF.
* (iii) reaches 0 only if Mathlib gains algebraic de Rham cohomology. The Hodge numbers could then be a printed
  leaf (`dim H⁰(A, Ω¹) = g`) and Scholze's filtered comparison could be stated with `H_dR`.
* The Picard rows themselves cannot leave without (iii): every consumer had to be rerouted, and (i)/(ii) cost +1
  net (c8-conrad3).

## 7. Known issues

1. **The premise of task part (2) does not hold.** `ScholzeDeRhamAlg` + `T10_TateDuality` do not determine the
   multiplicities (§2). Neither statement is false, vacuous or inert; they are insufficient, and the manuscript's
   own extra input (the Hodge numbers, L10996) is the missing piece.
2. **The manuscript states the Hodge numbers only for `g = 2` and cites nothing** (L10996, ELLIOT). The field is
   for every `g`. The general statement `h^{1,0}(A) = g` is standard (Mumford §4, UNVERIFIED locator), so this is
   no defect of the manuscript, but the leaf goes beyond the literal sentence in `g`.
3. **No `H_dR` in Mathlib** (as derham-scholze Known issue 1). The Hodge number is stated through Scholze's
   filtered comparison on the étale side. It inherits derham-scholze's dictionary steps: analytification, `F̄`
   versus `ℂ_p`, pro-étale versus étale.
4. **Faltings 1988 III.4.1 is cited only as a remark** (L11003-11006). It is not used (§3.4).
5. No known issue with Scholze's Cor. 1.8 or Milne's Thm 12.1(a) as the manuscript uses them. Neither was re-read
   here; their locators stand as in derham-scholze §3.

## 8. On-the-spot steps (neither in the manuscript nor in a cited print), all proved in Lean

* **Fontaine's `gr D_dR ≅ D_HT` with dimensions** (`hodgeTate01_dims`), behind the manuscript's "Consequently"
  (L10997). Sketch: `gr¹ : D_dR ∩ Fil¹ → Hom_{G_F}(V, ℂ_p(1))` is injective (its kernel is `Fil² = 0`), so
  `h ≤ b`. `gr⁰ : D_dR → Hom_{G_F}(V, ℂ_p)` has kernel inside `Fil¹`, so `dim V ≤ a + h`. Tate–Sen
  (`F'`-independent invariant vectors of weights `0`, `1` are `ℂ_p`-independent, from Tate's two theorems) gives
  `a + b ≤ dim V`. Hence `b = h` and `a = dim V − h`. It is derham-scholze's argument with the inequalities
  sharpened to equalities.
* **The transport of `Fil¹` along Milne's identification** (`finrank_filD_dual`): linear algebra
  (derham-scholze's `map_filD`).
* **Hom form → tensor form** (htdecomp-or's `dualEquiv`, already in the tree).

## 9. What remains

* The fold itself (integrator): c8-conrad3's handfold plus the (iii) swap of `scratch/ht-abvar/autofold.json`.
  It removes three rows and adds six, and needs `--allow-rise` or a ruling (§5, §6).
* Readings: Milne Thm 12.1(a) (for `t10TateDuality`), and a locator for `h^{1,0}(A) = g`.
* Optional: the merged single leaf of §6(a), if the integrator prefers the count over the separation of sources.
* Not needed by the field: the descent and coefficient parts of `lem:de-rham-descent`.

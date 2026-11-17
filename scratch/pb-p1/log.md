# pb-p1 results log

## Setup (2026-11-17 04:24-04:45 PST)

- Base: origin/wip/pb-pst cad410ec; origin/main 5c7d9ba7 was not an ancestor. Direct merge of origin/main conflicted
  on generated docs only (STATUS.md, docs/one-proof/*); aborted and merged origin/wip/leaf-fold33b 56b6353d instead
  (it already contains origin/main 5c7d9ba7 with those conflicts resolved): merge 8702090d, origin/main now an
  ancestor (VERIFIED `git merge-base --is-ancestor`). Current top: TailZ71.
- Build cache: rsync of ~/dzq-wt/pb-pst/.lake/build; `lake build +ZInQKernel.Contrib.OneProof.PanBergerPst`
  succeeded (10668 jobs, build1.txt).

## Prints read (arXiv, fetched 2026-11-17 with WebFetch, text extracted with pdftotext; downloads deleted after use)

- Berger, math/0102179v3 (Invent. Math. 148 (2002)), §1.2 p. 10-11 (VERIFIED, read):
  - p. 10: `B_max^+ = {Σ a_n ω^n/p^n : a_n ∈ B̃^+ a sequence tending to 0}`, `B_max = B_max^+[1/t]`; "on peut remplacer ω
    par n'importe quel générateur de ker(θ), par exemple [p̃] − p"; crystalline = `B_max`-admissible.
  - p. 11: `log[π̄]` is defined as the limit in `B_dR^+` of "the series defining `log(π̄^(0)) + log([π̄]/π̄^(0))`
    (after choosing `log(p)`, `π̄ = ε − 1`)"; `B_st = B_max[log[π̄]]`; semistable = `B_st`-admissible;
    "La définition de B_st donnée ci-dessus est légèrement différente de celle de Fontaine, mais le foncteur D_st
    est le même." (p. 11).
  - Prop. 2.23, p. 23-24 (proof): `log[x] = Σ (−1)^{n−1}([x]−1)^n/n` for `v_p(x^(0) − 1) > 1` converges in
    `B_max^+`; extended to `x^{p^n} ∈ U_1`, to `(Ẽ^+)^* = k^* (1 + m)` with `log = 0` on `k`, then by valuation.
  - FINDING (VERIFIED by reading): the §1.2 formula is not literal in `B_dR^+`: it divides by
    `π̄^(0) ∈ 𝓞_ℂ_p`, and `ℂ_p` is not a subring of `B_dR^+` (only `ℚ̄_p` is, by Hensel). Any Lean definition of
    Berger's `log[π̄]` needs the `p`-adic logarithm of Prop. 2.23's proof (series converging in `B_max^+`).
- Berger, math/0210184v1, *An introduction to the theory of p-adic representations* (Geometric aspects of Dwork
  theory, de Gruyter 2004; journal data UNVERIFIED) (VERIFIED, read):
  - I.2.3 p. 6: `D_B(V) = (B ⊗_{ℚ_p} V)^{G_K}`; "V is B-admissible if [dim_{B^{G_K}} D_B(V) = d], which is
    equivalent to having B ⊗_{ℚ_p} V ≃ B^d as B[G_K]-modules" (for `G_K`-regular `B`).
  - II.2.2 p. 11: `ω = ([ε] − 1)/([ε_1] − 1)`, `ker θ = (ω)` (with proof).
  - II.2.3 p. 11-12: `B_dR^+`, `t = −Σ (1 − [ε])^n/n`, de Rham = `dim_K D_dR(V) = d`.
  - II.3.1 p. 13: `B_cris^+ = {x ∈ B_dR^+ : x = Σ x_n ω^n/n!, x_n → 0 in B̃^+}`, `B_cris = B_cris^+[1/t]`.
  - II.3.3 p. 14-15: `B_st = B_cris[Y]`, embedded in `B_dR` by `Y ↦ log[p̃] = log_p(p) − Σ (1 − [p̃]/p)^n/n`
    (`p̃^(0) = p`), "It is customary to choose log_p(p) = 0 which is what we'll always assume from now on."
  - II.3.5 p. 16: `B_max^+ = {Σ x_n ω^n/p^n}`; crystalline periods lie in `∩ φ^n B_cris^+[1/t] = ∩ φ^n B_max^+[1/t]`.
  - II.5.2 p. 19-20: potentially semistable = semistable on `G_L` for a finite `L/K`.
  - IV.5.1 p. 30: "every de Rham representation is potentially semi-stable. We shall now give a proof of that
    statement."; IV.5.3 p. 31: the proof ("Let V be a de Rham representation ... V is potentially semi-stable").
- Pan, arXiv 1901.07166v2: Conj. 1.0.1 p. 2 ("potentially semi-stable in the sense of Fontaine"); Thm 1.0.4 p. 5
  ("Let p be an odd prime and ρ be as in conjecture 1.0.1") (VERIFIED, read).
- Berger, math/0406601v1 (Astérisque 319): §V.3 p. 25 writes Fontaine's `B_st = B_cris[log[π̄], 1/t]` and
  `D_st(V) = (B̃_rig^+[log[π̄], 1/t] ⊗ V)^{G_K}` (VERIFIED, read; not used).

## Route decision

- Fontaine's ring is printed concretely in Berger 2004 (II.3.1, II.3.3) with `log[p̃]` (log p = 0), which is the
  tree's `logPTilde`. Berger 2004 prints Berger's theorem over it (IV.5.1, IV.5.3). Pan uses Fontaine's sense.
  So both leaves can be stated over the same printed ring; then `r11r12 : PanBerger` (de Rham hypothesis) needs no
  comparison between rings at all.
- B1 (Berger's `B_max[log[π̄]] = B_max[log[p̃]]`) is then not needed for either leaf; it is not formalized (see
  FINDING above; it needs a `p`-adic logarithm on `A_max`, which the tree lacks).

## Lean (all VERIFIED: compiled with `lake env lean` / `lake build`, standard axioms)

- `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges`: 16093 jobs, success (build2.txt).
- scratch/pb-p1/FontaineSt.lean (→ ZInQKernel/Contrib/OneProof/PanBergerFontaine.lean via mkcontrib.py): compiles
  (13 s); `lake build +ZInQKernel.Contrib.OneProof.PanBergerFontaine` success (build3.txt).
  - Fontaine's rings per Berger 2004: AcrisOf, BcrisPlusOf, BcrisOf, BstFOf; bcrisPlusOf_eq_set (B_cris^+ = printed
    set p^-k A_cris; acrisOf_mul via dpSeries_mul), acrisOf_eq (generator independence), acrisOf_le_amax
    (p^n/n! ∈ Z_p), bstFOf_le (B_st^F ⊆ tree's B_st), logTeich_mem_acris, bstF_stable, isAdmissibleT_mono,
    isAdmissible_of_pstF, bmax_adjoin_eq_bst (B1 algebraic half).
  - Leaves BergerSurveyF, PanPrintedF; bergerPrintedV_of_survey : BergerSurveyF → BergerPrintedV;
    panBerger_of_F : PanPrintedF → BergerSurveyF → DS fields → PanBerger; panPrintedP_of_F (needs the non-leaf
    BmaxStToFontaine; not in any fold).
- Axioms.lean: 19 declarations, all [propext, Classical.choice, Quot.sound] (axioms-output.txt).
- Discharges.lean: bergerPrintedV by bergerPrintedV_of_survey (assumes BergerSurveyF); panPrintedP by
  panPrintedP_of_F (assumes PanPrintedF, BmaxStToFontaine); 39 open, 14150 theorems, 34 discharge one.
- autofold.json (bergerPrintedV -> bergerSurveyF) dry run: strict 5/29 on 34 -> 5/29 on 34; output compiles
  (folddryrun-output.txt).
- BypassFold.lean (gen_bypass.py; PBP1 copies of research generations 40..45, r11r12 := panBerger_of_F):
  PBP1.sixContactMin_of_open65 compiles, standard axioms (bypass-out.txt).
- scan_contrib.py 56b6353d5 HEAD: PanBergerFontaine.lean 0 likely, 0 possible hits.

## Open

- B1 analytic half (Lean definition of Berger's log[π̄]): not formalized; on-the-spot sketch in the report §4.
- BmaxStToFontaine (tree-ring pst ⇒ Fontaine pst): not a leaf, not proved; avoided by the bypass fold.

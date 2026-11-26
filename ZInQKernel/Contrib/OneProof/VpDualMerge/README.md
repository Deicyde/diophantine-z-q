# vpdual-merge

Glue for a later fold that replaces the added-bundle rows `scholzeH1AbVar`
(`DeRhamScholze.HTMerge.ScholzeH1AbVar`) and `t10TateDuality` (`T10Etale.T10_TateDuality`) of
`ZInQ.OneProof.frozenTarget` by two single-print rows on `V_p(A)` (in progress, in a separate lane).

Both current rows are read on the live route only through one statement about the dual Tate module,
`DeRhamScholze.HTMerge.VpDualDeRhamAbVar`: `V_p(A)^∨` is de Rham, its Hodge jumps lie in `[0, 1]`,
and `dim_{ℚ_p} Fil¹ D_dR = [F:ℚ_p] · g`. Under the owner's ruling (each row is one printed theorem,
with the glue derived in Lean), this statement is **not a row**. It is a derived `Prop`: the
single-print rows are to imply it in Lean, and this directory carries everything above it, namely
the conversions to the three `HTMerge` outputs and a copy of the live chain whose added bundle has
the one field `vpDual` in place of the pair. The current pair implies the statement
(`vpDual_of_pair`), so nothing here is stronger than `main`.

This PR is add-only and changes no count. It claims no row. Draft PR #204 (`t10TateDuality` via
Milne 1986) touches the same row; the later fold settles how the two fit together.

Base: `main` at `c05342735cf71fe001e0dcf8c617743f62d135ba` (the run also built on top of
`e9956cda`, which only adds `CasselsTatePS`).

## Files

* `Row.lean`: the statement and its conversions, in `DeRhamScholze.HTMerge` (the file name
  predates the owner's ruling; `VpDualDeRhamAbVar` is not a row).
  * `VpDualDeRhamAbVar`, with its three clauses `VpDualIsDeRham`, `VpDualHodgeRange`,
    `VpDualFilOneDim` (each with its sources); `vpDualDeRhamAbVar_iff` unfolds them (`Iff.rfl`).
    `V_p(A) = ℚ_p ⊗ T_p(A)` is `A.V p` with `A.galRep p`, built from the `F̄`-points of `A`.
  * `vpDual_of_pair : ScholzeH1AbVar → T10_TateDuality → VpDualDeRhamAbVar`, through the existing
    `HTMerge.dual_of_H1` (with `mumfordTorsionAlgClosed_proof`).
  * The three outputs of the `HTMerge` theorems from the statement alone:
    `deRhamVpAbVarDirect_of_vpDual`, `hodgeTateDecompOr_of_vpDual` (through
    `hodgeTateDecompHom_of_vpDual`) and `hodgeTateDecompAbVar_of_vpDual` (through
    `htDecomp_of_vpDual`).
* `Chain.lean`: the generated copy reroute (below), new top
  `HDec.HSyn.sixContactMin_of_open98_vp (r : OpenResearchLeaves78) (t : OpenTextbookLeaves18)
  (l : OpenAddedLeaves29VP)`.
* `gen_vp.txt`: the generator (a Python script, shipped as text because the scope gate admits no
  `.py`): `python3 gen_vp.txt REPO_ROOT OUT_DIR [AUDIT_FILE]`. It reads named files only.
* `FoldCheck.lean`: `addedLeaves29VP_ofLive`, a fully qualified `example`,
  `frozenTarget_with_vpDual` (`frozenTarget`'s body verbatim with only the top swapped), and
  `#print axioms` for every new theorem.

## Where the two fields are read

On the live route (`sixContactMin_of_open98` → `DS965Reroute/Chain5`…`Chain3`), the pair is read
in three places, each passing both fields together into one `HTMerge` theorem:

| Declaration (live copy) | File | Reader |
|---|---|---|
| `openResearchLeaves60_y3x6_of_OpenResearchLeaves63_nos_ds` | `DS965Reroute/Chain3.lean` L1666 | `hodgeTateDecompOr_of_scholzeH1Milne` |
| `sixContactMin_of_open82_nos_ds` | `DS965Reroute/Chain3.lean` L1711 | `hodgeTateDecompAbVar_of_scholzeH1` |
| `openResearchLeaves65_of_OpenResearchLeaves66_ds` | `DS965Reroute/Chain4.lean` L520 | `deRhamVpAbVarDirect_of_scholzeH1Milne` |

Everything else on the route only passes the bundle on (`sixContactMin_of_open83_nos_ds`, the
copies of `TailZ91`–`TailZ103` in `Chain4`/`Chain5`, `openAddedLeaves28_of_OpenAddedLeaves29`,
`sixContactMin_of_open98`) or reads `conradAppB` (`c8Leaves_of_OpenAddedLeaves28`).

Checked by reading named files, and found off the live route:

* `TailZ87` L94/L120, `TailZ88` L91/L122, `TailZ89` L90/L122, `TailZ92` L76: the originals of the
  conversions above. The live route uses their copies (`NOSNarrowChain` → `DS965Reroute`).
* `NOSNarrowChain.lean` L4691/L4728: the originals of the two `Chain3` readers.
* `C8Chain.lean` L1427/L1439 (`sixContactMin_of_open72_sf_u_hm`, `sixContactMin_of_open79_hm`)
  and `CMR5.lean` L1049/L1074/L1087 (`…_hm_cm_r5`, `sixContactMin_of_open80_cm_r5`) take
  `(hN : ScholzeH1AbVar) (hT : T10_TateDuality)`. They feed the superseded tops
  (`sixContactMin_of_open80`, `…_open80_cm_r5` and the generations above them), not the live top,
  whose declarations take no such argument.
* No mention of either field or row in `TailZ90`, `TailZ93`–`TailZ105` (apart from forwarding
  `OpenAddedLeaves28`/`29`), `Y3Copy1`–`Y3Copy6`, `D2A6Chain`, `CMOpen`, `NOSNarrow`,
  `NOSNarrowNC`, `CMCurveOrderLiveNOS`, `DS965Reroute/Chain1`, `Chain2`.

The check does not depend on this list alone. The generator stops if a copied declaration still
names either field or row after the edits. The new bundles lack the two fields, so Lean rejects any
reader of them that was not switched, and any uncopied declaration that is handed the new bundle.

## The copy reroute (`Chain.lean`, generated)

Generated from `TailZ87` (`OpenAddedLeaves28`, `c8Leaves_of_OpenAddedLeaves28`),
`DS965Reroute/Chain3`–`Chain5` (every declaration that the taint from `OpenAddedLeaves28` reaches),
`TailZ104` (`OpenAddedLeaves29`, `openAddedLeaves28_of_OpenAddedLeaves29`) and `TailZ105`
(`sixContactMin_of_open98`). The suffix is `VP` for structures and `_vp` for theorems. 22
declarations:

* `OpenAddedLeaves28VP` = `{conradAppB, vpDual}`, `OpenAddedLeaves29VP` = `{vpDual}`: the pair is
  replaced by `vpDual : DeRhamScholze.HTMerge.VpDualDeRhamAbVar`;
  `openAddedLeaves28_of_OpenAddedLeaves29_vp`: `vpDual := n.vpDual`.
* Readers: `HTMerge.<out>_of_scholzeH1[Milne] l.scholzeH1AbVar l.t10TateDuality` →
  `HTMerge.<out>_of_vpDual l.vpDual` (the three rows of the table above).
* Pass-through copies: `c8Leaves_of_OpenAddedLeaves28_vp`, `sixContactMin_of_open83_nos_ds_vp`,
  `sixContactMin_of_open84_ds_vp` … `sixContactMin_of_open96_ds_vp`, and the top
  `sixContactMin_of_open98_vp` (through `openResearchLeaves77DS_of_OpenResearchLeaves78`, reused).
* The research and textbook bundles are unchanged and reused.

## Plan for the later fold (in progress; not part of this PR)

The fold that removes `scholzeH1AbVar` and `t10TateDuality` needs two single-print rows on `V_p(A)`
and one Lean theorem from them to `VpDualDeRhamAbVar`. The candidates being worked out in a separate
lane:

* Colmez, *Périodes p-adiques des variétés abéliennes*, Math. Ann. 292 (1992), Thm 5.2: `V_p(A)` is
  de Rham. The period pairing `H¹_dR(A) × T_p(A) → B_dR` is Galois-equivariant, sends `H⁰(Ω¹)` into
  `Fil¹ B_dR`, and is non-degenerate over `B_dR` (Thm 5.2(ii), p. 639).
* Fontaine, *Formes différentielles et modules de Tate des variétés abéliennes sur les corps
  locaux*, Invent. Math. 65 (1982): the Hodge-Tate decomposition `ℂ_p ⊗ V_p(A) ≅ ℂ_p(1)^g ⊕ ℂ_p^g`.

Then, in order:

1. A Lean theorem `vpDual_of_colmez_fontaine : <Colmez row> → <Fontaine row> → VpDualDeRhamAbVar`.
   Clause (i) comes from the de Rham row (dualized, `DeRhamPrint.isDeRhamTensorOver_dual`). Clauses
   (ii)-(iii) come from the Hodge-Tate decomposition through the equality of Hodge and Hodge-Tate
   numbers for de Rham representations. That equality is not in the tree; whether it is proved in
   Lean or needs its own row is for that lane to settle.
2. `OneProof/H/TailZ106.lean`: `OpenAddedLeaves30 := {<Colmez row>, <Fontaine row>}`; a conversion
   `openAddedLeaves29VP_of_OpenAddedLeaves30 (n) : OpenAddedLeaves29VP` with
   `vpDual := vpDual_of_colmez_fontaine n.… n.…`; and
   `sixContactMin_of_open99 r t l := sixContactMin_of_open98_vp r t
   (openAddedLeaves29VP_of_OpenAddedLeaves30 l)`.
3. `Main.lean`: `frozenTarget (l : HDec.HSyn.OpenAddedLeaves30)` through `sixContactMin_of_open99`
   (`FoldCheck.frozenTarget_with_vpDual` is that body over `OpenAddedLeaves29VP`).
4. `docs/one-proof/kinds.tsv`: the two rows `added scholzeH1AbVar` and `added t10TateDuality` are
   replaced by the two single-print rows (written by that lane; no merged row). Count unchanged
   (22), with each new row rated by its own reading. Any `reviews.tsv` rows of the two old fields go
   to `reviews-retired.tsv` (there are none at `c0534273`). OPEN.md is regenerated with
   `scripts/one_proof/render_open.py`.

No existing constant changes. `ScholzeH1AbVar`, `T10_TateDuality` and the `HTMerge` theorems stay
for the superseded tops.

Sources of the current pair, recorded in the clause docstrings of `Row.lean` (they cover the
current rows only and are not a reading of the statement):

* Scholze, Forum Math. Pi 1 (2013) e1, Cor. 1.8, pp. 5-6, Thm 9.1(ii), p. 74, and Thm 9.3, p. 75.
* Milne, *Abelian Varieties* v2.0 (March 16, 2008), Part I, Thm 12.1(a), p. 55, with Rem. 12.5,
  p. 56: the edition read on main (the `t10TateDuality` docstring). The same statement in Milne,
  *Abelian varieties*, in Cornell-Silverman (eds.), *Arithmetic Geometry* (Springer 1986),
  Thm 15.1(a), p. 129, with Rem. 15.5, p. 131, is not yet read on main (draft #204).
* `h^{1,0}(A) = g`: Mumford, *Abelian varieties*, §4 (locator unverified).

## Open points

* The Lean theorem from the two single-print rows to `VpDualDeRhamAbVar` (step 1) is the remaining
  glue. The equality of Hodge and Hodge-Tate numbers for de Rham representations is the likely gap.
* If `main` gains a `TailZ106` first, re-run `gen_vp.txt` with its top in `SOURCES` and `TOP_OLD`.

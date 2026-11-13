#!/usr/bin/env python3
"""leaf-adopt3: edits of docs/research/h-decomposition.md (wave 25 and g0-split). Run once."""
import sys
p = sys.argv[1] if len(sys.argv) > 1 else 'docs/research/h-decomposition.md'
L = open(p).read().split('\n')

def find_row(prefix):
    idx = [i for i, l in enumerate(L) if l.startswith(prefix)]
    assert len(idx) == 1, (prefix, idx)
    return idx[0]

def set_row(prefix, new):
    L[find_row(prefix)] = new

def append_status(prefix, text):
    i = find_row(prefix)
    cells = L[i].split(' | ')
    assert len(cells) == 6, (prefix, len(cells))
    cells[-2] = cells[-2] + ' ; **leaf-adopt3**: ' + text
    L[i] = ' | '.join(cells)

def rep(old, new):
    t = '\n'.join(L)
    assert t.count(old) == 1, old[:70]
    t = t.replace(old, new)
    L[:] = t.split('\n')

# ---- status header
rep("""(glue proofs). No file under""", """(glue proofs). Brought up to date by **leaf-adopt3** (2026-11-13; report
`docs/research/leaf-adopt3.md`, log `scratch/leaf-adopt3/log.md`): g0-split's proof of G1-G17, G19
and the wave-25 reports are folded in; **`Leaves.lean` has no `sorry`** (dated paragraph at the
end of §0). No file under""")

# ---- §0 claim
rep("""manuscript that the proof uses). On the manuscript's own route, H follows from **23
research-level theorems** of the literature""", """manuscript that the proof uses). *leaf-adopt3 (2026-11-13): the numbers in this paragraph are
leaf-adopt2's; the current ones are 23 research-level and 35 textbook leaves, and the glue is
proved in Lean from the leaves and eleven named glue pieces (dated paragraph at the end of §0).*
On the manuscript's own route, H follows from **23
research-level theorems** of the literature""")

# ---- §0 dated paragraph, before the locator-audit paragraph
rep("""**Locator audit (loc-adopt, 2026-11-12).**""", """**leaf-adopt3 (2026-11-13): no `sorry`; wave 25 folded in.** (VERIFIED: `lake env lean
scratch/h-decomposition/Leaves.lean`, see §2.3.)
- **G0 is a theorem.** `HSyn.sixContactMin_of_leaves (r : ResearchLeaves) (t : TextbookLeaves)
  (gp : GluePieces) : ZInQ.SixContactMin`, with exactly these three hypotheses, uses only
  `propext`, `Classical.choice`, `Quot.sound`. Its proof is g0-split's `glueOutputs_of_leaves`
  (glue G1-G17, G19) followed by glue-assembly's G18-G20. `GluePieces` bundles the eleven glue
  Props that remain to be proved (§3, table "Glue pieces"): g0-split's ten pieces, with piece 5
  (additivity) narrowed to the model-level `ProductModelHeight` (h5-neron), and leaf-adopt2's
  `HeightCopiesAgree` (R18, R22 are now taken from the bundle through it).
- **Textbook leaves proved or narrowed.** T13 (Skolem–Noether), T19 (Brauer–Nesbitt), T22
  (Herbrand, both parts) are proved (t-skolem-kw, t-different), and T30 is proved from T16(a)
  (t30-adelic); all four leave the bundle. T20, T21 are proved in local form (the global forms
  stay leaves). T17 is narrowed to Kronecker–Weber for cyclic extensions and T18 to Chebotarev's
  existence form, with the forms the glue uses proved from them. T10 is now concrete and
  Galois-equivariant (t10-etale).
- **New leaves**: T36-T40 (x1-belyi: torsion of elliptic curves, Néron–Ogg–Shafarevich over
  `k(T)`, curves from function fields, constant field and rational cusp of `X₁(N)`), from which
  `X1ModelExists` and `BelyiX1` are proved, and T41 (Néron models exist, h5-neron's N1).
- **Glue proved**: C9 (c9-rhof), E1's `VSurjOfSurjective` (e1-sub), `SemisimpleBaseChange`
  (glue-ssbc, now in the file), `HodgeLatticeTheorem` from two Props and `DimBaseChange`
  (hodge-lattice), H5's Néron identity from N1, N2 and glue (h5-neron; H5 itself stays a leaf),
  the reduction of R1's clause `π₀(X₆) = 1` (pi0-x6; the clause stays in R1, as recommended).
- Counts: **23 research-level leaves** (21 concrete; R17 and R1(b) placeholders) and **35
  textbook leaves** (all concrete), **58** in all, **56 concrete**.

**Locator audit (loc-adopt, 2026-11-12).**""")

# ---- §2.1 R1, R16, H5
rep("""rv-blueprints Q4 (SPECULATIVE). Part (b) is the placeholder""", """rv-blueprints Q4 (SPECULATIVE); leaf-adopt3: pi0-x6 found that sketch incomplete and proved the
clause instead from R5's clauses `R5ptProps`, `R5fpCount` and two new Props (`Pi0X6.R2X6CMExact`,
exact CM at the points over `0`, `∞`; `Pi0X6.AGInputs`, algebraic geometry over `ℚ̄`):
`Pi0X6.leafAdopt_r1pi0Props_of_bundle`, compiled in `Leaves.lean`; the clause stays part of R1, as
pi0-x6 recommends. Part (b) is the placeholder""")
rep("""leaf (rv-leaves48 P2).""", """leaf (rv-leaves48 P2). **leaf-adopt3**: resolved. `X1ModelExists` is proved from the new
textbook leaves T36, T38-T40 (x1-belyi, `HSyn.TextbookLeaves.x1ModelExists`), and
`HSyn.TextbookLeaves.exists_J1` gives a `J₁(N)` from T33 and those leaves, so R16 and T34 are not
vacuous for lack of a model.""")
rep("""non-vacuous"). Steps E2-E4 (G18), F3 (G19).""", """non-vacuous"). Steps E2-E4 (G18), F3 (G19). **leaf-adopt3**: h5-neron reduces H5's identity
"`stableFaltingsHeight` = the Néron-model height over a large enough field" to two leaves (N1
`ZInQ.H5Neron.NeronModelExists`, now textbook leaf T41; N2 `SemistableNeronIdentityComponent`) and
glue (`NeronModelMinimal`, `ModelHeightBaseChange`, `GroupModelBaseChangeExists`,
`OpenSubgroupHeight`): `ZInQ.H5Neron.stableFaltingsHeight_eq_neron_all`, compiled in `Leaves.lean`.
No theorem concludes H5 (its `NeronModelMinimal` half is a hypothesis of the reduction and
`StableHeightFinite` needs AN3), so H5 stays a leaf. hodge-lattice proves
`HodgeLatticeTheorem` (one of AN3's three Props) from `RegularAtOrigin`, `DimAtOrigin` and
`DimBaseChange` (`HSyn.G0Split.hodgeLatticeTheorem_of_dimBaseChange`).""")

# ---- §2.2 rows
set_row("| T10 |", "| T10 | `H¹(A_K̄, ℤ_ℓ) ≅ Hom(T_ℓA, ℤ_ℓ)`, Galois-equivariantly (so `V_ℓ(A) ≅ H¹_et(A_K̄, ℚ_ℓ)^∨`) | Milne 1986, Thm 15.1(a); Bhatt–Scholze 2015 §5.6 (pro-étale comparison) | E | **yes** (leaf-adopt3, from t10-etale): `T10Etale.T10_TateDuality` over Mathlib's pro-étale `Scheme.EllAdicCohomology` with its `ℤ_ℓ`-module structure and the Galois action by transport of structure (both built in t10-etale, no `sorry`); implies leaf-push2's `T10_groupIso` (`HSyn.TextbookLeaves.t10_groupIso`) | none |")
set_row("| T13 |", "| ~~T13~~ | Skolem–Noether | Reiner Thm 7.21 | — | **glue, proved** (leaf-adopt3, from t-skolem-kw): `HSyn.t13_proved : HSyn.SkolemNoether`, also `PkgI6.SkolemNoether`, `GlueDescent.LeafSkolemNoether`; no longer a field | Tau Ceti `skolemNoether` |")
set_row("| T17 |", "| T17 | Kronecker–Weber, **narrowed** (leaf-adopt3) to cyclic `L/ℚ`, the case C8 uses | Washington Thm 14.1 | C | yes, `TSkolemKW.KW.KroneckerWeberCyclic` (a consequence of `HSyn.KroneckerWeber`, proved); C8's use form (a finite-order character of `G_ℚ` is Dirichlet) proved from it (t-skolem-kw) | Tau Ceti `kroneckerWeber` |")
set_row("| T18 |", "| T18 | Chebotarev, existence form (**narrowed**, leaf-adopt3) | Neukirch VII.13.4 | C | yes, `PkgI6.ChebotarevExists`; the density form `HSyn.FrobeniusDense` is proved from it (`HSyn.TextbookLeaves.frobeniusDense`, t-skolem-kw), and so is glue-c10's `c10` with T19 discharged (`TSkolemKW.C10.c10_of_chebotarev`) | Tau Ceti `hasNaturalDensity_frobeniusPrimeSet` |")
set_row("| T19 |", "| ~~T19~~ | Brauer–Nesbitt (char 0, trace form) | Curtis–Reiner §30; Lang XVII 3.8 | — | **glue, proved** (leaf-adopt3, from t-skolem-kw): `HSyn.t19_proved : HSyn.BrauerNesbitt`, also `PkgI6.BrauerNesbittChar0`; no longer a field | none found |")
set_row("| T30 |", "| ~~T30~~ | Local square-root criterion: `χ\\|G_{ℚ_p}` has a continuous square root iff `χ(u) = 1` for `u ≡ −1 mod p^k`, `≡ 1` prime to `p` | consequence of local CFT for `ℚ_p` (Serre, *Local fields*) | — | **glue, proved from T16(a)** (leaf-adopt3, from t30-adelic): `HSyn.TextbookLeaves.leafSqrtCrit` (`T30.leafSqrtCrit_of_t16a`); no longer a field | none |")
append_status_rows = None
i = find_row("| T20 |"); L[i] = L[i].rstrip(' |').rstrip() if False else L[i]
rep(L[find_row("| T20 |")], L[find_row("| T20 |")].replace("| E | yes,", "| E | yes (global form still a leaf; the local form `PkgI6.HilbertDifferentFormula` is **proved**, leaf-adopt3 from t-different, `HSyn.t20_local_proved`),", 1))
rep(L[find_row("| T21 |")], L[find_row("| T21 |")].replace("| E | yes,", "| E | yes (global form still a leaf; the local form `PkgI6.DifferentBound` is **proved**, leaf-adopt3 from t-different, `HSyn.t21_local_proved`),", 1))
set_row("| T22 |", "| ~~T22~~ | Herbrand: quotients `(G/H)^v = G^vH/H`, transitivity of `φ` | Serre IV §3 Props. 14, 15 | — | **glue, proved** (leaf-adopt3, from t-different): `HSyn.t22a_proved`, `t22b_proved` (`PkgI6.herbrandQuotient`, `herbrandTransitivity`); no longer fields | Tau Ceti `map_restrictNormalHom_upperRamificationGroup` |")
i = find_row("| T34 |")
L.insert(i + 1, "| **(g) New in leaf-adopt3** | | | | | |")
new_rows = [
 "| T36 | `E[N] ≅ (ℤ/N)²` for an elliptic curve over an algebraically closed field of characteristic 0 (Mathlib's Weierstrass points) | Silverman, AEC Cor. III.6.4(b) | E | yes, `X1Belyi.TorsionStructure` (field `x1.torsion`; x1-belyi) | none |",
 "| T37 | Néron–Ogg–Shafarevich over `k(T)`: good reduction at an irreducible `p` makes `k(T)(x(P))` unramified over `p` for torsion `P` | Serre–Tate 1968 Thm 1; AEC VII.4.1 | C | yes, `X1Belyi.GoodReductionUnramified` (`x1.goodRed`) | none |",
 "| T38 | A finite extension of `ℚ(T)` with constant field `ℚ` is the function field of a smooth proper curve, with a `ℚ`-point if it has a degree-1 place | Hartshorne I.6, II.6.7; Stacks, *Curves and function fields* | C | yes, `X1Belyi.CurveOfFunctionFieldQ` (`x1.curve`) | none |",
 "| T39 | `ℚ` is algebraically closed in `K_N = ℚ(j)(x(P))` (`X₁(N)` geometrically irreducible) | Igusa 1959; Shimura 1971 §6.2, Prop. 6.9 | E | yes, `X1Belyi.X1ConstantField` (`x1.constants`) | none |",
 "| T40 | `K_N` has a place of degree 1 (a rational cusp) | Silverman, *Advanced topics* V.3.1 (Tate curve); Ogg 1973 | C | yes, `X1Belyi.X1RationalCusp` (`x1.cusp`) | none |",
 "| T41 | Néron models exist: `A_L` has a smooth group model over `𝓞_L` with the Néron mapping property (h5-neron's N1) | Bosch–Lütkebohmert–Raynaud 1.2/1, 1.4/3 | E | yes, `ZInQ.H5Neron.NeronModelExists` (field `t41`) | Anthropic FLT (special case) |",
]
for k, r in enumerate(new_rows):
    L.insert(i + 2 + k, r)
L.insert(i + 2 + len(new_rows), "")  # keep table end? (blank line follows anyway)
del L[i + 2 + len(new_rows)]

# ---- §2.3 counts
rep("""### §2.3 Counts (VERIFIED from the lists and the compiled file; updated by leaf-adopt2, 2026-11-12)
""", """### §2.3 Counts (VERIFIED from the lists and the compiled file; updated by leaf-adopt3, 2026-11-13)

- **leaf-adopt3 counts.** Research-level: **23** leaves (R1-R22 and H5), unchanged. Textbook:
  **35** leaves: T1-T11, T14-T18, T20, T21, T23-T29, T31, T33-T41 (T13, T19, T22, T30 are now proved
  glue, T12 glue, T32 proved glue; T17 and T18 narrowed; T36-T41 new). In all **58**. Stated
  concretely: research **21** (R2-R16, R18-R22, H5) plus R1 in part; textbook **35** (T10 is now
  concrete). Total **56 of 58**, plus R1 in part. Placeholders: R17 and R1(b) (**2 `opaque`**).
  Bundle fields (VERIFIED by counting the structures): `ResearchLeaves` 26 (24 concrete, 2
  `opaque`: `r1an`, `r17`), `TextbookLeaves` 35 (all concrete; `x1` bundles T36-T40):
  **59 concrete Props, 2 placeholders**. `GluePieces`: 11 glue Props (§3).
- Lean check (leaf-adopt3, VERIFIED 2026-11-13): see `docs/research/leaf-adopt3.md` §1 for the
  run; **no `sorry`**, 2 `opaque`, no `axiom`; every `#print axioms` line, including
  `HSyn.sixContactMin_of_leaves`, gives `propext`, `Classical.choice`, `Quot.sound`.
- *The bullets below are leaf-adopt2's (counts then: 53 of 56).*
""")

# ---- §3 glue table
set_row("| G0 |", "| G0 | The leaves imply `SixContactMin` | G1-G20 | N5 L404-964 | **proved** (leaf-adopt3, from g0-split): `HSyn.sixContactMin_of_leaves (r : ResearchLeaves) (t : TextbookLeaves) (gp : GluePieces)` = (G1-G17, G19: `HSyn.glueOutputs_of_leaves`, proved from the bundles) then (G18-G20, proved); `GluePieces` = the eleven glue Props of the table below, still to be proved | small |")
append_status("| G7 |", "T30 is proved from T16(a) (`T30.leafSqrtCrit_of_t16a`, t30-adelic, with the kernel's `GlueI6Rest`, `GlueSqrtLocal`, `GlueSqrtDisj` copied into `Leaves.lean`); T13 proved (t-skolem-kw); G1-adelic (`|Γ'| = 144`) proved in scratch/t30-adelic, not copied")
append_status("| G8 |", "`SemisimpleBaseChange` is **proved** (glue-ssbc, section `GlueSSBCSec`; `HSyn.G0Split.semisimpleBaseChange`), so C2 has no glue hypothesis left; the instantiation on `A` is inside the glue piece `ModularConstituent`")
append_status("| G13 |", "`X1ModelExists` **proved** from T36, T38-T40 (x1-belyi), `VSurjOfSurjective` **proved** from R9, T26 (e1-sub, `E1Sub.vSurjOfSurjective`; `ρ_{f,ι}` is a sub of `V_ℓ(J₁(N)) ⊗ ℚ̄_ℓ`), C9 **proved**: `ρ_{f,ι}` semisimple and continuous, Brauer–Nesbitt against R14 and C8's `r₅` (c9-rhof, `C9Rhof.c9`, `c9_R14`, `c9_r5`)")
append_status("| G14 |", "`c10` needs only `ChebotarevExists` among the leaves (`TSkolemKW.C10.c10_of_chebotarev`); C9's `r₅ ≅ ρ_{f,5}` proved (`C9Rhof.c10_via_c9`)")
append_status("| G15 |", "T20, T21 proved in local form and T22 proved (t-different); the local-to-global transport for T20, T21 is still not in Lean")
append_status("| G17 |", "E1's hypothesis `SemisimpleBaseChange` proved (glue-ssbc); the application of T8 is in `glueOutputs_of_leaves`, with `EndDivision A` the glue piece `FibreSimple`; the reverse isogeny and products are the pieces `ReverseIsogeny`, `ProductExists`, `DimFinite` (`isogenousProduct`)")
append_status("| G18 |", "`BelyiX1` **proved** from T36, T37 (x1-belyi); R18 on `J₁(N)` proved (`javanpeykarJ1`) modulo the glue piece `X1BelyiOnModel` (transport of `BelyiX1` to the model of `IsJ1`); E3-E4 numerics proved (`transfer_core`); additivity proved from T41, H5 and the piece `ProductModelHeight` (`heightAdditivity_of_h5neron`)")

# glue pieces table after the proved-end paragraph
rep("""Route K replaces G9, G10, G12, G14 by **GK1**""", """**Glue pieces** (leaf-adopt3; `HSyn.GluePieces`, the third hypothesis of G0). g0-split split the
former `sorry` into named Props (docs/research/g0-split.md); each is a `def … : Prop` whose
docstring names its glue step. None is a literature leaf; each is to be proved by the project.
Sizes SPECULATIVE (g0-split).

| # | Lean (field) | Glue step | Status | Size |
| --- | --- | --- | --- | --- |
| 1 | `G0Split.DimFinite` (`dimFinite`) | definition level (G17) | open | small |
| 2 | `G0Split.DimBaseChange` (`dimBaseChange`) | definition level (E2, G17; also gives `HodgeLatticeTheorem` with two Props, hodge-lattice) | open | medium |
| 3 | `G0Split.X1BelyiOnModel` (`belyi`) | E2, Belyi half | `BelyiX1` proved from T36, T37; the transport to the model of `IsJ1` (x1-belyi notes, about 50-100 lines) open | small-medium |
| 4 | `G0Split.FibreSimple` (`fibreSimple`) | G5-G6 on `A` | open (cores proved: T27 at `(2,−3)`, `fibre_free`, `cm_of_val`) | medium |
| 5 | `ZInQ.H5Neron.ProductModelHeight` (`productModelHeight`) | E4 at model level | open; replaces g0-split's `HeightAdditivity`, now proved from it with T41 and H5 | medium |
| 6 | `G0Split.StableHeightBaseChange` (`stableHeightBaseChange`) | definition level (E3-E4) | open (h5-neron: needs a Néron-model transport glue not yet stated) | large |
| 7 | `G0Split.ProductExists` (`productExists`) | G17 | open | large |
| 8 | `G0Split.ReverseIsogeny` (`reverseIsogeny`) | G17 after Poincaré | open | large |
| 9 | `G0Split.ThetaPointOfFibre` (`thetaPoint`) | G19, F1 on `A` | open | very large |
| 10 | `G0Split.ModularConstituent` (`modularConstituent`) | G2, G4, G7-G16 | open (cores proved, including C9, E1's `VSurjOfSurjective`, C10, B3, D1-D5) | very large |
| 11 | `HeightCopiesAgree` (`heightCopies`) | transport between the two textual copies of the stable Faltings height | open (pure transport, WP1) | medium |

Route K replaces G9, G10, G12, G14 by **GK1**""")

# ---- §4
rep(L[find_row("| ℓ-adic étale")], "| ℓ-adic étale cohomology | T10 (to derive R10's Tate-module form) | **done for T10** (leaf-adopt3, from t10-etale): Mathlib's pro-étale `Scheme.EllAdicCohomology` with a `ℤ_ℓ`-module structure, transport along scheme isomorphisms and the Galois action (`T10Etale`) | done (statement) |")

# ---- §5 WPs
append_status_wp = lambda prefix, text: None
for pre, txt in [
  ("| WP2 |", "leaf-adopt3: T13, T19, T22 proved and T20, T21 in local form (t-skolem-kw, t-different); T17, T18 narrowed (KW cyclic, Chebotarev existence); remaining: T17, T18, T14-T15, T1, T2, global T20-T21"),
  ("| WP3 |", "leaf-adopt3: `SemisimpleBaseChange` done (glue-ssbc, in `Leaves.lean`); the disjointness step done (glue-sqrt-disj; T30 proved from T16(a), t30-adelic)"),
  ("| WP9 |", "leaf-adopt3: `X1ModelExists`, `BelyiX1` proved from T36-T40 (x1-belyi), `VSurjOfSurjective` proved (e1-sub); remaining: the glue piece `X1BelyiOnModel` (transport)"),
  ("| WP10 |", "leaf-adopt3: `HodgeLatticeTheorem` from `RegularAtOrigin`, `DimAtOrigin`, `DimBaseChange` (hodge-lattice); H5's Néron identity from N1 (T41), N2 and glue (h5-neron); `HeightCopiesAgree` is glue piece 11"),
  ("| WP13 |", "leaf-adopt3: the QM dichotomy's locator is now Chia-Fu Yu 2013 Thm 1.1 (loc-fix), not a combined locator"),
]:
    i = find_row(pre)
    cells = L[i].split(' | ')
    cells[1] = cells[1] + ' (' + txt + ')'
    L[i] = ' | '.join(cells)

# ---- remaining work
rep("""**Remaining work after leaf-adopt2 (2026-11-12).**""", """**Remaining work after leaf-adopt3 (2026-11-13).**
1. The eleven glue pieces of `HSyn.GluePieces` (§3, table "Glue pieces"), the only Lean work left
   between the leaves and H: smallest first `DimFinite`, `DimBaseChange`, `X1BelyiOnModel`
   (transport only), `FibreSimple`, `ProductModelHeight`, `HeightCopiesAgree`,
   `StableHeightBaseChange`, `ProductExists`, `ReverseIsogeny`, `ThetaPointOfFibre`,
   `ModularConstituent` (the bulk: G2, G4, G7-G16 on the actual `A`).
2. Placeholders: R1(b) (analytification, family form), R17 (fold def-ladic-cond's `CarayolR17'`).
3. Premises: Lemma P (rv-qm-polar); AN3 (`AnalyticUniformizationExists`, `…Unique`;
   `HodgeLatticeTheorem` now reduced to `RegularAtOrigin`, `DimAtOrigin`, `DimBaseChange`); Pazuki's
   Def. 2.6 coordinates (R22); Lin–Yang's printed (13)-(14) (R3).
4. Glue targets outside G0's hypotheses: `T12_ComplexConjEigen`, `R03_LinYang_algClosed`; pi0-x6's
   `R2X6CMExact`, `AGInputs` (if R1's clause `π₀(X₆) = 1` is to be derived); h5-neron's glue
   (`ModelHeightBaseChange`, `GroupModelBaseChangeExists`, `OpenSubgroupHeight`) and leaf N2 (if
   H5's identity is to be derived); the local-to-global transport for T20, T21.
5. Unification (WP1): the duplicated layers (`ZInQ.LeafPush2` vs `ZInQ.DefFaltings`, `LeafModCurves`
   vs `ZInQ.LeafPush2` curves, `HSyn` vs `PkgI4` Galois objects).

**Remaining work after leaf-adopt2 (2026-11-12; superseded by the list above).**""")

open(p, 'w').write('\n'.join(L))
print('ok')

# rv-hsyn: adversarial fact-check of h-decomposition.md

Status: review note (task rv-hsyn, 2026-11-11, branch `wip/rv-hsyn` from `wip/hsyn` at 279a09ec).
Results log: `scratch/rv-hsyn/log.md`; compile outputs `scratch/rv-hsyn/leaves.out`, `check.out`;
extra axiom checks `scratch/rv-hsyn/LeavesCheck.lean` (a copy of `Leaves.lean` with 20 more
`#print axioms` lines and one `example`). No other task's file was edited.

## Verdict: ANNOUNCEABLE AFTER REPAIRS

The Lean claims hold as stated (VERIFIED, §B). The counts add up (VERIFIED, §A.2). No leaf I
checked is stronger than its source. Before 01:00 the note needs: the TYZ sentence fixed (repair 1);
§3's description of route K's glue brought into line with §0, §1 and §6 (repair 2); and the B2-B3
claim corrected, because the four leaves that the proved theorem uses are glue-descent's cochain
forms, not the T14/T15 Props that the leaf bundle contains (repair 3). Repairs 4-10 are smaller:
wording that claims a little more than the file and the tables support. None of them changes a
count or the recommendation of route P.

## Repairs (exact replacement text)

**1. §0, CR3 side: the TYZ hypothesis (must fix).** The note says "weakened", but the Lean form
assumes a *special case* of the printed hypothesis.
Replace
> `TYZThm35ReadingA` is the intended reading of their Theorem 3.5(2), with
>   the hypothesis weakened to `𝓛(n) = 0`;

with
> `TYZThm35ReadingA` is the intended reading of their Theorem 3.5(2), used only in the case
>   `𝓛(n) = 0`. That case is a special case of the printed hypothesis "`2^{−ρ(n)}𝓛(n)` even", and
>   it does not depend on the unproved "i.e." of Theorem 3.5(2) (`docs/research/nt-tyz.md` §2.2, F6);

(Source: nt-tyz.md L275-278, VERIFIED. The same wrong word "weakened" is in the docstring of
`TYZThm35ReadingA`, `ZInQKernel/Hypotheses/CR3Literature.lean` L137-139. That file is outside this
task's write scope; flag it for the integration.)

**2. §3, last paragraph: route K's glue status (must fix: it contradicts §0, §1 and §6 R3).** §3
says GK1 and GK2 are "both NEW and unreviewed". But §0 says "one adversarial model review … found
it sound after five repairs", §1 says "Lemma GL₂ and Lemma Ind verified as arguments", and §6 R3
says "verified as arguments by one adversarial model review (rv-routek)".
Replace
> both NEW and unreviewed (hdec-elementary §2.2);

with
> both new (hdec-elementary §2.2), verified as arguments by one adversarial model review
> (rv-routek) with repairs 1-4 of §1 pending, and with no human review;

**3. §0, "What is in Lean today": B2-B3 (must fix).** `GlueDescent.B3Q.b3_degree_le_QM` takes the
hypotheses `LeafHasse`, `LeafLocalTwo`, `LeafSqrtCrit` and `LeafUnramified` (Leaves.lean L7449-7450,
VERIFIED). The first two are glue-descent's finite-place cochain consequences of T14 and T15. They
are *not* the Props in the bundle `HSyn.TextbookLeaves` (`PkgI6.BrauerHasse2`,
`PkgI6.BrauerReciprocity2`, `PkgI6.LocalH2Card`), and no Lean theorem derives them from those Props.
§5 lists that derivation as open work (WP3). (The cochains are locally constant, so these forms are
consequences of the continuous-cohomology statements, as the note says; VERIFIED, L6749-6755.)
Replace
> Glazer's Brauer and
> cochain steps B2-B3 from four textbook leaves, ending in `[L':ℚ] ≤ Q·M`;

with
> Glazer's Brauer and
> cochain steps B2-B3, ending in `[L':ℚ] ≤ Q·M`, from four textbook statements: T30, T31 and
> glue-descent's cochain forms of T14-T15 (`LeafHasse`, `LeafLocalTwo`). Deriving those two forms
> from the T14-T15 leaves as bundled is glue that is not yet proved (WP3);

In §3, row G7, replace "from T14-T15 (glue-descent forms), T30, T31" with "from glue-descent's
cochain forms of T14-T15 (`LeafHasse`, `LeafLocalTwo`; their derivation from `PkgI6.BrauerHasse2`,
`BrauerReciprocity2`, `LocalH2Card` is unproved, WP3), T30, T31".

**4. §0, the other `sorry`s (should fix).** §0 mentions only the top theorem's `sorry`. The file has
four (L1234, L3826, L3848, L9274; VERIFIED by `#print axioms`). The header of `Leaves.lean` lists
all four; §0 should list them too.
Replace
> The top theorem "leaves ⇒ H" is
> stated in Lean; its one `sorry` is the glue from the leaves to the numerical interface of the
> Arakelov end.

with
> The top theorem "leaves ⇒ H" is
> stated in Lean, with conclusion the repository's `ZInQ.SixContactMin`. Its proof has one `sorry`:
> the glue from the leaves to the numerical interface of the Arakelov end
> (`HSyn.glueOutputs_of_leaves`). Three statements of the reports are also stated with `sorry` and
> are not counted as proved: `PkgI2.goodReduction_of_QM_rational3` (A6), `PkgI6.artinConductor_le_of_upper`
> (D4), and `PkgI6.sq_principalUnits` (D3; the same statement is proved as `HSyn.sq_principalUnits_proved`).

**5. §0, the glue count (should fix).** The 21 rows G0-G20 include G0, "the leaves imply
`SixContactMin`", whose inputs are G1-G20. G0 is their composition, not a separate argument.
In the "Claim for H" paragraph replace "and **21 glue steps**:" with "and **20 glue steps**
(G1-G20, composed in G0):". In "The exact claim" replace "plus 21 glue steps;" with "plus 20 glue
steps;". (Alternatively keep 21 and write "21 glue items G0-G20" in both places.)

**6. §0, Lemma PR(i) and NoCM (should fix).** "the whole arithmetic of the repository's Lemma PR(i)
and NoCM" claims more than §3: row G2 lists Prop. TS and Lemma NV as unproved, and row G6 lists
the counting with R5 as unproved.
Replace
> the whole arithmetic of the repository's Lemma PR(i) and NoCM;

with
> the valuation case analysis and the identities of the repository's Lemma PR(i) (not Prop. TS or
> Lemma NV), and the explicit part of NoCM (not the count from R5);

**7. §1, reason (i), and §0's list: refereed status (should fix).** Reason (i) says "every route-P
modularity leaf is a journal paper". But R14 cites Deligne, Sém. Bourbaki 355 (1971) for `k ≥ 2`.
Elsewhere R1 cites Deligne, Sém. Bourbaki 389, R21 cites Bost, Sém. Bourbaki 795, and R6, R8, T1
and T2 cite SGA. Séminaire Bourbaki exposés and SGA volumes are published, but they are not
refereed journal papers in the usual sense (SPECULATIVE assessment). Under the task's definition of
a leaf ("published, refereed"), they raise the same question that the note raises for Ribet 1992.
Replace reason (i) with
> (i) A leaf must be a refereed published theorem. K2 (Ribet 1992) and the converse direction of
> Pyle appeared in proceedings whose refereeing is UNVERIFIED. Route P's modularity leaves are
> journal papers (Pan in JAMS) except R14 for `k ≥ 2`, which cites Deligne's Bourbaki exposé
> (Sém. Bourbaki 355, 1971). Route P has the same question for R1 (Deligne, Sém. Bourbaki 389;
> Shimura 1967 in Ann. of Math. is the primary source), R21 (Bost, Sém. Bourbaki 795) and the SGA
> citations (R6, R8, T1, T2). These are standard sources, but whether they count as refereed
> should be stated, not assumed.

and add to §6 R1 (Locators): "Refereed sources for R14 (`k ≥ 2`), R21 and the SGA-cited leaves, or
an explicit policy that Séminaire Bourbaki and SGA count as refereed."

**8. §0, placeholders (minor).** "named placeholders that carry no content until their definitions
exist" is wrong for T29. Its row says it is statable but not drafted, and §2.3 says its new
definitions are cheap.
Replace
> The other 12
> research-level and 7 textbook leaves are named placeholders that carry no content until their
> definitions exist.

with
> The other 12
> research-level and 7 textbook leaves are `opaque` placeholders with no content. Each needs new
> definitions (cheap for T29 and T32, up to very large for R1-R3, R5, R16, R18-R22) before it can
> be stated.

**9. §0, how R11 and R12 are counted (minor).** "10 research-level leaves" counts R11 and R12 as
stated, but only their joint consequence `PkgI4.PanBerger` is in the file. §0 says this. To make
the arithmetic visible, replace "and 25 textbook leaves, 35 of 54, are stated concretely" with "and
25 textbook leaves, 35 of 54 (33 stated individually, R11 and R12 only through their joint
consequence), are stated concretely".

**10. §2.1 R15: one input is missing (minor).** pkg-I4 §1.7 gives Deligne–Serre's Thm 4.1 as a
statement about weight-one *newforms*. `HSyn.DeligneSerreConseq` (Leaves.lean L9043) is stated for
every normalized eigenform of weight 1 and level `N`. Passing from an eigenform to a newform uses
T25 as well as T18 and T19.
In R15 replace "(with T18, T19 for "every semisimple `ρ` with these traces")" with "(with T25 to pass
from an eigenform to a newform, and T18, T19 for "every semisimple `ρ` with these traces")". If the
printed Thm 4.1 covers every eigenform of the Hecke operators `T_p`, `p ∤ N`, T25 is not needed;
the number and statement are UNVERIFIED.

## A. §0 against its sources

A.1 Theorem numbers. Each of these locators appears in the reports or designs (grep, VERIFIED as
present; not checked against the papers, no network): Javanpeykar 1.1.1 (pkg-I5, glue-assembly);
Pazuki Cor. 1.3 (pkg-I5, glue-assembly); Baba–Granath Lemma 3.1 (h-trust, hdec-*); Lin–Yang
Example 30 (pkg-I1); González–Rotger 5.12 and Prop. 5.6 (pkg-I1, glue-repo); Berger 0.7 (pkg-I4);
Pan 1.0.4 (pkg-I4, h-a011); Deligne 4.21 (pkg-I1); SGA 7 IX Prop. 4.7 (pkg-I2); Faltings Lemma 5
(pkg-I5); Faltings Satz 3 (pkg-I3); Scholze Cor. 1.8 (pkg-I4, h-a011). Also present: Gaudron–Rémond Thm 1.4 (pkg-I5 L4, L95; glue-assembly L282)
and Deligne–Serre Thm 4.1 (pkg-I4 §1.7; h-trust L564, L920). pkg-I4 L163 cites Deligne–Serre
Thm 6.1 for the existence of `ρ` in weight 1. That is consistent with the note, which gives no
number for R14 at `k = 1`. UNCHECKED: every number in §2.2.

A.2 Counts (VERIFIED against the note's lists and the compiled file). R1-R22: 22. T1-T32: 32.
G0-G20: 21 rows (repair 5). Stated research Props: r4, r6, r7a, r7b, r9a, r9b, r10, r11r12, r13,
r14, r15, which is 11 Props for 10 leaves. Stated textbook Props: 28, for 25 leaves. Total 35
leaves and 39 Props. The 19 `opaque` placeholders in the file (L9075-9178) are exactly R01, R02,
R03, R05, R08, R16-R22, T09-T12, T23, T29, T32, which is the list in §2.3 and §0. Route K:
22 − 6 + 4 = 20.

A.3 The CR3 caveats against README.md. The note's caveats are at least as strong as README's: the
literal Theorem 1.2 is false (d = 26565, 33117); the proposition on the way is only sketched; the
journal version is unchecked; Proposition N was reviewed twice by models and never by a human. The
note adds "Neither TYZ form is a printed statement". Only the wording of repair 1 is wrong. One
difference that needs no repair: README says the fork proves the theorem "from four explicit
hypotheses", and §0 says "from two hypotheses", with CR3 reduced to three. That is the same count
grouped differently.

## B. The Lean claims (all VERIFIED by compilation, Lean 4.35.0, Mathlib v4.35.0)

- `lake build ZInQKernel.Hypotheses.JHeight`: success. `lake env lean
  scratch/h-decomposition/Leaves.lean`: exit 0, no errors, no `axiom`.
- Every Prop that the note calls stated is a `def` with content over genuine definitions. I checked
  all 39 fields of `ResearchLeaves` and `TextbookLeaves` against their `def`s; none is `True` or
  `opaque`. Spot checks: `AbVar` and `IsAbelianVariety` are proper, smooth, geometrically integral
  group objects over `Spec K`. `CF N k` is Mathlib's `CuspForm` for `Γ₁(N)`.
  `IsNormalizedEigenform` is nebentypus plus `a₁ = 1` plus the full Hecke recursion. The cochains
  in `LeafHasse` are locally constant.
- Axioms are only `propext`, `Classical.choice` and `Quot.sound` for the 20 theorems the file
  prints and for 15 more that the note cites by name: `PkgI1.gram_det`, `cm4`, `cm24`,
  `G6_sub_F2`, `Ju_ne_branch`, `elkies_t`, `elkies_t_sub_one`, `thetaRatio_invariant`;
  `GlueAssembly.logHeight_Phi_le`, `transfer_of_level`, `weight_match_coh`,
  `sixContactMinAt_of_glueOutputs`; `PkgI3.range_tateHomZl_subset`;
  `GlueDescent.B2Q.b2_of_leaves`; `GlueConductor.exists_sq_eq_one_add`.
- `sorryAx` appears exactly in `HSyn.glueOutputs_of_leaves`, hence in `HSyn.sixContactMin_of_leaves`,
  and in `PkgI2.goodReduction_of_QM_rational3`, `PkgI6.artinConductor_le_of_upper` and
  `PkgI6.sq_principalUnits`. That is four `sorry` sites, all listed in the file header; §0 names
  only the first (repair 4). None of the theorems the note calls proved depends on them.
- The conclusion is the real hypothesis: `example : HSyn.ResearchLeaves → HSyn.TextbookLeaves →
  ZInQ.SixContactMin := HSyn.sixContactMin_of_leaves` compiles. `ZInQ.SixContactMin` comes from the
  imported `ZInQKernel.Hypotheses.JHeight`, and `HSyn.sixContactMin_of_glueOutputs` has type
  `GlueOutputs Mult.S_mul → ZInQ.SixContactMin` with no `sorry`.
- Caveat, as the note says itself (§3, §6 R5): `glueOutputs_of_leaves` ignores its arguments and is
  `sorry`, so "leaves ⇒ H" has no content beyond "`GlueOutputs` ⇒ H". `GlueOutputs` is a height
  bound in disguise, not a leaf.

## C. §1-§6 spot checks

- Internal contradiction: §3 against §0, §1 and §6 on GK1 and GK2 (repair 2). §6 "B2's two
  formalizations" correctly says that glue-descent's forms are derived from pkg-I6's forms via WP3,
  and §0 should say the same (repair 3).
- Leaves checked against their sources: R7 (the finite-level NOS form is in Serre–Tate Thm 1; the
  Lean form uses torsion points, not the Tate module); R14 (`k ≥ 1`, semisimple, traces at
  `p ∤ Nℓ`: Deligne, and Deligne–Serre for `k = 1`); R13 (Hodge–Tate weights `{0, 1−k}` at every
  level, a consequence of de Rham or pst); T5 (genuine abelian varieties, so not false for `G_m`).
  None is stronger than its source as stated (STANDARD, references UNVERIFIED).
- UNCHECKED for lack of time: the Lean bodies of R4, R6, R10, `PanBerger`, T1-T4, T16, T22 and
  T24-T28 against their sources; the §4 definitions table; the §5 dependencies.

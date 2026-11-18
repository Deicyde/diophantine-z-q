# Scholze comparison: restrict the added row to surfaces

**VERIFIED (source):** `ScholzeH1Narrow` restricts `ScholzeH1AbVar` to
`g = 2`. It drops the requirement at other dimensions; it drops **no
numbered clause**. For every prime `p`, finite `F/ℚ_p`, and abelian surface
`A/F`, it still asks of `H¹_ét(A_F̄, ℚ_p)` that it is de Rham, its
`D_dR` has `Fil⁰ = D_dR` and `Fil² = 0`, and
`dim_{ℚ_p} Fil¹ = 2 [F:ℚ_p]`. The live G9 consumer (including C8 through G9)
uses all three. The dimension-free Or result reaches a dead record slot.
The restriction keeps the original quantifiers over primes and finite
extensions; the G9 reader is stated at an arbitrary coefficient prime.

The proposed field is `scholzeH1Narrow :
DeRhamScholze.HTMerge.ScholzeH1Narrow`. A proof of the original row
specializes via `narrow_of_abVar`; `narrow_iff_abSurf` identifies the new
row with the existing `ScholzeH1AbSurf` (commuting the two factors in the
rank formula). There is no new literature input.

## Reader census

VERIFIED by reading the base at `41892618b`; the kernel-side dependency
audit of the carrier modules is replayable with
`scratch/scholze-narrow/Census.lean`; the output lists their exact declaration
edges. The generated declaration map gives source locations for the copied
converters, including those which project only unchanged fields.
Number the clauses as in `ScholzeH1AbVar`: **1** de Rham, **2** filtration
range (both `Fil⁰ = D_dR` and `Fil² = 0`), **3** rank of `Fil¹`.
All local instances use finite extensions of `ℚ_p`; the table distinguishes
arbitrary variables at intermediate declarations from actual applications.

| Base declaration or call | Clauses read and actual field/dimension |
| --- | --- |
| `ZInQ.OneProof.frozenTarget` (`ZInQKernel/OneProof/Main.lean:190`, call at 197); `OpenAddedLeaves28.scholzeH1AbVar` (`ZInQKernel/OneProof/H/TailZ87.lean:69`, field at 73) | The headline passes the bundle to `sixContactMin_of_open82`. The other headline inputs have no path to this field. |
| `sixContactMin_of_open82` and `openResearchLeaves60_y3x6_of_OpenResearchLeaves63` (`ZInQKernel/OneProof/H/TailZ89.lean:79,90,110,122,124`) | Two syntactic reads: the dimensionless HT slot uses 1–2; the dimensioned HT slot uses 1–3. The third argument to the H top is the only live added bundle. |
| `c8Leaves_of_OpenAddedLeaves28`, `c8Inputs_of_leaves` (`ZInQKernel/OneProof/H/TailZ87.lean:109`; `ZInQKernel/Contrib/OneProof/C8Printed.lean:30`) | No clause. `C8Leaves` projects `conradAppB`; the other three `C8Inputs` fields are closed proofs. The outer applications after this expression in `TailZ87.lean:116` supply the HT argument and T10 separately; that top is historical. |
| `hodgeTateDecompOr_of_scholzeH1Milne` → `hodgeTateDecompHom_of_scholzeH1` → `dual_deRham_of_scholzeH1` (`ZInQKernel/Contrib/OneProof/ScholzeH1AbVar.lean:192,184,163`) | Clauses 1–2 in the generic API; `dual_of_H1` accepts 1–3 but this pair projects away its rank output. Finite `F/ℚ_p`, arbitrary `g` from `dim_finite_I4` in the generic proof. At the base headline the result only fills a discarded slot. |
| `openResearchLeaves59_y3x6_of_60_y3x6` → `openResearchLeaves54SFU_y3x6_of_59_y3x6` → `openResearchLeaves36EBCFSFU_y3x6_of_54SFU_y3x6` → `openResearchLeaves35EBCFSFU_y3x6_of_36_y3x6` (`ZInQKernel/OneProof/H/Y3Open.lean:332,366,413,454`) | Forwards the general Or field, converts it to `hodgeTateDecompExists` at 435, then drops it (the next converter takes the explicit dimensioned HT proof). No geometric instance of the Or backend is taken on the live route. |
| `hodgeTateDecompAbVar_of_scholzeH1` → `htDecomp_of_H1` → `dual_of_H1` and `hodgeTate01_dims` (`ZInQKernel/Contrib/OneProof/ScholzeH1AbVar.lean:199,138,102`; `ZInQKernel/Contrib/OneProof/HTAbVarScholzeDims.lean:172`) | 1 for the full de Rham dimension, 2 for the bounds on `Fil⁰` and `Fil²`, 3 for the multiplicity of weight −1, with the remaining multiplicity coming from Tate-module rank. General `p,F,g` in the API; only the local surface below is needed. The duality uses the existing `t10TateDuality` over that same `F`. |
| `openResearchLeaves35EBCFSFU_y3x6_of_36_y3x6` through `researchLeaves5_of_open7_pz_eb_u_c8_y3c` (`ZInQKernel/OneProof/H/Y3Open.lean:454`; `ZInQKernel/OneProof/H/Y3Copy5.lean:1183,1194`) | The `hodgeTateDecompAbVar` field passes through the Y3 conversions into `r10`; no intermediate conversion takes a local instance. |
| `deRhamComparisonHT_of_leavesT` → `deRhamComparisonHT_of_leaves` and `HodgeLF7.r10` (`ZInQKernel/OneProof/H/TailS.lean:2059,730`; `ZInQKernel/OneProof/H/TailV.lean:162`; types in `ZInQKernel/Contrib/R10/Amend.lean:43` and `ZInQKernel/OneProof/H/LPrefix.lean:13562`) | Both generic R10 parts ask for HT at arbitrary `g` in their statements: exact multiplicities at `0,−1` and vanishing elsewhere. The old tensor de Rham bridge also takes finite dimension from HT. The proposed bypass specializes those requests before building R10; G9 uses all four conclusions at the same surface. |
| `deRhamVpAbVarDirect` projection and adapters (`ZInQKernel/OneProof/H/TailZ89.lean:36,89`; `ZInQKernel/OneProof/H/Y3Open.lean:433`; `ZInQKernel/OneProof/H/Y3Copy4.lean:92`; `ZInQKernel/Contrib/OneProof/DeRhamPrintDirect.lean:193`; `ZInQKernel/Contrib/OneProof/DeRhamPrint.lean:386`) | No Scholze clause. The separate open research field passes through `deRhamVpAbVarPrinted` to `deRhamH1AbVarT`, giving the old R10 assertion for the Tate module. The bypass keeps that path. |
| `g8_g12_of_leaves3_hf_pz_eb_u_c8_y3c`, `afterG7NC_of3_hf_pz_eb_u_c8_y3c`, `g8_g12_hf_pz`, `g8_g11_hf` (`ZInQKernel/OneProof/H/Y3Copy5.lean:1225,1235,1237,1556,1574`; `ZInQKernel/OneProof/H/PicZeroCharZeroCopy.lean:815,831`; `ZInQKernel/Contrib/OneProof/HomFreeFiniteAlgClosedReroute/Consumers.lean:553,570`) | No direct Scholze read; at 3 and 5 they pass R10 to G9 for the input surface. |
| `g12DetPZ_of_inputs` → `g12DetPZ_of_twistFinite` (`ZInQKernel/Contrib/OneProof/C8Poincare.lean:41`; `ZInQKernel/Contrib/OneProof/C8Conrad.lean:179–182`) | C8 reads the weight half of G9 at `p=5`; no extra field or dimension is requested by C8. |
| `g9GlueNoT23_of_deRhamComparisonHT` → `g9GlueNoT23_of_abVarBaseChange` → `g9GlueNoT23_of_localModel` → `g9GlueNoT23_of_fieldEmb` (`ZInQKernel/OneProof/H/TailE.lean:6393`; `ZInQKernel/OneProof/H/TailC.lean:14398,14201,14121–14157`) | The only effective R10 instance: `g=2`, at the local model `A'/F` for the incoming surface over `K`; `F/ℚ_p` is finite Galois in the local-model bridge. The separate weight-vanishing call is at exactly the same `F,A'`. The older T23 form filled in `Y3Copy5.lean:1677` is a discarded `GaloisPiecesC8.deRham` slot. |
| `hodgeNumberH1AbVar_of_scholzeH1`, `deRhamVpAbVarDirect_of_scholzeH1`, `deRhamVpAbVarDirect_of_scholzeH1Milne`, `scholzeH1AbSurf_of_abVar` (`ZInQKernel/Contrib/OneProof/ScholzeH1AbVar.lean:91,173,179,75`) | Standalone API, absent from the headline. Respectively 3 at arbitrary `g`; 1 at arbitrary `g` (the helper produces 2 but only its first conjunct is taken); same with Mumford discharged; 1–3 at `g=2`. The surface versions recover exactly their surface instances. |
| Historical `sixContactMin_of_open80`, `sixContactMin_of_open81` (`ZInQKernel/OneProof/H/TailZ87.lean:114–116`; `ZInQKernel/OneProof/H/TailZ88.lean:91,122`) | Imports, not calls from the current headline. These also syntactically fill Or and dimensioned HT slots. |

## Re-proved readers

In `ZInQKernel/Contrib/OneProof/ScholzeNarrow.lean` the pointwise
`hodgeNumberH1AbSurf_of_narrow`, `dual_deRhamSurf_of_narrow`,
`deRhamVpAbSurfDirect_of_narrow`, and
`deRhamVpAbSurfDirect_of_narrowMilne` give the same outputs as the original
readers at a surface. The three HT readers are
`hodgeTateDecompHomSurf_of_narrow`, `hodgeTateDecompOrSurf_of_narrowMilne`,
and `hodgeTateDecompAbSurf_of_narrow`. The Or version retains the
disjunction of uniform alternatives, specialized to surfaces. The examples
in `scratch/scholze-narrow/Readers.lean` recover each original **surface
instance** through `narrow_of_abVar`. The arbitrary-dimension API remains
as it was; the narrower assumption by itself does not furnish proofs at
unspecified dimensions.

`r10Surface_of_leaves` computes all the multiplicities from the existing
equivariant decomposition, applies the same independent tensor de Rham
bridge to `V_p(A)`, and packages the outputs at the same surface.
`r10Surface_of_abVar` specializes the old amended R10 to this bundle.
`HDec.HSyn.HodgeLF7.r10Surface` gives the assembly's copy, and
`HDec.ZInQ.Contrib.G9.g9GlueFromSurfaces_of_fieldEmb` applies both parts of
R10 at the same witness from the local-model theorem. It reuses the
coefficient descent and the two period and weight descent arguments.
These are GLUE, with the specialization and bypass on the spot
(provenance (c)). The module and all reader examples compile. The 14
`#print axioms` results in `scratch/scholze-narrow/readers-axioms.txt` use
only `propext`, `Classical.choice`, and `Quot.sound`.

`#discharges` against the base checked 13,861 theorems and found 135
existing matches for 37 open hypotheses. None came from
`ScholzeNarrow.lean`; in particular the narrowing does not claim to
discharge the old field. The only match for that field was the existing
conditional `scholzeH1AbVar_of_old`. See
`scratch/scholze-narrow/discharges-output.txt`.

## Fold and counts

`autofold.py` cannot express this change: it requires filling the old
general field before calling the old top. The available implication goes
from the old field to the new surface one. The proposed bypass uses the
same outer proof and changes R10 in the affected chain. It removes the
unread intermediate Or/Exists slot and the unused T23-form G9 slot.
`conradAppB`, `t10TateDuality`, `deRhamVpAbVarDirect`, and the Berger
survey row are retained. No tracked module, headline, or catalog was
folded.

**VERIFIED (compiled):** the generator emits 121 declarations in
`scratch/scholze-narrow/Chain.lean`, with source locations in
`generated-declarations.tsv`. The chain compiles on its own. The
standalone `DryRun.lean` adds the
proposed headline and traverses the types and values, including opaque
proof values, below both versions of the H top and the headline. The
results in `dry-run-output.txt` show `ScholzeH1AbVar` and the old added
bundle present below both original tops and absent below both proposed
tops. The new proposition and bundle show the reverse pattern. The
general Or slot and old G9 wrapper are absent from the proposed closures;
the surface R10 and G9 proofs replace them. The four retained inputs
listed above occur in all four closures. No closure contains `sorryAx`;
all 89 dry-run axiom checks report the same three standard axioms.
`scratch/scholze-narrow/REPLAY.md` gives the replay commands.

VERIFIED (computed with the repository scorer; see
`scratch/scholze-narrow/counts-output.txt`):

| Scope | Strict before → after | Strictest before → after |
| --- | --- | --- |
| H (33 open) | 5 LEAF / 28 GLUE → 5 LEAF / 28 GLUE | 5 LEAF / 28 GLUE → 5 LEAF / 28 GLUE |
| Full headline (37 open) | 5 LEAF / 32 GLUE → 5 LEAF / 32 GLUE | 5 LEAF / 32 GLUE → 5 LEAF / 32 GLUE |

The proposed `added` row is in `scratch/scholze-narrow/kinds-row.tsv`:
`scholzeH1Narrow`, kind **consequence**, **GLUE / GLUE**, flag
**pending review**. Removed clauses: none; domain change: only `g = 2`.
The reviewer rates the new statement.

## Known issues

- **VERIFIED (manuscript), L10996:** the Hodge numbers are uncited. The
  specialization removes the need for a general-dimension Hodge-number
  input. It leaves the surface input explicit: the comparison must give
  `dim_F Fil¹ = 2`. Together with de Rham dimension, the Tate-module
  rank 4, and `Fil⁰ = D_dR`/`Fil² = 0`, this supplies multiplicity two
  for both grades. The new Lean statement assumes the first number and
  the proof derives the second; it does not prove the first from
  algebraic differential forms.
- **UNVERIFIED (locators):** Scholze, *p-adic Hodge theory for
  rigid-analytic varieties*, Forum Math. Pi 1 (2013), Cor. 1.8 and
  Thms. 9.1 and 9.3, with the corrigendum, Forum Math. Pi 4 (2016) e6.
  These are the manuscript locators; the corrected print was not
  re-read. The relation of algebraic and analytic comparison and of the
  Lean pro-étale model to classical étale cohomology is still part of
  checking the literature consequence.

## Manuscript check

Each locator is in `diophantine_zq.tex`.

| Lines | Verdict |
| --- | --- |
| L735–738: de Rham and the two weights at every coefficient prime | **OK** as an application of the appendix; the height proof uses the local surface and its two rank-two summands. |
| L758–766: the twist and the weight calculation at 5 | **OK** for the dependence checked here: C8 uses the weight pair from G9 at 5, so it adds no dimension or local field requirement to the comparison. The Conrad consequence remains a separate input. |
| L10939–10951: hypotheses and conclusion of `lem:de-rham-descent` | **OK** as used in this reroute: the dimension-two hypothesis is supplied by the local model; both R10 accesses use that very model. |
| L10954–10965: analytification, comparison with the corrigendum, passage to the algebraic étale group | **unverified** as a reading of the printed theorems and the Lean dictionary. Both the de Rham clause and the filtration bounds are still retained in the comparison assumption. |
| L10967–10978: Milne duality, coefficient extension and passage to a summand | **OK** as used here: the Galois equivariant duality is the same explicit input, and the existing finite coefficient and summand proofs are reused. No new locator check. |
| L10980–10994: finite extension descent | **OK** for the step used here; the old G9 proof of descent is reused with exactly the same input at its chosen local field. |
| L10996: Hodge numbers two and two | **unverified** as a source claim. The line gives no reference or proof of the `Fil¹` rank; dimension two alone in the Lean model does not supply it. The new row records exactly the rank input, and the glue accounts for the other number as described above. |
| L10997–11000: dual signs and halving the multiplicities in the two isomorphic summands | **OK**: at the surface the two multiplicities are 2 and all others vanish; the G9 descent argument consumes those exact facts and recovers the weights of a summand. |
| L11003–11006: using de Rham comparison itself | **OK**: the full de Rham clause stays in `ScholzeH1Narrow`; its dimension equality is used in the HT proof and is not supplied by the separate direct de Rham row. |

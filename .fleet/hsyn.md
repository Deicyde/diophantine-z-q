# hsyn: fleet report (synthesis of the decomposition of H)

**Deliverables.** `docs/research/h-decomposition.md` (§0 announcement summary, §1 route decision,
§2 leaves, §3 glue, §4 definitions, §5 work packages, §6 risks);
`scratch/h-decomposition/Leaves.lean` (one file, 9.3k lines, assembled from the reports' compiled
drafts by `scratch/hsyn/assemble.py`; `lake env lean` exit 0, no `axiom`, VERIFIED); log
`scratch/hsyn/log.md`. Note: `lake build ZInQKernel.Hypotheses.JHeight` must run once in a fresh
worktree first (two upstream helpers, seconds).

**Claim.** On the manuscript's route (route P), H = `ZInQ.SixContactMin` follows from **22
research-level theorems**, **32 textbook theorems** (six groups) and **21 glue steps** (Glazer's
new arguments, the repository's Lemma PR and NoCM, bookkeeping). The glue is not formalized and
has model reviews only. CR3 side unchanged: `Literature.GrossZagier`, `FunctionalEquation5`, and
TYZ as `TYZRow5b` or `TYZThm35ReadingA` + `HeckeContinuation` (neither TYZ form printed;
README caveats kept).

**Statable now.** 35 of 54 leaves (39 Props) over genuine definitions: research R4 (Igusa theta
modularity), R6 (Raynaud), R7 (Serre–Tate), R9 (Faltings 1983), R10 (de Rham comparison), R11+R12
jointly (`PkgI4.PanBerger`), R13 (HT weights of eigenforms), R14, R15 (eigenform representations,
Deligne–Serre); textbook T1-T8, T13-T22, T24-T28, T30, T31. 19 leaves are `opaque` placeholders
with exact statements in docstrings.

**Glue status.** Lean top theorem `HSyn.sixContactMin_of_leaves` = `glueOutputs_of_leaves`
(`sorry`: G1-G17, G19) + glue-assembly's proved `GlueOutputs Mult.S_mul → SixContactMin`
(checked against the real `ZInQ.SixContactMin`; standard axioms). Also proved: B2-B3
(`GlueDescent.B3Q.b3_degree_le_QM`), B1/C1 algebra, Lemma PR(i) arithmetic, NoCM fibre, D1, D3,
level bound, F2/F3, Faltings and NOS consequences, `sq_principalUnits` (new here, from
glue-conductor).

**Biggest missing definitions.** Stable Faltings height (R18-R22); QM moduli scheme `Y₃` with
canonical model (R1-R3, R5); `J₁(N)` over ℚ (R16, R18); ℓ-adic conductors (R17); and any nonzero
abelian variety at all in Mathlib.

**Route.** P recommended; K (Khare–Wintenberger + Ribet, 20 research leaves) kept as fallback:
rv-routek found it sound after five repairs, but Ribet 1992's refereed status is unchecked and
route K is not shorter.

**Top risks.** Unverified locators (Pan JAMS numbering, Carayol at `p | N`, journal versions of
Baba–Granath, Lin–Yang, and the model-read Arakelov papers; QM dichotomy needs a locator); leaves
in consequence form that must not exceed print (Pan's trace reading, finite-level reduction
theory, T27); unreviewed definitions (three copies of the abelian-variety layer to merge);
Glazer's and the repository's glue has only model reviews; `GlueOutputs` is a numerical contract,
not a leaf.

**Reports included:** all eleven (pkg-I1, pkg-I2, pkg-I3, pkg-I4, pkg-I5, pkg-I6, glue-descent,
glue-conductor, glue-assembly, glue-repo, rv-routek) plus hdec-faithful, hdec-elementary,
hdec-alt. pkg-I5's Lean (special-case leaves) is cited but not copied into `Leaves.lean`.

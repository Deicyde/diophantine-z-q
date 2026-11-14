# leaf-review-a (2026-11-13): statement review of leaf-fold3's groups A, A′, F

**Main result.** I reviewed all 21 fields: the 14 Shimura-curve/QM leaves of group A, the 2 theta-function
leaves of group A′ and the 5 modular-Galois-representation leaves of group F of
`HDec.HSyn.sixContactMin_of_open3` (leaf-fold3). Each Lean statement was read against its cited source,
together with every definition it uses. **All 21 come out CONSEQUENCE**: each follows from the cited
published theorems by a short derivation, written out in the report. None is STRONGER-THAN-SOURCE or
NOT-A-PUBLISHED-STATEMENT, so no statement repair is proposed. The report is
`docs/research/leaf-review-a.md`; §2 has the table, §§3-5 one derivation per field. Theorem numbers
are from memory and marked UNVERIFIED.

**Findings that do not change a verdict.**
- Docstring error, not a statement error: `QMDenZeroCM3` says `jDen(Ω(i√3))` vanishes to order 30.
  The order is 10, computed: `Σθ⁸` and `∏θ²` both vanish to order 2 there. The report proposes
  corrected docstring text (§1(d)); it is not applied.
- Standing caveats, already in the docstrings: the published locators of Lemma QP; the human check
  of R1's PEL specialization; and existential witness forms (`r1r2`, `y3Connected`, `x6ConicModel`,
  and `r1b` on the `Classical.choice` triple), which are false rather than vacuous if a clause list
  were unsatisfiable.

**What compiles.** `scratch/leaf-review-a/Check.lean` `#print`s the kernel copies of `R16_EichlerShimuraJ1'`,
`CarayolR17'`, `PkgI4.EigenformTwist`, `R1rec`, `R5fp`, `R5fpCount` and `R03_LinYang`. Under
`lake env lean` it exits 0 with 0 errors in 133 s.

Numerical checks (Python/mpmath, no network):
- `py/theta_mod_check.py`: R4's two transformation laws hold to at least 24 digits for 5 symplectic
  matrices.
- `py/hauptmodul_check.py`: `Ω(τ)` is a valid period matrix; `j_θ` is invariant under Atkin–Lehner
  elements; the CM values are 0 and −16/27; the orders at `P₋₃` are as stated in the first finding.
- `py/linyang_tuple_check.py`: R3's tuple is Igusa's `J`-tuple.

**Declarations proved.** None (review task). There are no new files under `ZInQKernel/` and no edits
to existing files.

**What remains.**
- Confirm the UNVERIFIED theorem numbers against the literature: Deligne–Serre Thm 4.1; Carayol
  Théorème (A); Shimura 1973 Thm 1; González–Rotger Thm 5.12 and Prop. 5.6; Baba–Granath Thm 2.1;
  Lin–Yang Ex. 29.
- Two numerical facts behind `qmHauptmodul` (the order of `∏θ²` at `P₋₃` and the exact value −16/27)
  are computed, not cited.
- Not compiled: which copy of `B` and `O` the names in `FS5NoCM.CMOptimalEmbedding` resolve to. All
  copies have the same meaning.

Files: `docs/research/leaf-review-a.md`, `scratch/leaf-review-a/{log.md, Check.lean, check_out.txt,
notes_A1.md, notes_A2.md, py/*.py}`.

# raynaud-proof: Raynaud's criterion (`raynaudSemistableSH`) is not dischargeable from the bundles; the live proof needs only its char-0, algebraically-closed-residue-field form

Task raynaud-proof, 2026-11-16. Base 0caafe66 (origin/main, top module `TailZ42`, `sixContactMin_of_open35`). Model
work, no human review. No network: every SGA 7 / BLR / Serre–Tate number below is recalled and UNVERIFIED unless it
cites a file.

Marks: **VERIFIED** (compiled, read in a file, or found by grep), **STANDARD** (published, reference given),
**SPECULATIVE** (my argument), **UNVERIFIED** (a theorem number or wording from memory).

## 1. Verdict

1. **The field `raynaudSemistableSH` cannot be removed with no new leaf.** No field of the current bundles, and nothing
   proved in `ZInQKernel/`, supplies the monodromy input that SGA 7 IX 4.7 needs (§2). Target −1 not reached; the
   count is unchanged.
2. **Narrowing, proved in Lean (VERIFIED, compiles, standard axioms).** Every use of the field in the live proof goes
   through the restricted printed form `ReductB.RaynaudSemistableSHcp` (TailZ23 L305): the field with `[CharZero K]`
   and `[PerfectField κ(O)]` added. Since `κ(O)` is also separably closed, the second condition means `κ(O)` is
   algebraically closed. `RaynaudCP.consumers_of_cp` proves both consumers from it and the other fields of the
   current top bundles, without reading `r.raynaudSemistableSH`. The consumers are r6 at number fields
   (`RaynaudCriterionNF`) and SS1 with SS3 (`SemistableReductionThm ∧ SemistablePersists`).
   File: `ZInQKernel/Contrib/OneProof/RaynaudSemistableCP.lean`.
3. **What the narrowing buys.** The row's only flagged risk is "the print may assume an algebraically closed residue
   field". It goes away: the cp form is the print restricted to characteristic 0 under either reading of the base. The
   `k(s)`-versus-`κ̄` reading of "semistable" also goes away, since `κ(O)` is algebraically closed (§4). One recorded
   risk remains: the `m = 3` boundary (locators.md R6). The live proof uses 4.7 at `m = 3` (§3.3), so that risk
   cannot be narrowed away.
4. **The fold is not an autofold.** The cp leaf is weaker than the field, so `autofold.py` cannot fold it. A
   weaker-leaf bypass fold (threading plus prune) is needed; the recipe is in §5. `scratch/raynaud-proof/autofold.json`
   records this and holds the row data for the replacement leaf.

Rating of the replacement leaf `ReductB.RaynaudSemistableSHcp`: **printed form (specialization of SGA 7 IX 4.7)**,
unread, with the remaining reading risk at `m = 3` (R6). It is not a new statement: reduct-b put it in the tree
(TailZ23), and neron-dvr's `GapNeron.ss1_ss3_of_cp_fullNF` already consumes it.

## 2. Why the field is not provable from the bundles

The standard proof of 4.7 (SGA 7 IX §4; UNVERIFIED numbers) has four steps.

1. Inertia acts quasi-unipotently on `T_ℓ`. This is Grothendieck's ℓ-adic monodromy theorem (SGA 7 IX 4.3 /
   Serre–Tate 1968 Appendix), or the semistable reduction theorem 3.6 with 3.5.
2. `A[m] ⊆ A(K)` with `m ≥ 3` makes `σ ≡ 1 mod m`. Serre's lemma then makes `σ` unipotent on `T_ℓ` for `ℓ | m`.
3. "Unipotent on `T_ℓ` for one `ℓ` implies semistable" is the **converse** direction of 3.5. Its proof goes through
   Grothendieck's orthogonality theorem (IX 2.4) on the Néron model's toric, abelian and unipotent parts.
4. Alternatively, Raynaud's argument runs on the special fibre of `N_L⁰` for `L/K` semistable, with
   `Gal(L/K)` acting trivially on its `m`-torsion. It uses Edixhoven-type fixed points of a Weil restriction.

Fields of the current bundles checked (VERIFIED by reading `TailZ41`/`TailZ42` and OPEN.md):

| field | content | gives a piece of 4.7? |
| --- | --- | --- |
| `sga7_IX_3_5_ForwardGeom` | semistable ⇒ `(σ-1)² = 0` on `T_ℓ` | no: forward direction; 4.7 needs the converse (step 3) |
| `sga7_IX_3_3_SH` | semistable ⇒ `N⁰ ×_S S' ≅ N'⁰` | no: assumes semistability |
| `r7a` (Serre–Tate Thm 1, NOS) | good reduction ⟺ inertia trivial on `A[m]` for all (or infinitely many) `m` | no: one `m` gives nothing; good ⊊ semistable |
| `neronBaseChangeStrictHenselization`, `sga3_VIB_3_10`, `neronSchemeExtensionExists` (textbook) | Néron-model existence, base change, `G⁰` open | structure only, no monodromy |
| `mumfordTorsionAlgClosed`, `geomConnOfRationalPoint`, `cartierSmooth` (textbook) | torsion count, connectedness, smoothness | no |
| `r9a`, `r9b` (Faltings) | semisimplicity, Tate conjecture over number fields | no |

Nothing in the tree states quasi-unipotence, 3.6, or the converse of 3.5 as a field.
`PkgI2.GrothendieckMonodromy` (r8) is dead (neron-dvr §), and the chain derived it from 3.6, which comes from 4.7
by K1 (VERIFIED: `grothendieckMonodromy_final'`, `semistableReductionDVR_of_raynaud`). So 4.7 is the only source
of monodromy information in the proof.

**Smallest missing input.** The smallest single Prop that discharges the field together with the bundles is 4.7
itself. Every decomposition I found replaces it by at least two published leaves:

* 3.6 together with the converse of 3.5;
* quasi-unipotence together with the converse of 3.5;
* Grothendieck's ℓ-independence of the inertia characteristic polynomial, used for the all-`ℓ` conclusion that r6
  needs.

So the minimal missing input is `RaynaudSemistableSHcp`, restricted as far as the consumers allow (§3).

## 3. The consumers (VERIFIED by grep over `ZInQKernel/`; `scratch/raynaud-proof/FieldUse.lean` for the closure check)

### 3.1 Readers of the field

`.raynaudSemistableSH` is read once, at TailZ23 L722 (`raynaudSemistable_of14`, through
`ReductB.raynaudSemistable_of_SH_pair`). Every other occurrence is a pass-through `raynaudSemistableSH :=
n.raynaudSemistableSH` in a generation map. `raynaudSemistable_of14` has two readers:

* `raynaudCriterionNF_of14` (TailZ26 L171) → `GapNeron.raynaudCriterion_leavesNF`. This applies 4.7 at a number
  field `K` and a DVR of `K`.
* `semistableReductionDVR_of14` (TailZ23 L727, K1) → only `ss1_ss3_of14NF` (TailZ26 L179) → `GapNeron.ss1_ss3_of_cpNF`.
  This uses it only through `reductionNF_of_general`, at number fields.

Both feed `sixContactMin_of_open20` (TailZ26 L188) as its arguments `h6` and `hSS`.

### 3.2 What generality is used

At a number field, `StrictHenselizationPair` passes to a strictly henselian `E ⊇ K`. `E` has characteristic 0, and its
residue field is a separable algebraic extension of a finite field, so it is algebraically closed. reduct-b's
`raynaudSemistableCP_of_SH` and `perfectField_residue_nf` (TailZ23) are exactly this step. So the live proof uses
4.7 only over strictly henselian DVRs of characteristic 0 with algebraically closed residue field.

### 3.3 The `m = 3` boundary cannot be narrowed away

* r6 is applied at `m = 3`:
  * by A6 (`goodReduction_of_QM_rational3_of_alg`, LPrefix L853: `hRay K O w hw A 3 le_rfl … 3 …`);
  * by TailH (`torsFixWildE_of_twist`, L3131: `torsFix_of_descent … 3 le_rfl …`).
* r6's conclusion is for **every** `ℓ ≠ p`. From 4.7 at `m ≥ 4` one can reach `m = 3` only at `ℓ = 3`. The route
  is `K(A[9])`, `σ³ ∈ I_{K(A[9])}`, and a Serre-type lemma (SPECULATIVE argument, not formalized). Other `ℓ` would
  need ℓ-independence or the converse of 3.5.
* So an `m ≥ 4` leaf would require re-proving r6's consumers (A6 and about ten theorems in TailH) with a narrower r6.
  I did not pursue it. The R6 locator row flags the boundary ("Do not silently close this boundary case"); it stays
  open.
* K1 (SS1) could use `m ∈ {4, 5}` instead of `{3, 4}` (one of 4 and 5 is a unit in any local ring). It is not the
  binding use.

### 3.4 The abelian varieties actually used

* r6 is consumed for:
  * QM abelian surfaces (A6, `m = 3`, `ℓ = 3`);
  * general abelian varieties over number fields at many `ℓ` (TailH `raynaudPlace_of_R6`, `tateWildK_of_R6`,
    `localGlue_of_leaves`).
* SS1 is the stable-height semistable reduction theorem for every abelian variety over a number field
  (`HeightSplit.SemistableReductionThm`, TailY L134).

So narrowing to "the abelian varieties actually used" does not help. For the QM surfaces alone, potentially good
reduction still needs the same monodromy input.

## 4. Rating of `RaynaudSemistableSHcp` (printed form)

* **Base.** If SGA 7 IX 4.7 is printed over an arbitrary strictly henselian trait, the cp form is a specialization
  (`RaynaudCP.raynaudSemistableSHcp_of_SH`, VERIFIED). If it is printed with an algebraically closed residue field,
  the cp form is the print restricted to `char K = 0`. Either way the leaf is the print or a consequence of it.
* **Meaning of "semistable".** The Lean conclusion `SemistableNeronModels A O` reads semistability on
  `𝒩 ×_O κ̄`. With `κ = κ(O)` algebraically closed, `κ → κ̄` is an isomorphism, so the `k(s)` reading and the
  geometric reading agree. The transport along a field isomorphism is reduct-glue's proved
  `ReductGlue.semiAbelianFieldIsoInvariant` (TailZ14 L1055). A torus over an algebraically closed field is split. So
  the dict-models disjunction (`RaynaudSemistableSHOr`) is not needed for the cp form. (SPECULATIVE as a dictionary
  statement; the transport lemma is VERIFIED Lean.)
* **Remaining risks.**
  * The `m = 3` boundary (locators.md R6: Silverberg–Zarhin, AIF 45 (1995) Thm 3.5 citing SGA 7 IX 4.7; the
    threshold looks like `> 3` in extraction).
  * The print may state a Galois-form conclusion. That is unchanged from the old row and is low risk, because
    SGA 7 IX defines semistable reduction by the Néron model (UNVERIFIED).
* Suggested kinds.tsv row: kind `published`, strict LEAF, flag
  `reading risk: m = 3 boundary unread (locators.md R6); locator UNVERIFIED (SGA 7 I Exp. IX Prop. 4.7, restricted to char 0 and algebraically closed residue field)`.

## 5. Fold recipe for the integrator (weaker-leaf bypass; not `autofold.py`)

`autofold.py` discharges a field with a proof of the field's own type, and no proof of `RaynaudSemistableSH` from
the cp leaf exists. The fold therefore follows the sem-prune/yu-prune pattern:

1. **Thread.** Add binders `(h6 : PkgI2.RaynaudCriterionNF.{0})` and
   `(hSS : ZInQ.HeightSplit.SemistableReductionThm ∧ ZInQ.HeightSplit.SemistablePersists)` to
   `sixContactMin_of_open20` … `sixContactMin_of_open35`, in place of the computation in `open20` (TailZ26
   L191-195). The terms `raynaudCriterionNF_of14 …` and `ss1_ss3_of14NF …` are the only readers of the field.
2. **Prune.** `raynaudSemistableSH` is now unread in every generation. Drop it from `OpenResearchLeaves14` …
   `OpenResearchLeaves26` and from their maps (PruneScan; `ReductB.raynaudSemistable_of_SH_pair` and
   `raynaudSemistable_of14`, `semistableReductionDVR_of14` become dead readers).
3. **New top.** Create `OpenResearchLeaves27` with the field `raynaudSemistableSHcp : _root_.ReductB.RaynaudSemistableSHcp`
   in place of `raynaudSemistableSH`. The top supplies `h6` and `hSS` with
   `(_root_.RaynaudCP.consumers_of_cp r.raynaudSemistableSHcp r' t l).1` and `.2`. Here `r'` stands for the other
   fields: `consumers_of_cp` takes an `OpenResearchLeaves26` only to read `neronBaseChangeStrictHenselization`,
   `sga7_IX_3_5_ForwardGeom`, `sga3_VIB_3_10` and `sga7_IX_3_3_SH`. After the prune use `consumers_of_cp_leaves`
   with those four fields and `t.neronSchemeExtensionExists`, `t.mumfordTorsionAlgClosed`,
   `t.geomConnOfRationalPoint`, `l.egaIV_8_10_5_xii`, as in `consumers_of_cp`'s body.
4. **Counts.** One LEAF row replaced by one LEAF row: strict and strictest unchanged. The row's flag changes from
   "algebraically closed residue field" to the R6 `m = 3` risk.

If dict-models' fold (`raynaudSemistableSH` → `RaynaudSemistableSHOr`) lands first, the same recipe applies to
`raynaudSemistableSHOr`. `consumers_of_cp_leaves` does not mention either form. If dict-models' `BLR_7_2_1` replaces
`neronBaseChangeStrictHenselization`, pass `neronBaseChangeStrictHenselization_of_BLR72 …` where step 3 reads that field.

## 6. Lean (VERIFIED)

`ZInQKernel/Contrib/OneProof/RaynaudSemistableCP.lean` (imports `ZInQKernel.OneProof.H.TailZ42`, namespace `RaynaudCP`):

| constant | statement |
| --- | --- |
| `raynaudSemistableSHcp_of_SH` | `RaynaudSemistableSH → RaynaudSemistableSHcp` (the new input is no stronger) |
| `RaynaudSemistableNF` (def) | `ReductSplit.RaynaudSemistable` with `[NumberField K]` |
| `raynaudSemistableNF_of_general`, `raynaudSemistableNF_of_CP`, `raynaudSemistableNF_of_SHcp` | the NF form from the general, CP, SHcp forms |
| `raynaudCriterion_of_leavesNF_cp` | `GapNeron.raynaudCriterion_of_leavesNF` with `hR : RaynaudSemistableNF` |
| `raynaudCriterion_leavesNF_cp` | r6 at number fields from `RaynaudSemistableSHcp`, the pair, `SemistableUnipotent`, N1, Mumford, `[m]` étale |
| `consumers_of_cp_leaves` | `RaynaudCriterionNF ∧ (SS1 ∧ SS3)` from the cp leaf and the other inputs as hypotheses |
| `consumers_of_cp` | the same from the cp leaf and `OpenResearchLeaves26`, `OpenTextbookLeaves12`, `OpenAddedLeaves17` (field `raynaudSemistableSH` not read) |

Compile, axioms and `#discharges` output: §7.

## 7. Checks (VERIFIED; outputs in `scratch/raynaud-proof/`)

* `lake build +ZInQKernel.Contrib.OneProof.RaynaudSemistableCP +ZInQKernel.OneProof.Discharges`: "Build completed
  successfully (12999 jobs)"; then `lake build +ZInQKernel.OneProof.Main`: "Build completed successfully (13697 jobs)".
* `#discharges` (`DischargesCheck.lean`, output `discharges-output.txt`): `56 open hypotheses, 2871 theorems checked,
  7 discharge one`. None of the seven is in `RaynaudCP`: as expected, no theorem of this file proves an open
  hypothesis, because the field is not discharged. Axioms of `consumers_of_cp`, `consumers_of_cp_leaves` and
  `raynaudSemistableSHcp_of_SH`: `[propext, Classical.choice, Quot.sound]`.
* Verbatim statement check (`Statements.lean`, output `statements-output.txt`): copies of `RaynaudSemistableSH` and
  `RaynaudSemistableSHcp` are `rfl`-equal to the originals; exit 0.
* Closure probe (`FieldUse.lean`, output `fielduse-output.txt`, about 3 min): the closure of
  `ZInQ.OneProof.frozenTarget` has 259,583 constants. Those that mention `ReductGlue.RaynaudSemistableSH` or any
  projection `OpenResearchLeavesN.raynaudSemistableSH` are:
  * the constructors `OpenResearchLeaves14.mk` … `26.mk`;
  * the pass-through maps `openResearchLeaves14_of_…15` … `25_of_…26`;
  * `HDec.HSyn.raynaudSemistable_of14`;
  * the two lemmas taking the leaf as a hypothesis, `ReductB.raynaudSemistable_of_SH_pair` and
    `ReductGlue.raynaudSemistable_of_SH'`.

  So `raynaudSemistable_of14` is the only reader. Its readers (grep) are `raynaudCriterionNF_of14` and
  `semistableReductionDVR_of14`, and the latter is read only by `ss1_ss3_of14NF`. These are exactly the two
  conclusions `consumers_of_cp` provides.

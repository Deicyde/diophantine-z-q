# Preliminary non-author source coverage and consumer reconciliation

Date: 2026-11-10. Reviewer: Codex subagent `/root/source_inventory`, distinct from the contribution author. Configured/requested model: `gpt-6-astra`. The serving-model identity and controller eligibility are not established by trusted run records in this report. Prepared head: `37a65df0b8f815b6c10c00bdf85f01e2b0c2860f`.

This is an informal, bounded source review under the evidence structure of Protocol_D v1.4. It is **not** protected Astra/controller acceptance, a new Lean replay, independent kernel certification, assembled-main-theorem acceptance, or release authorization. The applicable Astra policy requires trusted controller run records; a report cannot supply those records itself.

The unchanged initial inventory is [SOURCE_USE_INITIAL.md](SOURCE_USE_INITIAL.md), SHA-256 `598260344053fa4433ef792a60f7152d5f9e1043ce4af0840adc20aedf38ca08`. It was frozen before reading TARGETS, APPLICATION, ORIGIN, README, FINDINGS, policy records or source maps. Initial exposure was the task prompt and inherited generic context, not earlier favorable reports. Stage B exposure adds these declared inventories and the actual V13/V14 manuscript passages. Earlier reviewer verdicts were not used as proof. Stage A's generic-context exposure means this is source-first, not a claim of perfect blindness.

The accompanying validation receipt incorporates the reviewer’s machine-readable bindings and contains exact raw-byte SHA-256 bindings, all 57 declaration sites and passage hashes, per-declaration source uses, all dependency pins, and each V13/V14 passage comparison. Repository paths below are relative to the repository root; no local path is required to reconstruct this report. The initial inventory uses portable repository paths; its source names and hashes identify the inputs without requiring a local filesystem layout.

## Distinct decisions

**Informal Lean-source coverage:** all four complete sources were read, including imports, variables, structures, definitions and proof bodies. All 41 declared proof roots and all 16 printed definitions match the 57 independently reconstructed declarations, without omission or extra target. Their substantive source uses have identified suppliers or displayed inline derivations. This is satisfactory preliminary coverage of the bounded conditional interfaces. It is not an exhaustive elaborated constant/axiom graph. A small supplier-map omission is recorded below and corrected by this supplementary index, without changing the frozen package.

**Informal manuscript mapping:** L1/L2/B1/O1/O2 accurately describe conditional interfaces relevant to the inspected V13 consumers, with the finite-stage, coefficient-carrier, trace, sign and supplied-inverse restrictions stated in APPLICATION. The corresponding V14 passages have identical bytes at shifted locations; no change to these interface statements is indicated. This decision accepts relevance and contract fidelity only. Arithmetic realization of those contracts and global consequences remain outside this review. A minor locator omission is preserved below.

**Protected decision:** unestablished. Neither preliminary decision satisfies the designated-controller acceptance requirement. No main-theorem protocol closure is claimed.

## Scope and graph reconciliation

The coverage index in the accompanying validation receipt covers every explicit declaration and its body through the next declaration boundary (or EOF), alongside the initial source-use entry. Imports and shared contexts were reviewed as part of each complete file. Comments, namespace delimiters and attributes supply notation/provenance rather than additional mathematical conclusions. Structures expose supplied assumptions rather than proving their arithmetic occurrence. Generated field projections and recursors are not separately announced claims.

TARGETS is a root/definition inventory, not a direct dependency graph. APPLICATION's L1/L2/B1/O1/O2 table and ORIGIN's import list are the declared application and module edges. The initial table supplies the direct internal proof-use detail absent from that coarse map; its entries must not be replaced by transitive ancestry. Each initial entry is carried verbatim into the validation receipt reconciliation. No separate direct-use graph was found within the selected package.

| Declared edge or family | Reconciliation and extra-edge disposition |
| --- | --- |
| Transport → End, Subgroup, Group | Genuine algebraic representation, normal-subgroup conjugation and group-normalization uses. Ordinary linear/group laws, inductions and arithmetic rewrites are inline proof infrastructure, with the precise substantive internal lemmas listed individually in the initial table. |
| H1 → Transport | Genuine original/conjugate coordinate and crossed-cocycle derivations; no reverse dependency. |
| H1 → LowDegree | Genuine cocycle equation, actual H1 projection, kernel characterization and representative induction. |
| H1 → Isomorphisms | Genuine quotient descent and evaluation; source-map omission R01 below. |
| Cup → Isomorphisms | Broad import providing linear algebra environment; cup proofs do not invoke the specialized quotient-descent theorem. Do not claim such a theorem application merely because the module is imported. |
| Comparison → Homotopy, Abel | Genuine composition/induced homology suppliers and abelian normalization of degreewise identities. |
| L1 → L2 | Genuine reduction to representatives using the projected evaluation/pullback formulas, not identification of coefficient carriers. |
| B1 → paired-functional/switch | Conditional intended use. The helper itself does not construct a Selmer cup or PD. |
| O1 → O2 | Compatible intended construction route, not a Lean theorem that automatically assembles O1 into O2; O2 separately receives genuine chain maps and right-inverse homotopy. |
| Historical DERIVATION links / Nekovář sections | Attribution and construction context, expressly not additional audited roots or fresh acceptance of all arithmetic claims. Published-source hypotheses are not newly checked here; no conditional algebra proof relies on an unexamined appeal to those sections. |
| Downstream determinant / lower bound / inner limit | Consumer context and remaining arithmetic obligations, not conclusions of these four modules. |

ORIGIN's four hashes and exact imports agree with the examined files. Both OpenMath source maps name the same four hashes; their root-package manifest rename is declared, not a mathematical supplier change. This review checks source-map identity only, not generated-support execution or imported binary authentication. Historical commit/PR state fields in ORIGIN are dated provenance, not current service-state claims. The 39-target foundation is outside the imports and acceptance scope.

## Available / needed / bridge

| Transition | Available from actual sources | Needed by consumer | Bridge and status |
| --- | --- | --- | --- |
| L1 group data → coordinate transport | `LocalData` plus crossed equation; explicit u=alpha(d) inverse; trivial finite/inertia actions. | One shared unit for every retained cocycle; exact tame relation in same group. | `crossed_conjugation`, trivial-action powers and conjugation identities derive (u f,u ell s). No scalar-transport conclusion is assumed. Source derivation checked. |
| L1 → minus-one | Equality (ell:R)=-1 supplied. | Finite retained H12 precision and compatible arithmetic group/character. | Ring rewriting gives (u f,-u s), including characteristic two and zero coordinates. H12 supplies congruence context, but actual LocalData realization/common quotient is external to helper. No fixed natural ell equals -1 in characteristic zero. |
| Cocycle → actual H1 | Mathlib cocycles as kernel, coboundaries as range, H1π kernel theorem and representative induction; evaluation/pullback kill kernel. | Well-defined linear maps on actual H1 with original and conjugate carriers distinguished. | `liftOfSurjective` and its computation theorem descend; H1 induction proves transport. Checked supplier definitions and proof. Continuous arithmetic identification/finite diagrams and limiting compatibility remain external. |
| B1 cone cycle → cup correction | Closed l; two Leibniz identities; cycle inc=loc+dq_N. | Exact correction of localCondition to localGlobal. | d(l cup q_N)=-l cup dq_N and bilinearity. Explicit negative correction; checked algebra. |
| Correction → equal traces / boundary invariance | One linear trace killing dt; appropriate other slot closed. | Same arithmetic trace/pairing on both functionals. | Linearity kills correction; other Leibniz equation treats first slot. Arithmetic trace square, cup construction and coefficient J once remain external. |
| H22 → alternate cone sign | H22 loc-inc-dq_H; comparison q_H↦q_H+hu. | Boundary convention -loc+inc-dq_N. | q_N=-q_H gives inc=loc+dq_N and comparison q_N↦q_N-hu. Coordinate identity checked; not a full cone-isomorphism construction. |
| O1 → degreewise comparison | Supplied ha and inc-inc'a=dh+hd. | Differential commutation, same global coordinate. | Expand third components and additive cancellation; both other components follow ha/rfl. Actual all-degree arithmetic chain-map assembly remains external. |
| O2 → preserved localized homology | hj:j≫q=p and supplied hk:k≫j homotopic to id D. | Orthogonal lift has same global/localized class as conjugate transport. | Postcompose hk with q, substitute hj; postcompose localization; Mathlib homotopy induces equal homology maps. No left inverse needed. Existence/identification of arithmetic k,hk remains external. |
| Local identities → determinant / bounds | Only conditional local transport, cup correction and comparison. | Actual retained functionals, integral lattices, strict factors, limiting diagrams and valuation comparison. | Not supplied here. V13 contains ordinary arguments at the recorded loci; this review does not call them absent or false, and does not certify them. |

No division by two, by a vector, or by a nilpotent deformation parameter is used in the four modules. LocalData's natural ell is not asserted prime. Probability/stopping-time obligations do not apply to these deterministic algebraic deductions; inverse-limit uniformity is deliberately not inferred from them.

## Exact consumer comparison

All eleven ORIGIN excerpt hashes match the preserved V13 bytes. Each corresponding V14 excerpt is byte-identical at **+773 lines**. Whole files differ, so this is a bounded consumer comparison, not a V14-wide equivalence or dependency review. Exact hashes/ranges are in the validation receipt.

| Consumer | V13 lines | V14 lines | Available source / appropriate interface boundary |
| --- | --- | --- | --- |
| conjugate-duality | 2898–2967 | 3671–3740 | Pullback coefficient system, Weil pairing with J once, orthogonal diagrams; L1/L2 do not establish global duality. |
| H12 | 3225–3233 | 3998–4006 | Tate Frobenius congruence and ell+1 divisibility; finite-stage input, not characteristic-zero hEll. |
| H20-H21 | 3339–3417 | 4112–4190 | Actual coefficient push, cocycle and boundary formulas, local triviality at derivative prime; arithmetic source for realizing L1/L2. |
| local-pairing | 3431–3508 | 4204–4281 | Finite tame model, transported pairing, comparison contractions/homotopies; relevant external data for B1/O1. |
| H22 | 3509–3542 | 4282–4315 | Finite continuous witnesses, cone equation and common finite quotient; L2/B1/O1 conditional interfaces. |
| paired-functional | 3842–4012 | 4615–4785 | Actual z-perp and PD functional plus localization/integral regimes; O2 relevant but inverse existence not provided by helper. |
| stored-coordinate | 4014–4029 | 4787–4802 | Class-functional determinant coordinate only, not stored-row construction; no matrix identification follows. |
| inner-limit | 4577–4636 | 5350–5409 | Finite models, finite-diagram contraction and retained limits; no such theorem in L1/L2. |
| derivative-switch | 5021–5093 | 5794–5866 | Truncated strict/relaxed conditions retaining D0 and determinant switch; helper covers only local compatibility. |
| lower-bound | 5095–5379 | 5868–6152 | Actual-class iteration, quadratic-sign and determinant consumers; not covered as a theorem. |
| derivative-orthogonal | 5351–5373 | 6124–6146 | Identity comparison at derivative conditions; arithmetic partner identification relevant to O2. |

The paired functional is defined at V13 3873–3891 (V14 4646–4664), with actual comparison/homotopies at V13 3979–3999 (V14 4752–4772). These identify the needed partner; V13 4014–4029 only names its determinant coordinate. The lower-bound passage explicitly retains characteristic-zero limits and signs, so L1's exact finite-ring specialization cannot be promoted to that passage without its retained-diagram argument. The derivative-prime identity comparison at V13 5351–5373 remains byte-identical in V14 6124–6146. No relevant passage difference was found; an upstream shift and other whole-file changes do not discharge missing arithmetic instantiation.

## Preserved discrepancies and minimal documentation correction

**R01 — substantive supplier name omitted from compact source paragraph.** APPLICATION names the LowDegree and Homotopy suppliers but omits `LinearMap.liftOfSurjective` and `LinearMap.equivOfSurjective_apply` from `Mathlib/LinearAlgebra/Isomorphisms.lean:159–172`. H1 uses these directly at lines 51–52, 58, 83–85 and 92. ORIGIN does include the module import, so this is a source-map granularity omission, not a hidden axiom or proof failure. Initial source reconstruction already located and checked their definitions. Minimal correction: append that exact supplier/use sentence in an additive supplement (this report does so); do not overwrite the historical package or prior verdict hashes. Any protected coverage decision must explicitly include this supplement.

**R02 — excerpt begins after theorem label.** The declared derivative-switch excerpt starts at V13 5021, while the lemma heading/label is at 5020 (V14 5793). Its contents and end cover the body/proof, but the frozen excerpt is not the whole labelled lemma. Minimal additive correction: identify 5020–5093 / 5793–5866 as the full lemma, preserving the original 5021–5093 excerpt hash. The full-lemma hash is recorded below. No mathematical repair is indicated.

**R03 — initial inventory wording precision.** The initial table's phrase “kernel replay” is an explicit non-claim; this reviewer did not replay Lean. Its final sentence asking Stage B to “inspect application evidence for each external obligation” does not enlarge scope into accepting all arithmetic source proofs. This report identifies source arguments and remaining proof boundaries, rather than classifying those arguments as unproved merely because not audited here.

No new mathematical contradiction was found in the bounded sources. Findings F01–F07 and F11 are independently supported as interface boundaries by the inspected proof bytes. F08–F09 are consistent with the actual functional and coordinate passages. F10/F12/F14 concern execution, provenance and trust: their historical reproduction assertions were not rerun or newly accepted in this source review. F13 is a scope exclusion, consistent with the selected imports. The frozen findings ledger remains untouched; R01–R03 are supplementary dated entries, not erased discrepancies.

## Limits and handoff

This review derived the conditional algebra from source rather than importing historical favorable conclusions. It checked selected actual Mathlib supplier definitions at revision `56a005855ea17e0b0958f73ec801ae140b0a1679` (Lean `v4.35.0`). Other dependency revisions are bound from the manifest; they were not independently replayed. The source-use inventory lists visible substantive proof dependencies, not every simp-generated constant. Manuscript passages were read to assess contracts and consumers, not to certify their published-source applications or all changed V14 dependencies. The Nekovář publication is contextual to the application record and was not newly source-audited in this task. Historical runner/control claims remain separate.

No proof, manuscript or frozen package was edited. No build caches were rebuilt; no jobs dispatched, commits made or remote messages sent. The remaining protected eligibility, exact-head controller decision, and any final submission/merge checks belong to the controlling process.

Full derivative-switch lemma SHA-256 (both editions, ranges above): `2f23916a10a7bf9724f702d575fd6cf620023d811730b77f4cbcc7a460d57680`.

## Four Lean source bindings

| Repository source | SHA-256 |
| --- | --- |
| `lean/Research/DerivativeSwitch/ConjugateLocalTransport.lean` | `8688eef27fcc89c02eb3ab270e5359534dc23ef16e11678bdb1dd3587e3f8b86` |
| `lean/Research/DerivativeSwitch/ConjugateLocalH1.lean` | `078ac50ae0c90c8e609a57c51c5884a25646ad7305531f1cf531617485b9078f` |
| `lean/Research/DerivativeSwitch/ActualBoundaryCup.lean` | `77bcdd2ae5283ffd6cc51062e452da4294fcd5b3d952940b588b2d5b52ecdd90` |
| `lean/Research/DerivativeSwitch/OrthogonalComparison.lean` | `bfec996b869e44c6a42fc058fbc24cc7288b1f61d0f0e7eef1f4f58f41dca1ba` |

V13 SHA-256: `9db71bbfcefb37db56eabcf40a5f9dd85de9ed58294635da3dbf6d4f5caa8fcd`.

V14 SHA-256: `5882a77003b9772b5b572a5ab2c2b2f8ce9fc53e1e368a3b69851c8a9b3bfcac`.

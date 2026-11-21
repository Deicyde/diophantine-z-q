rc-oldnew-proof: prove the printed-form leaf OldNewIndependenceWeightTwo (RC/EvenJoin/DistinctCuspColumns.lean) from the vendored newform library already in the tree, so the even inventory no longer rests on an unverified print (base: wip/rc-lane-batch-1120e at 9a60a98cd9bcca63c7bc283c58be01eb9952578d).

Why: the owner asked that the remaining inputs "can be reduced to well-known theorems". rc-even-inventory2 stated the old/new independence (the distinct dilations f(dτ) of normalized newforms f with d * level(f) ∣ N are linearly independent in S₂(Γ₁(N))) as one printed-form leaf. Its locators are unverified: Diamond–Shurman GTM 228 Thm 5.8.3, and Atkin–Lehner 1970 Thm 5 for trivial character. Li 1975 does not prove it; Li's Thm 5, p. 298, is strong multiplicity one. Since then, the tree proved Li's strong multiplicity one at weight two from the vendored TauCeti backport (Newform.level_eq_and_coe_eq_of_forall_notMem_prime_eigenvalue_eq in ZInQKernel/Contrib/TauCeti/Backport/NumberTheory/ModularForms/Newforms/StrongMultiplicityOne/Across.lean). The same library has the old/new splitting at a prime. If this run proves the leaf, the inventory has no printed input left and the locator drops off the reading list. The project claims it on fork issue #83.
Do not overlap: rc-even-inventory3 and rc-even-inventory4 (the even inventory's SourceAttachment and Whittaker comparison) and the hcm lanes. Import existing modules; do not edit them.

Setup: git fetch origin wip/rc-lane-batch-1120e. Create branch wip/rc-oldnew-proof at 9a60a98cd9bcca63c7bc283c58be01eb9952578d. Your files go under ZInQKernel/Contrib/OneProof/RC/EvenJoin/ (new files only, for example OldNewProof.lean).

What exists (read first):
- RC/EvenJoin/DistinctCuspColumns.lean: NormalizedCuspSource (level, level_ne, newform : Newform level 2), CuspDilation N (source, degree, divides : degree * source.level ∣ N), CuspDilation.form, coeff_form (q-expansion of the dilation is Odd.divCoeff of the source's), the leaf OldNewIndependenceWeightTwo : ∀ (N : ℕ) [NeZero N], LinearIndependent ℂ (fun x : CuspDilation N => x.form), and its consumer cuspDilation_coeff_independent. Consumers in ExactInventory, PlacedBudget, PlacedDeterminant, PlacedDiamond, PlacedInventory, PlacedModel, PlacedSeed and PlacedTrace take it as hLi.
- The vendored library under ZInQKernel/Contrib/TauCeti/Backport/NumberTheory/ModularForms/:
  - Newforms/Basic.lean: cuspFormsOldOf, levelRaise_mem_cuspFormsOldOf, and the new space as the Petersson orthogonal complement of the old space.
  - Newforms/OldAtPrime.lean: cuspFormsOldAt, cuspFormsNewAt, isCompl_cuspFormsOldAt_cuspFormsNewAt, levelRaise_mem_cuspFormsNewAt.
  - Newforms/PrimeDecomposition.lean: exists_eq_sum_levelRaise_prime_of_forall_coprime_qExpansion_coeff_eq_zero.
  - Newforms/StrongMultiplicityOne/Across.lean: strong multiplicity one within and across levels.
  - Degeneracy.lean: the level-raising maps.
- The tree's eigenvalue-away-from-level API used by Across.lean (toEigenformAwayFromLevel, qExpansion_coeff_eq_eigenvalue).
- The manuscript, diophantine_zq.tex: 9649-9654 and 9754-9764 (the constituent inventory that uses the independence).

Your work:
1. Size first, in scratch/rc-oldnew-proof/log.md: the exact leaf, what the vendored library proves toward it, and which route below fits it.
2. Prove oldNewIndependenceWeightTwo_proved : OldNewIndependenceWeightTwo, with exactly that type and no extra hypothesis. One standard route, for guidance only:
   (a) Separate eigensystems. For a prime p ∤ N, the dilation f(dτ) with d * level(f) ∣ N has the same T_p-eigenvalue a_p(f) as f. By strong multiplicity one across levels (Across.lean), distinct normalized newforms of levels dividing N differ at infinitely many such p. A linear relation therefore splits into relations among the dilations of a single newform, by the usual Vandermonde or eigenvector argument over finitely many p.
   (b) For one newform f of level L, the forms f(dτ) for d ∣ N/L are independent by q-expansions. The expansion of f(dτ) starts with q^d, since a_1(f) = 1, so leading exponents separate them (use coeff_form and Odd.divCoeff).
   If the library's old/new splitting gives a shorter proof, use it. Prove that CuspDilation N → form is injective as part of linear independence; do not assume it.
3. Rewire: give the consumer theorems with hLi discharged, as new theorems in new files (for example cuspInventory_proved and the Placed* conclusions with the leaf supplied by oldNewIndependenceWeightTwo_proved). Change no existing statement.
4. Stop rule: if step 2 needs anything beyond the vendored library and Mathlib (for example Hecke operators T_p on S₂(Γ₁(N)) commuting with dilations, if the tree lacks them), build only the minimal faithful pieces. If a large piece remains, stop with the smallest missing statement as a named Prop with its size, and say what follows once it exists. Do not add a print: this run adds no printed leaf.
Out of scope for this run: everything in the even inventory other than this leaf; editing existing files.
Prints: none.

RESOURCE LIMITS (hard rules; breaking one fails your task):
- At most ONE Lean process (lean, lake, repl, or a pytest run that starts real Lean) at a time. Never start Lean jobs in the background with &, xargs -P, or shards.
- A Lean REPL session gets at most 10 commands, then restart it. Or send the header once and pass "env" on later commands so it doesn't re-import.
- Check `uptime` and `sysctl vm.swapusage` before every Lean or pytest run. If load is above 40 or swap used is above 8 GB, don't start it; report that you were blocked.
- Ground-truth or differential checks use a sample of at most 30 inputs, run one after another.
Host note (devserver): check `uptime` and `free -g` instead of vm.swapusage; hold Lean only above load 120 or below 20 GB available memory; do not sleep and poll. Run Lean under MemoryMax 60G. Run one lake command at a time, never two in parallel, and never a check while a build runs.

The owner's rules: follow the manuscript (diophantine_zq.tex) first, then the literature it cites. Label any step that is in neither as on-the-spot (provenance (c)) in the report. Reuse the statements already in the tree and add no print. No network is needed and you have none: mark page and theorem numbers you give from memory UNVERIFIED. If a source has a known issue, document it. Report any error you find in the manuscript or a source at once, first in the report and in .fleet/rc-oldnew-proof.md.

Hygiene, for everything bound for the fork (Lean, report, commit messages): no session names, host names or user paths. Write paths relative to the repository root, and refer to people by role ("the lead", "the reviewer").

The stop rule, for this unattended run: if a step needs a large missing theory, build only the minimal faithful pieces the next step needs. Otherwise finish what can be finished and write a scoped report: what is missing, how large it is, the smallest faithful statement of it, and what would follow once it exists. Never add a leaf, and never weaken a statement to make it provable.

Deliverables: new files only, under ZInQKernel/Contrib/OneProof/RC/EvenJoin/. Never import ZInQKernel.OneProof.Main, and edit nothing outside that directory except the report, .fleet/rc-oldnew-proof.md and scratch/rc-oldnew-proof/. Do not use local notation; write abbreviations with explicit arguments (the merge rule blocks local notation). Compile each file with lake env lean (one Lean process at a time), with no sorry and no axiom. Run #print axioms of each new theorem from a check file under scratch/rc-oldnew-proof/, not in the deliverable files (only propext, Classical.choice and Quot.sound), and list the results in the report. The report docs/research/rc-oldnew-proof.md needs:
- the main result, or the scoped stop, first;
- the statement of each new theorem, and which input it supplies;
- the exact list of remaining hypotheses with their owners;
- a Known-issues section;
- a section "Manuscript check": one line per manuscript step you formalize or rely on, with its tex lines and one verdict: OK (right as written), gap filled (what was missing), error (what is wrong), or unverified (why).
Commit as you go (after each step that compiles). Commit and push your branch wip/rc-oldnew-proof (only that branch) with the report; give the final SHA in your last message.

Build note (read before compiling): the worktree's .lake was copied from a build of the fork's main, so modules that exist only on your base branch (or arrive with your merge) have no .olean yet, and lake env lean on a file that imports them stops with a missing-object error. Before checking your own files, build their imports once with lake build <Module> for each module your files import (one Lean process at a time; let each finish), then compile your files. Never report a file as unchecked because an import was not built: build it. Report any file that still fails, with the error. One Lean process at a time means one lake command at a time: let each lake build or lake env lean finish before starting the next, never run two in parallel, and never start a check while a build is running.

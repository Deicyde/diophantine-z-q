rc-o12-eisenstein: the Eisenstein blocks at p ∈ U (tex 9862–9864). Proves the Eisenstein branch of O12.LocalBlocks.newLine from the two Galois characters and the divisor-sum Fourier coefficients (base: rc/thm53-proof-20261117 at 71d379283cea3d3650e7bd8c2b23ecb58163a7e7).

Why: the owner said "I feel like we're spending way too much time re-reading literature and not nearly enough time trying to prove Elliot's manuscript", then approved the project's hosts taking Theorem 5.3's appendices. The host task rc-o12 proved both halves of GaloisConstituentModel.Inputs from named data (O12.inputs_of_theta, folded at 453aeacb; report docs/research/rc-o12.md). Its remaining inputs include "the Eisenstein comparison": LocalBlocks.newLine includes "the parallel Eisenstein calculation as data of the character pair and divisor-sum expansion", and the cuspidal print does not apply to it. The project claimed this follow-up on fork issue #83. Do not overlap the sibling tasks: rc-o12-local (the cuspidal blocks), rc-theta-coeff, rc-pm, rc-two-fresh. Do not edit RC/O12/, RC/Odd/ or RC/AddressGenuine/; import them.

Setup: your worktree is already on branch wip/rc-o12-eisenstein at 71d379283cea3d3650e7bd8c2b23ecb58163a7e7. Origin refs in the shared repository are refreshed for you; do not run git fetch or git push yourself (a separate job pushes your commits). Your files go under ZInQKernel/Contrib/OneProof/RC/O12Eisenstein/ (a new directory).

What exists (read first):
- RC/O12/Local.lean: LocalPair and LocalBlocks with the field newLine (for each active ramified constituent: b, λ, μ with b ρ_i(τ) b⁻¹ = diag(1, −1), b ρ_i(φ) b⁻¹ = diag(λ, μ), and Up acting on that coordinate by λ). RC/O12/Fourier.lean: UpAtOne. docs/research/rc-o12.md, the rows for LocalBlocks and UpAtOne.
- RC/AddressGenuine/Constituents.lean: GaloisConstituentModel.ρ, which on an Eisenstein constituent is the sum of the two characters (tex 9652–9654, 9762–9771). Find the exact normalization the tree uses for that sum (which character carries the cyclotomic twist, arithmetic or geometric Frobenius) before you start.
- The manuscript, diophantine_zq.tex:
  - 9647–9654: the constituents, including the Eisenstein character pairs ("Holomorphy alone does not exclude the latter");
  - 9754–9771: the blocks at p ∈ U, with level exponent at most one and primitive quadratic character at p for the blocks that matter;
  - 9773–9797: the normalization on cuspidal constituents, for comparison;
  - 9862–9864: "For Eisenstein constituents, the two Galois characters and the divisor-sum Fourier coefficients give the same equality directly; Carayol's cuspidal theorem is not applied to them."

Your work, for an Eisenstein constituent of weight two in a ramified block at p, with character pair (χ₁, χ₂), one unramified at p and the other with primitive quadratic conductor one at p:
1. The divisor-sum coefficients. Write the Fourier coefficients a_n = ∑_{d ∣ n} χ₁(n/d) χ₂(d) d (or the normalization the tree uses), and prove a_{pn} = λ a_n for every n ≥ 1, with λ the value at p of the character unramified there, scaled as the weight-two normalization requires. This is U_p^{(2)} on the block. Cover the degeneracies at other primes (old multiplicities carry the same scalar) and both orders of the pair.
2. The Galois side. In the basis of the two character lines, ρ(τ) = diag(1, −1) (the quadratic character is −1 on τ, the other character is trivial on inertia) and ρ(φ) = diag(λ, μ), with λ the arithmetic Frobenius value on the unramified line in the tree's normalization. Check that this λ agrees with the eigenvalue of step 1; if the conventions disagree, report it at once.
3. Assemble the Eisenstein branch of newLine, and the corresponding coordinates of UpAtOne, in exactly the types of RC/O12, as a theorem for every Eisenstein constituent of an active ramified block.
Out of scope for this run:
- the cuspidal blocks (rc-o12-local);
- the theta forms and the coefficient family (rc-theta-coeff);
- the existence of the Eisenstein constituents in the forms (part of the constituent decomposition).
Prints: none. The text gives this comparison "directly"; prove it, or make the missing piece the scoped stop.

RESOURCE LIMITS (hard rules; breaking one fails your task):
- At most ONE Lean process (lean, lake, repl, or a pytest run that starts real Lean) at a time. Never start Lean jobs in the background with &, xargs -P, or shards.
- A Lean REPL session gets at most 10 commands, then restart it. Or send the header once and pass "env" on later commands so it doesn't re-import.
- Check `uptime` and `sysctl vm.swapusage` before every Lean or pytest run. If load is above 40 or swap used is above 8 GB, don't start it; report that you were blocked.
- Ground-truth or differential checks use a sample of at most 30 inputs, run one after another.
Host note (devserver): check `uptime` and `free -g` instead of vm.swapusage; hold Lean only above load 120 or below 20 GB available memory; do not sleep and poll.

The owner's rules: follow the manuscript (diophantine_zq.tex) first, then the literature it cites. Label any step that is in neither as on-the-spot (provenance (c)). Cited prints become printed-form leaves exactly as Elliot uses them (the owner's Gross-Zagier ruling: "Follow the manuscript: CST Thm 1.1 and Kolyvagin Thm 1 become printed-form leaves exactly as Elliot cites them; we write no GZ argument of our own"). Reuse the print statements already in the tree (RC/PrintsArith, RC/PrintsAnalytic, RC/AppF/Prints.lean, the shared layer's Prints) and add only the prints named in this brief. No network is needed and you have none: mark page and theorem numbers you give from memory UNVERIFIED. If a source has a known issue, document it. Report any error you find in the manuscript or a source at once, first in the report and in .fleet/rc-o12-eisenstein.md.

Hygiene, for everything bound for the fork (Lean, report, commit messages): no session names, host names or user paths. Write paths relative to the repository root, and refer to people by role ("the lead", "the reviewer", "the cloud agent").

The stop rule, for this unattended run: if a step needs a large missing theory, build only the minimal faithful pieces the next step needs. Otherwise finish what can be finished and write a scoped report: what is missing, how large it is, the smallest faithful statement of it, and what would follow once it exists. Never add a leaf beyond the prints named here, and never weaken a statement to make it provable.

Deliverables: new files only, under ZInQKernel/Contrib/OneProof/RC/O12Eisenstein/. Never import ZInQKernel.OneProof.Main, and edit nothing outside that directory except the report, .fleet/rc-o12-eisenstein.md and scratch/rc-o12-eisenstein/. Do not use local notation; write abbreviations with explicit arguments (the merge rule blocks local notation). Compile each file with lake env lean (one Lean process at a time), with no sorry and no axiom, and give #print axioms of each new theorem (only propext, Classical.choice and Quot.sound). The report docs/research/rc-o12-eisenstein.md needs:
- the main result, or the scoped stop, first;
- the statement of each new theorem, and which part of newLine or UpAtOne it supplies;
- the normalization you found in the tree for the Eisenstein ρ, with file and line;
- a Known-issues section;
- a section "Manuscript check": one line per manuscript step you formalize or rely on, with its tex lines and one verdict: OK (right as written), gap filled (what was missing), error (what is wrong), or unverified (why).
Commit on your branch wip/rc-o12-eisenstein (only that branch) with the report (a background job pushes it; do not run git push), and give the final SHA in your last message and in .fleet/rc-o12-eisenstein.md.

Output and commits: besides the report, keep a results log at scratch/rc-o12-eisenstein/log.md (statements, findings, compile outcomes; no narrative), and at the end write .fleet/rc-o12-eisenstein.md (half a page: main result or scoped stop, what compiles, what remains). Commit as you go with git add of your own paths and git commit (never git add -A). Commit .fleet/rc-o12-eisenstein.md last. Resuming: if scratch/rc-o12-eisenstein/log.md exists, an earlier run was interrupted; read it and the report, and continue where it stopped. Keep working until .fleet/rc-o12-eisenstein.md is written and committed.

rc-theta-close: finish the actual PMLocal. Discharge rc-theta-join's remaining Lean-side inputs: the indexed neighbour transport (class match, lattice test, norm valuation one), the filtered support bridge at the exceptional places, and the packaging of the level roots. The result is an unconditional inhabitant of PMLocal for the explicit level order at the manuscript's discriminant data (base: wip/rc-theta-join at 399d56047ff7a8e5ef12e8ae14dcc602215dddc1).

Why: the owner said "I feel like we're spending way too much time re-reading literature and not nearly enough time trying to prove Elliot's manuscript", and the standing goal is to reduce the manuscript to the literature it cites. The host task rc-theta-join (report docs/research/rc-theta-join.md on its branch) built every field of PMLocal on the explicit level order: the Schwartz product, the norm spheres, the adelic norm character, the phase and the trace-zero frames. That is 105 theorems on the standard axioms. It stopped conditional on three local inputs, all Lean-side comparisons rather than manuscript steps. Its remaining-hypotheses table sizes each one as small or medium. Closing them makes pmStage and pmValLift run on an actual PMLocal. It also supplies the support bridge that rc-o7-actual's IntegralSupport.half and the orbit exhaustion of rc-o7-orbits consume. The project claims it on fork issue #83.
Do not overlap:
- rc-o7-orbits and rc-o7-character (they take the support bridge as a parameter and do not prove it);
- rc-stage-kummer (the stage maps);
- rc-pm-geometry and pm-adelic-join (PM.Geometry, PM.Evaluation).
Import existing modules; do not edit them.

Setup: your worktree is already on branch wip/rc-theta-close at 399d56047ff7a8e5ef12e8ae14dcc602215dddc1. Origin refs in the shared repository are refreshed for you; do not run git fetch or git push yourself (a separate job pushes your commits). Your files go under ZInQKernel/Contrib/OneProof/RC/ThetaClose/ (a new directory).

What exists (read first):
- docs/research/rc-theta-join.md: the sections "Remaining hypotheses and owners" and "Known issues" (the counterexample to the unfiltered support bridge), and the Manuscript check.
- RC/ThetaJoin/: Assembly.lean (IndexedNeighbourTransport, its fields step, class_match, lattice and norm; weightedNeighbour_of_transport), LevelTheta.lean (DisjointDiscriminant, levelNormCovariance, levelPmLocal), NormCharacter.lean (levelNormCharacter_single), Neighbour.lean, Frame.lean, Coordinates.lean, Schwartz.lean (LevelRoots, LevelRoots.ParityAt), Support.lean (halfIntegral_iff_local, affine_mem_at_odd, weightAt_support_iff_affine, weight_support_iff_halfIntegral, RequestedSupport, FilteredSupport).
- RC/Adelic/ (heckeStep_eq_nbAt, classesEquiv, classRepresentative, mem_leftRing_iff), RC/LineIndex/ (lineIndex, adjoint_good), RC/LocalWeights/ (the local weights, their rules, and the odd and dyadic existence theorems for the roots α_p of (O.3)), RC/ExplicitSplit/, RC/DivisionJoin/.
- The manuscript, diophantine_zq.tex: 8494-8577 (the local Schwartz functions and (O.3)); 9039-9093 (the frames, the neighbours, the y/p-sum, the norm character change χ_{h_*}(p)); 9105-9135 (the odd filter and the support on the sphere Q_B(x) = mD).

Your work:
1. IndexedNeighbourTransport, for every good p and every line of LineIndex: choose step, the adelic generator of the line aligned with the frame chart. Prove class_match with the indexed neighbour, using Adelic.heckeStep_eq_nbAt on an aligned lift. The class representative used by the product may differ there by a local unit, so either transport that unit in the frame chart or work on the aligned lift and transport the frame back. Prove lattice, the equivalence between the neighbour's rational vectors and the MemNbr p 1 test on px, by matching the integer calculation mod p² with the p-adic basis-lattice inclusion and the rational intersection. Prove norm through levelNormCharacter_single, once the aligned generator has reduced-norm valuation one (its split determinant is p times an integral unit).
2. FilteredSupport, at the manuscript's odd filter: D > 0 squarefree, gcd(D, h_*) = 1, (D/ℓ₀) = 1, and d = Dh_* an odd fundamental discriminant with F = ℚ(√d) split at every prime dividing 2N (tex 9105-9108, 9119-9120). On the sphere x.re = 0, nrd x = mD, prove schwartz ≠ 0 ↔ HalfIntegral (classOrder z) x through weight_support_iff_halfIntegral. That requires "nonzero iff affine membership" at each exceptional prime: the unit split norm at the level primes, the affine test and the square condition at 2, exact norm valuation one at the primes of m, and a nonzero residue in the division order from a unit norm at ℓ₀. Keep RequestedSupport recorded as false. Do not weaken the filter, and do not use a hypothesis the text does not state.
3. LevelRoots with ParityAt (α_q(-1) = w_{q^e} χ_{h_*}(q)^e) in the coefficient ring, from the existing odd and dyadic existence theorems, with a common two-power bound over the finite family. Also DisjointDiscriminant from the filter (a prime of m divides none of 2, N, ℓ₀).
4. Assemble levelPmLocal with every input discharged except the discriminant data and the atkin signs w_{q^e} as inputs (state them exactly), apply levelStage and levelValLift, and list exactly what remains, each with its owner.
Out of scope for this run:
- PM.Geometry and PM.Evaluation;
- (O.7) and its orbits;
- the choice of the discriminant h_* and the detecting prime (ELLIOT data, upstream);
- editing existing files.
Prints: none new.

RESOURCE LIMITS (hard rules; breaking one fails your task):
- At most ONE Lean process (lean, lake, repl, or a pytest run that starts real Lean) at a time. Never start Lean jobs in the background with &, xargs -P, or shards.
- A Lean REPL session gets at most 10 commands, then restart it. Or send the header once and pass "env" on later commands so it doesn't re-import.
- Check `uptime` and `sysctl vm.swapusage` before every Lean or pytest run. If load is above 40 or swap used is above 8 GB, don't start it; report that you were blocked.
- Ground-truth or differential checks use a sample of at most 30 inputs, run one after another.
Host note (devserver): check `uptime` and `free -g` instead of vm.swapusage; hold Lean only above load 120 or below 20 GB available memory; do not sleep and poll.

The owner's rules: follow the manuscript (diophantine_zq.tex) first, then the literature it cites. Label any step that is in neither as on-the-spot (provenance (c)) in the report. Cited prints become printed-form leaves exactly as Elliot uses them (the owner's Gross-Zagier ruling: "Follow the manuscript: CST Thm 1.1 and Kolyvagin Thm 1 become printed-form leaves exactly as Elliot cites them; we write no GZ argument of our own"). Reuse the print statements already in the tree (RC/PrintsArith, RC/PrintsAnalytic, RC/AppF/Prints.lean, the shared layer's Prints) and add only the prints named in this brief. No network is needed and you have none: mark page and theorem numbers you give from memory UNVERIFIED. If a source has a known issue, document it. Report any error you find in the manuscript or a source at once, first in the report and in .fleet/rc-theta-close.md.

Hygiene, for everything bound for the fork (Lean, report, commit messages): no session names, host names or user paths. Write paths relative to the repository root, and refer to people by role ("the lead", "the reviewer", "the cloud agent").

The stop rule, for this unattended run: if a step needs a large missing theory, build only the minimal faithful pieces the next step needs. Otherwise finish what can be finished and write a scoped report: what is missing, how large it is, the smallest faithful statement of it, and what would follow once it exists. Never add a leaf beyond the prints named here, and never weaken a statement to make it provable.

Deliverables: new files only, under ZInQKernel/Contrib/OneProof/RC/ThetaClose/. Never import ZInQKernel.OneProof.Main, and edit nothing outside that directory except the report, .fleet/rc-theta-close.md and scratch/rc-theta-close/. Do not use local notation; write abbreviations with explicit arguments (the merge rule blocks local notation). Compile each file with lake env lean (one Lean process at a time), with no sorry and no axiom. Run #print axioms of each new theorem from a check file under scratch/rc-theta-close/, not in the deliverable files (only propext, Classical.choice and Quot.sound), and list the results in the report. The report docs/research/rc-theta-close.md needs:
- the main result, or the scoped stop, first;
- the statement of each new theorem, and which input of levelPmLocal or which support statement it discharges;
- the exact list of remaining hypotheses with their owners;
- a Known-issues section;
- a section "Manuscript check": one line per manuscript step you formalize or rely on, with its tex lines and one verdict: OK (right as written), gap filled (what was missing), error (what is wrong), or unverified (why).
Commit on your branch wip/rc-theta-close (only that branch) with the report (a background job pushes it; do not run git push), and give the final SHA in your last message and in .fleet/rc-theta-close.md.

Output and commits: besides the report, keep a results log at scratch/rc-theta-close/log.md (statements, findings, compile outcomes; no narrative), and at the end write .fleet/rc-theta-close.md (half a page: main result or scoped stop, what compiles, what remains). Commit as you go with git add of your own paths and git commit (never git add -A). Commit .fleet/rc-theta-close.md last. Resuming: if scratch/rc-theta-close/log.md exists, an earlier run was interrupted; read it and the report, and continue where it stopped. Keep working until .fleet/rc-theta-close.md is written and committed.

rc-witness-spec: Appendix F's witness specialization (tex 8392-8398), the scoped stop of rc-stages, proved (base: wip/rc-stages at c653a7426f795b39762764fa31999a53c9e5922c).

Why: the owner said "I feel like we're spending way too much time re-reading literature and not nearly enough time trying to prove Elliot's manuscript", then approved the project's hosts taking Theorem 5.3's appendices. The host task rc-stages built Proposition ex:app-detector's stages (docs/research/rc-stages.md) and stopped, as planned, at tex 8392-8398: "Good reduction identifies the reduction of the global division cocycle with this exact map." The lead approved this continuation. Do not overlap the cloud agent: import its lanes' files and do not edit them. RC/Stages/ is rc-stages' work: import it, do not edit it. RC/Eichler/, RC/LocalWeights/, RC/HalfIntegral/ and RC/TraceLimits/ belong to sibling host tasks.

Setup: your worktree is already on branch wip/rc-witness-spec at c653a7426f795b39762764fa31999a53c9e5922c. Origin refs in the shared repository are refreshed for you; do not run git fetch or git push yourself (a separate job pushes your commits). Your files go under ZInQKernel/Contrib/OneProof/RC/WitnessSpec/ (a new directory).

What exists (read first):
- docs/research/rc-stages.md, especially "Exact reduction identity": for a selected datum dat : HeegnerDatum E f Lat κ (Dw * hstar) 1 hstar, P = genusPoint dat, Q the rational point of A = E^(D_w) corresponding to L·P, and a compatible tower of divisions of Q, at stage i (same place that exhibits the chosen g_i as arithmetic Frobenius, M = M_i) the identity
    ev i Dw dat (L • genusPoint dat) = b_M (proj M (c_Q (g_i * g_i)))   in ZMod (2 ^ M),
  where b_M(proj M t) is b(t) mod 2^M. Its Lean name is WitnessSpecialization (RC/Stages/Witness.lean); witnessValuation_withStages there proves WitnessValuation from it. Only the fixed multiplied witness and the chosen stages are needed, not every point or discriminant.
- The interface and the target: RC/Visibility/Genus.lean (StageKummer, the stage maps; lamOf; kummerLift) and RC/Visibility/Witness.lean (WitnessValuation W lam Dw cw, (O.2) at the witness).
- rc-stages' files: RC/Stages/Primes.lean (the joint Galois field, exists_jointFrob, global_frob_sq_on_torsion, apply_sqrt_of_isFrobAt, residueSigns_of_agreement), Actual.lean (actualStageSequence, selectedFrobenius), SplitTwist.lean (geomTwist_some, geomTwist_equivariant, geomTwist_tate_equivariant, geomTwist_tate_action_eq), ReducedCurve.lean (frob_apply, reducedKappa_surjective), FiniteField.lean (kappa and its kernel, surjectivity, equivariance), Kummer.lean (DivisionTower, finiteRow, finiteRow_proj), LocalTorsionBound.lean and UniformBound.lean (reduction at a prime of a number field of small degree, prime-to-p torsion injecting).
- The tree already has Affine.Point.reductionHom, injectivity of reduction on prime-to-residue-characteristic torsion, an equivalence on torsion over the completion, and the good-reduction inertia results in vendored Tau Ceti (git grep for them).

Your work (tex 8392-8398, with 8358-8391 as rc-stages formalized them):
1. The place: restrict the Chebotarev place of stage i to the finite extensions containing the genus point, the division point and the torsion, and build one common residue model: a finite field of characteristic ell_0 containing all the reductions.
2. Frobenius and reduction: on the chosen division point and on the prime-to-ell_0 torsion, reduction commutes with the decomposition group, and g_i acts on the reductions as the residue Frobenius.
3. The split twist: reduce the split twist identification (geomTwist) at ell_0, where D_w is a square mod ell_0, compatibly with steps 1-2.
4. The ring class field: ev lives in the ring class field of the datum. At an inert prime of K_D the rational prime ideal is principal, so in conductor one it splits in the Hilbert class field; descend to the resulting quadratic residue field.
5. Construct the actual stage map at the witness (reduction at the chosen place, then kappa_M, then the finite row) in the shape StageKummer takes, prove WitnessSpecialization for it, and then WitnessValuation through witnessValuation_withStages. Do not change StageKummer or any existing statement. If StageKummer requires more than the witness identity (for example properties on all genus data), deliver what you can and state the rest as the scoped stop.
Out of scope for this run: the theta forms and aθ; (O.7); and RC/Visibility/ beyond reading it.
Prints: only those already in the tree (as listed for rc-stages: SerreThm3, DokchitserThm18, the Bump-Friedberg-Hoffstein statements, Prints.cst). Everything else is proved, or it is the scoped stop.

RESOURCE LIMITS (hard rules; breaking one fails your task):
- At most ONE Lean process (lean, lake, repl, or a pytest run that starts real Lean) at a time. Never start Lean jobs in the background with &, xargs -P, or shards.
- A Lean REPL session gets at most 10 commands, then restart it. Or send the header once and pass "env" on later commands so it doesn't re-import.
- Check `uptime` and `sysctl vm.swapusage` before every Lean or pytest run. If load is above 40 or swap used is above 8 GB, don't start it; report that you were blocked.
- Ground-truth or differential checks use a sample of at most 30 inputs, run one after another.
Host note (devserver): check `uptime` and `free -g` instead of vm.swapusage; hold Lean only above load 120 or below 20 GB available memory; do not sleep and poll.

The owner's rules: follow the manuscript (diophantine_zq.tex) first, then the literature it cites. Label any step that is in neither as on-the-spot (provenance (c)). Cited prints become printed-form leaves exactly as Elliot uses them (the owner's Gross-Zagier ruling: "Follow the manuscript: CST Thm 1.1 and Kolyvagin Thm 1 become printed-form leaves exactly as Elliot cites them; we write no GZ argument of our own"). Reuse the print statements already in the tree (RC/PrintsArith, RC/PrintsAnalytic, RC/AppF/Prints.lean, the shared layer's Prints) and add only the prints named in this brief. No network is needed and you have none: mark page and theorem numbers you give from memory UNVERIFIED. If a source has a known issue, document it. Report any error you find in the manuscript or a source at once, first in the report and in .fleet/rc-witness-spec.md.

Hygiene, for everything bound for the fork (Lean, report, commit messages): no session names, host names or user paths. Write paths relative to the repository root, and refer to people by role ("the lead", "the reviewer", "the cloud agent").

The stop rule, for this unattended run: if a step needs a large missing theory, build only the minimal faithful pieces the next step needs. Otherwise finish what can be finished and write a scoped report: what is missing, how large it is, the smallest faithful statement of it, and what would follow once it exists. Never add a leaf beyond the prints named here, and never weaken a statement to make it provable.

Deliverables: new files only, under ZInQKernel/Contrib/OneProof/RC/WitnessSpec/. Never import ZInQKernel.OneProof.Main, and edit nothing outside that directory except the report, .fleet/rc-witness-spec.md and scratch/rc-witness-spec/. Compile each file with lake env lean (one Lean process at a time), with no sorry and no axiom, and give #print axioms of each new theorem (only propext, Classical.choice and Quot.sound). The report docs/research/rc-witness-spec.md needs:
- the main result, or the scoped stop, first;
- the statement of each new theorem, and which field or input of the tree it supplies (WitnessSpecialization, WitnessValuation, the stage-map interface);
- the exact statement of anything left open, and how large the missing theory is;
- a Known-issues section;
- a section "Manuscript check": one line per manuscript step you formalize or rely on, with its tex lines and one verdict: OK (right as written), gap filled (what was missing), error (what is wrong), or unverified (why).
Commit on your branch wip/rc-witness-spec (only that branch) with the report (a background job pushes it; do not run git push), and give the final SHA in your last message and in .fleet/rc-witness-spec.md.

Output and commits: besides the report, keep a results log at scratch/rc-witness-spec/log.md (statements, findings, compile outcomes; no narrative), and at the end write .fleet/rc-witness-spec.md (half a page: main result or scoped stop, what compiles, what remains). Commit as you go with git add of your own paths and git commit (never git add -A). Commit .fleet/rc-witness-spec.md last. Resuming: if scratch/rc-witness-spec/log.md exists, an earlier run was interrupted; read it and the report, and continue where it stopped. Keep working until .fleet/rc-witness-spec.md is written and committed.

rc-hiw-twist: Appendix E's remaining GLUE HalfIntegralTwist, the twist of a weight-3/2 form by a Dirichlet character (tex 8099-8103), through the theta multiplier on Γ₀(4) (base: rc/thm53-proof-20261117 at 1ddd7c2ac7a579baf80026a2f48bb8206ce6cdf2).

Why: the owner said "I feel like we're spending way too much time re-reading literature and not nearly enough time trying to prove Elliot's manuscript", then approved the project's hosts taking Theorem 5.3's appendices. The project's App E piece (folded into the integration branch at 0266f729) filled EvenPhaseData for E_ℓ. Its one open GLUE is HalfIntegralTwist, which evenPhaseData_Ecurve takes as a hypothesis (the scoped stop of docs/research/rc-appE-phase.md). The project claimed this piece on fork issue #83 (comment 6968946147). Do not overlap the cloud agent that owns Theorem 5.3: RC/PrintsAnalytic/ (its lane RC8), RC/Even/ and RC/AppE/ stay as they are. Import them; do not edit them.

Setup: your worktree is already on branch wip/rc-hiw-twist at 1ddd7c2ac7a579baf80026a2f48bb8206ce6cdf2. Origin refs in the shared repository are refreshed for you; do not run git fetch or git push yourself (a separate job pushes your commits). Your files go under ZInQKernel/Contrib/OneProof/RC/HalfIntegral/ (a new directory).

What exists (read first):
- RC/AppE/Galois.lean:49, def HalfIntegralTwist. Prove exactly this Prop: for N > 0 with 4 ∣ N, characters ψ, ν mod N and f with IsHalfIntegralWeightCuspForm 3 N ψ f, there is M with N ∣ M, 0 < M and the same prime support as N, and f' with IsHalfIntegralWeightCuspForm 3 M ((ψ * ν ^ 2).changeLevel _) f' and hiwCoeff f' n = ν n * hiwCoeff f n for all n. In the same file: twist_mem_eigenspace (its consumer) and the level-raising lemmas.
- RC/PrintsAnalytic/Waldspurger.lean:
  - thetaFun z = jacobiTheta (2z) (line 80);
  - thetaMultiplier γ z = θ(γz)/θ(z) (line 84);
  - IsHalfIntegralWeightCuspForm k N χ g (line 91): holomorphy, the law g(γz) = χ(d) j(γ,z)^k g(z) on Γ₀(N), and the cusp conditions. Read its exact form, including the cusp conditions, before planning;
  - hiwCoeff.
- RC/AppE/Linear.lean: periodicity (hiwForm_periodic), linearity of the coefficients, and closure of the spaces under linear combinations.
- docs/research/rc-appE-phase.md, section "What is missing (scoped stop): HalfIntegralTwist": why the translation-sum proof needs j(γ', z + u'/m) = j(γ, z) for γ' = T^{u/m} γ T^{−u'/m}.
- Mathlib (check the exact names):
  - jacobiTheta, with its S- and T²-transformations (jacobiTheta_S_smul, jacobiTheta_T_sq_smul);
  - jacobiTheta₂ and its functional equation;
  - Gauss sums (gaussSum, gaussSum_mul_gaussSum_eq_card);
  - Dirichlet characters (primitive characters, conductor);
  - Poisson summation.

Your work. The manuscript, tex 8099-8103: "The twist is modular at a level still supported on S_0; this follows as well by writing it as the finite additive translation sum using the Gauss sum of the primitive character inducing ν."
1. The theta multiplier under conjugation by translations: j(T^{u/m} γ T^{−u'/m}, z + u'/m) = j(γ, z) whenever both matrices lie in Γ₀(4) and are related as in the translation sum. There are two routes; choose the shorter. Route (a) is reusable for other half-integral-weight work.
   - (a) The explicit formula j(γ, z) = ε_d^{−1} (c/d) √(cz + d) on Γ₀(4), in Shimura's normalization and with the branch of the square root that the tree's thetaMultiplier gives. Prove it from Mathlib's S- and T²-transformations of θ, the generation of Γ₀(4), and the cocycle property of j. The symbol (c/d) needs the reciprocity behaviour of the Kronecker or Jacobi symbol under the generator moves.
   - (b) The transformation law of θ(z + u/m) = Σ_n e(n²u/m) q^{n²} on Γ₀(4m²), by splitting n modulo m and using Poisson summation or jacobiTheta₂'s functional equation.
2. The twist for a primitive ν of conductor r: f ⊗ ν = G(ν̄)^{−1} Σ_{u mod r} ν̄(u) f(z + u/r). Show that it transforms under Γ₀(Nr²), or the level the manuscript's support condition allows, with character ψν², and that it is holomorphic and cuspidal. Its coefficients are ν(n) a_f(n).
3. An imprimitive ν mod N, as in the statement: it is the primitive character inducing it, times the trivial character at the primes of N. The twist by the trivial character at p is again a translation sum: f − (1/p) Σ_{u mod p} f(z + u/p) keeps exactly the coefficients at n prime to p. Check that the level keeps the prime support of N.
4. Assemble HalfIntegralTwist exactly as stated. Then state evenPhaseData_Ecurve without its hypothesis hTw, as a corollary theorem in your directory that applies the existing theorem; do not edit RC/AppE/.
Out of scope for this run: Waldspurger's prints, Ramsey's model, and RC/Even/.
Prints: none. The manuscript cites no source for this step; it calls the step standard and sketches it. In particular, add no Shimura leaf: the manuscript cites Shimura only for Theorem 1 of another paper (tex 771). If a step is too large, the scoped stop gives its smallest faithful statement (for example, the explicit multiplier formula as one named statement) and what follows from it.

RESOURCE LIMITS (hard rules; breaking one fails your task):
- At most ONE Lean process (lean, lake, repl, or a pytest run that starts real Lean) at a time. Never start Lean jobs in the background with &, xargs -P, or shards.
- A Lean REPL session gets at most 10 commands, then restart it. Or send the header once and pass "env" on later commands so it doesn't re-import.
- Check `uptime` and `sysctl vm.swapusage` before every Lean or pytest run. If load is above 40 or swap used is above 8 GB, don't start it; report that you were blocked.
- Ground-truth or differential checks use a sample of at most 30 inputs, run one after another.
Host note (devserver): check `uptime` and `free -g` instead of vm.swapusage; hold Lean only above load 120 or below 20 GB available memory; do not sleep and poll.

The owner's rules: follow the manuscript (diophantine_zq.tex) first, then the literature it cites. Label any step that is in neither as on-the-spot (provenance (c)). Cited prints become printed-form leaves exactly as Elliot uses them (the owner's Gross-Zagier ruling: "Follow the manuscript: CST Thm 1.1 and Kolyvagin Thm 1 become printed-form leaves exactly as Elliot cites them; we write no GZ argument of our own"). Reuse the print statements already in the tree (RC/PrintsArith, RC/PrintsAnalytic, RC/AppF/Prints.lean, the shared layer's Prints) and add only the prints named in this brief. No network is needed and you have none: mark page and theorem numbers you give from memory UNVERIFIED. If a source has a known issue, document it. Report any error you find in the manuscript or a source at once, first in the report and in .fleet/rc-hiw-twist.md.

Hygiene, for everything bound for the fork (Lean, report, commit messages): no session names, host names or user paths. Write paths relative to the repository root, and refer to people by role ("the lead", "the reviewer", "the cloud agent").

The stop rule, for this unattended run: if a step needs a large missing theory, build only the minimal faithful pieces the next step needs. Otherwise finish what can be finished and write a scoped report: what is missing, how large it is, the smallest faithful statement of it, and what would follow once it exists. Never add a leaf beyond the prints named here, and never weaken a statement to make it provable.

Deliverables: new files only, under ZInQKernel/Contrib/OneProof/RC/HalfIntegral/. Never import ZInQKernel.OneProof.Main, and edit nothing outside that directory except the report, .fleet/rc-hiw-twist.md and scratch/rc-hiw-twist/. Compile each file with lake env lean (one Lean process at a time), with no sorry and no axiom, and give #print axioms of each new theorem (only propext, Classical.choice and Quot.sound). The report docs/research/rc-hiw-twist.md needs:
- the main result, or the scoped stop, first;
- the statement of each new theorem, and which hypothesis of the tree it discharges (HalfIntegralTwist; hTw of evenPhaseData_Ecurve);
- a Known-issues section;
- a section "Manuscript check": one line per manuscript step you formalize or rely on, with its tex lines and one verdict: OK (right as written), gap filled (what was missing), error (what is wrong), or unverified (why).
Commit on your branch wip/rc-hiw-twist (only that branch) with the report (a background job pushes it; do not run git push), and give the final SHA in your last message and in .fleet/rc-hiw-twist.md.

Output and commits: besides the report, keep a results log at scratch/rc-hiw-twist/log.md (statements, findings, compile outcomes; no narrative), and at the end write .fleet/rc-hiw-twist.md (half a page: main result or scoped stop, what compiles, what remains). Commit as you go with git add of your own paths and git commit (never git add -A). Commit .fleet/rc-hiw-twist.md last. Resuming: if scratch/rc-hiw-twist/log.md exists, an earlier run was interrupted; read it and the report, and continue where it stopped. Keep working until .fleet/rc-hiw-twist.md is written and committed.

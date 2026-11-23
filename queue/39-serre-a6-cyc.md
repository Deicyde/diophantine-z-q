serre-a6-cyc: prove in Lean one nontrivial instance of the named input LocalArtin.serreA6OnIntegerUnits, the cyclotomic character with weight n ≡ 1, on the (iv) side, as a sign check (base: fold/conrad-serre-1123 at 8ed0590c0cd95dbb16643c338aca466ddb5fb1eb).

Why: serreA6OnIntegerUnits (ZInQKernel/Contrib/OneProof/ConradSerre/LocalArtin.lean, `def serreA6OnIntegerUnits`) is a named input stating Serre's III-A6 Prop. 6 (ii) ⇔ (iv) with the character evaluated at the Artin map of K. Its only regression check, serreA6_integerUnits_trivial in the same file, uses the trivial character with n = 0, so it can't catch a sign error in the (iv) identity χ(art_K u) · ∏_σ σ⁻¹(u)^{n σ} = 1. For ψ = χ_cyc, Serre's weight is n ≡ 1, and the (iv) identity reads χ_cyc(art_K u) · N_{K/ℚ_p}(u) = 1. That holds exactly when the Artin-map normalization in the statement matches Tau Ceti's, where χ_cyc(Art_{ℚ_p}(p^k u)) = u⁻¹. A Lean proof of this instance makes the sign machine-checked.
Do not overlap: the RC lanes (hcm, the O.7 model, the even inventory) and the #183 fold itself. The PR desk folds your file in afterwards.

Setup: git fetch origin fold/conrad-serre-1123. Create branch wip/serre-a6-cyc at 8ed0590c0cd95dbb16643c338aca466ddb5fb1eb (git rev-parse origin/fold/conrad-serre-1123 must print that SHA; if it doesn't, use the SHA above anyway and note the difference in the report).

What exists (read first):
- LocalArtin.lean: artinK, character_norm (norm functoriality of the Artin map, Tau Ceti's artinMap_norm), continuousCharacter, restrictCharacter, serreConditionII, serreConditionIVUnits, serreA6OnIntegerUnits, serreA6_integerUnits_trivial (the pattern for unfolding the (iv) side).
- ZInQKernel/Contrib/TauCeti/NumberTheory/ClassFieldTheory/Local/ExplicitCyclotomicSymbol/ArtinMap.lean: abelianizedLocalCyclotomicCharacter_artinMap_padic, χ_cyc(Art_{ℚ_p}(p^k u)) = u⁻¹.
- The cyclotomic power cycPow in ZInQ.Contrib.G9.PkgI4 (opened in LocalArtin.lean), which serreConditionII uses.

Your work:
1. In ONE new file, ZInQKernel/Contrib/OneProof/ConradSerre/SerreA6CyclotomicCheck.lean, define the cyclotomic character as ψ : GQp p →* Kˣ (the p-adic cyclotomic character, valued in ℤ_pˣ ⊂ ℚ_pˣ ⊂ Kˣ), and prove its continuity hypothesis hc. Use the cyclotomic character Tau Ceti's lemma speaks about. If you need its agreement with cycPow, prove that agreement as a lemma; do not assume it.
2. Prove `serreConditionIVUnits p K ψ hc (fun _ => 1)` for every finite Galois K/ℚ_p inside PadicAlgCl p. Expected route: character_norm moves art_K u to Art_{ℚ_p}(N u); N u is a unit of ℤ_p, so abelianizedLocalCyclotomicCharacter_artinMap_padic with k = 0 gives (N u)⁻¹; the product ∏_σ σ⁻¹(u) is N_{K/ℚ_p}(u). The open subgroup can be all of the integer units.
3. Add #print axioms for the new theorem in the file. Build the file's imports first (build note), then compile the file with lake env lean, one Lean process at a time. Save the output as scratch/serre-a6-cyc/axioms.txt and a short log as scratch/serre-a6-cyc/log.md.
4. Write docs/research/serre-a6-cyc.md: the result first (closed or not); the statement proved, quoted from the file; the route; the axiom output; Known issues. Write .fleet/serre-a6-cyc.md, a short summary.
Edit no existing file. Change no statement in LocalArtin.lean or anywhere else.
Stop rule, for this unattended run: if the (iv) identity does not close, find out which way it fails. Prove the instance with the opposite weight (fun _ => -1), or the inverse identity, if that closes; otherwise state precisely the step that fails. Report it first as a possible SIGN ERROR in the named input serreA6OnIntegerUnits, in the report and in .fleet/serre-a6-cyc.md. Commit whatever compiles. Never weaken or edit the named input to make it close.
Out of scope: the (ii) side, any change to the #183 fold, new prints.
Prints: none. The theorem cited is Tau Ceti's proved lemma; nothing is assumed.

RESOURCE LIMITS (hard rules; breaking one fails your task):
- At most ONE Lean process (lean, lake, repl, or a pytest run that starts real Lean) at a time. Never start Lean jobs in the background with &, xargs -P, or shards.
- A Lean REPL session gets at most 10 commands, then restart it. Or send the header once and pass "env" on later commands so it doesn't re-import.
- Check `uptime` and `sysctl vm.swapusage` before every Lean or pytest run. If load is above 40 or swap used is above 8 GB, don't start it; report that you were blocked.
- Ground-truth or differential checks use a sample of at most 30 inputs, run one after another.
Host note (devserver): check `uptime` and `free -g` instead of vm.swapusage; hold Lean only above load 120 or below 20 GB available memory; do not sleep and poll. Run Lean under MemoryMax 60G. Run one lake command at a time, never two in parallel, and never a check while a build runs.

The owner's rules: follow the manuscript (diophantine_zq.tex) first, then the literature it cites. Add no print. Report any error you find in the manuscript, a source or a named input at once, first in the report and in .fleet/serre-a6-cyc.md.

Hygiene, for everything bound for the fork (Lean, report, commit messages): no session names, host names or user paths. Write paths relative to the repository root, and refer to people by role ("the lead", "the reviewer").

Deliverables: branch wip/serre-a6-cyc with the one new Lean file; scratch/serre-a6-cyc/ (log.md, axioms.txt); docs/research/serre-a6-cyc.md; .fleet/serre-a6-cyc.md. No sorry and no axiom; only propext, Classical.choice and Quot.sound in the axiom output.
Commit as you go (after each step that compiles). Commit and push your branch wip/serre-a6-cyc (only that branch) with the report; give the final SHA in your last message.

Build note (read before compiling): the worktree's .lake was copied from a build of the fork's main, so modules that exist only on your base branch (or arrive with your merge) have no .olean yet, and lake env lean on a file that imports them stops with a missing-object error. Before checking your own files, build their imports once with lake build <Module> for each module your files import (one Lean process at a time; let each finish), then compile your files. Never report a file as unchecked because an import was not built: build it. Report any file that still fails, with the error. One Lean process at a time means one lake command at a time: let each lake build or lake env lean finish before starting the next, never run two in parallel, and never start a check while a build is running.

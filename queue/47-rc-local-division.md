rc-local-division: the local division algebra at the detecting prime ℓ₀ and its maximal order, inhabiting the division-prime interface of RC/LocalWeights (base: wip/rc-local-weights at 23d66f067d7f047ecc7ef687d2307d3164124de8).

Why: the owner said "I feel like we're spending way too much time re-reading literature and not nearly enough time trying to prove Elliot's manuscript", then approved the project's hosts taking Theorem 5.3's appendices. The hosts' local-weights task (report docs/research/rc-local-weights.md) proved the ℓ₀-weight and its rules conditional on a local model. Its scoped stop: "The smallest missing local theorem provides C : DivisionCoordinates p D and DivisionLocalModel C as above. One route is the unramified quadratic extension L/ℚₚ and the algebra L ⊕ LΠ, where Π² = p and Πa = Frob(a)Π." The project claimed this follow-up on fork issue #83 (comment 6970086480). Do not overlap the sibling tasks: RC/Eichler/ (the global order) and RC/LocalWeights/ (import it, do not edit it).

Setup: your worktree is already on branch wip/rc-local-division at 23d66f067d7f047ecc7ef687d2307d3164124de8. Origin refs in the shared repository are refreshed for you; do not run git fetch or git push yourself (a separate job pushes your commits). Your files go under ZInQKernel/Contrib/OneProof/RC/LocalDivision/ (a new directory).

What exists (read first):
- docs/research/rc-local-weights.md, section "Exact interface to the order construction", the Division bullet: the exact list of what to supply.
- RC/LocalWeights/Division.lean: structure DivisionCoordinates p D (fields order, tr, nrd, red, red_surj, red_scalar, red_locallyConstant, order_open, order_compact, beta, beta_ne_zero, trace_line, uniformizer, uniformizer_order, uniformizer_conj, uniformizer_frobenius, beta_frobenius, and others; read them all), DivisionLocalModel, and the theorems that become unconditional once these are inhabited (divisionWeight_eq, divisionWeight_conj, divisionWeight_scale, divisionWeight_uniformizer). RC/LocalWeights/DivisionAmbient.lean: the ambient rules and compact open support.
- The manuscript, diophantine_zq.tex 8551-8566 (the weight at ℓ₀), 8462-8463 (B ramified exactly at ℓ₀ and ∞), and "The determinant gives ℓ₀ ≡ −1 (mod 4)" in the proof of ex:app-theta-form.
- Mathlib: QuaternionAlgebra (ℍ[R,a,b,c]), PadicInt, Padic and its valuation, GaloisField p 2, ZMod.

Your work, for a prime p ≡ 3 (mod 4):
1. The algebra. Take D := ℍ[ℚ_[p], −1, 0, −p]: i² = −1, j² = −p, ij = −ji. This is the base change of the explicit global algebra ℍ[ℚ, −1, 0, −ℓ₀] suggested to the Eichler task, so the later join is a base change. ℚ_p(i) is the unramified quadratic extension, since −1 is a nonsquare modulo p, and j acts on it by conjugation.
   - Prove D is a division ring. The reduced norm x₀² + x₁² + p(x₂² + x₃²) is anisotropic over ℚ_p: a sum of two squares has even valuation when p ≡ 3 (mod 4). Then x̄/nrd x inverts any x ≠ 0.
   - Give the DivisionRing instance, the ℚ_[p]- and ℤ_[p]-algebra structures, rank four, and the product topology (Hausdorff), as the interface needs.
2. The maximal order 𝒪: the ℤ_[p]-span of 1, i, j, k, which equals {x : nrd x ∈ ℤ_p}.
   - It is compact and open, and it is a finite ℤ_[p]-subalgebra.
   - It is maximal among finite subalgebras containing it: every element of a finite ℤ_p-subalgebra is integral, so its norm and trace lie in ℤ_p, so it lies in 𝒪. Use v(x) = v_p(nrd x).
3. The reduced trace and norm: tr x = 2x₀ and nrd x = x x̄, with the interface's continuity, conjugation invariance, multiplicativity, and order units mapping into ℤ_[p]ˣ.
4. The residue map red : 𝒪 → GaloisField p 2, through 𝒪/j𝒪 ≅ ℤ_p[i]/(p) ≅ F_p(i).
   - It is surjective and locally constant, sends scalars to their reductions, and its kernel is exactly the nonunits (the maximal ideal j𝒪).
   - beta := the image of i, so beta^p = −beta, because i^p = −i when p ≡ 3 (mod 4).
   - A trace-zero order element x₁i + x₂j + x₃k reduces to t·beta with t = x₁ mod p.
5. The uniformizer Π = j: nrd j = p has valuation one. Conjugation by j restricts to a ring automorphism of 𝒪 whose residue action is a ↦ a^p.
6. Assemble C : DivisionCoordinates p D and DivisionLocalModel C exactly as RC/LocalWeights/Division.lean states them. Then state the instantiated weight theorems (divisionWeight_uniformizer and the others) as corollaries for this D.
Out of scope for this run:
- the identification of the completed global order R ⊗ ℤ_ℓ₀ with this model (the join, on top of the Eichler task);
- the split identifications (the Eichler task supplies them);
- P_M.
Prints: none. This is local algebra: prove each step, or make it the scoped stop.

RESOURCE LIMITS (hard rules; breaking one fails your task):
- At most ONE Lean process (lean, lake, repl, or a pytest run that starts real Lean) at a time. Never start Lean jobs in the background with &, xargs -P, or shards.
- A Lean REPL session gets at most 10 commands, then restart it. Or send the header once and pass "env" on later commands so it doesn't re-import.
- Check `uptime` and `sysctl vm.swapusage` before every Lean or pytest run. If load is above 40 or swap used is above 8 GB, don't start it; report that you were blocked.
- Ground-truth or differential checks use a sample of at most 30 inputs, run one after another.
Host note (devserver): check `uptime` and `free -g` instead of vm.swapusage; hold Lean only above load 120 or below 20 GB available memory; do not sleep and poll.

The owner's rules: follow the manuscript (diophantine_zq.tex) first, then the literature it cites. Label any step that is in neither as on-the-spot (provenance (c)). Cited prints become printed-form leaves exactly as Elliot uses them (the owner's Gross-Zagier ruling: "Follow the manuscript: CST Thm 1.1 and Kolyvagin Thm 1 become printed-form leaves exactly as Elliot cites them; we write no GZ argument of our own"). Reuse the print statements already in the tree (RC/PrintsArith, RC/PrintsAnalytic, RC/AppF/Prints.lean, the shared layer's Prints) and add only the prints named in this brief. No network is needed and you have none: mark page and theorem numbers you give from memory UNVERIFIED. If a source has a known issue, document it. Report any error you find in the manuscript or a source at once, first in the report and in .fleet/rc-local-division.md.

Hygiene, for everything bound for the fork (Lean, report, commit messages): no session names, host names or user paths. Write paths relative to the repository root, and refer to people by role ("the lead", "the reviewer", "the cloud agent").

The stop rule, for this unattended run: if a step needs a large missing theory, build only the minimal faithful pieces the next step needs. Otherwise finish what can be finished and write a scoped report: what is missing, how large it is, the smallest faithful statement of it, and what would follow once it exists. Never add a leaf beyond the prints named here, and never weaken a statement to make it provable.

Deliverables: new files only, under ZInQKernel/Contrib/OneProof/RC/LocalDivision/. Never import ZInQKernel.OneProof.Main, and edit nothing outside that directory except the report, .fleet/rc-local-division.md and scratch/rc-local-division/. Compile each file with lake env lean (one Lean process at a time), with no sorry and no axiom, and give #print axioms of each new theorem (only propext, Classical.choice and Quot.sound). The report docs/research/rc-local-division.md needs:
- the main result, or the scoped stop, first;
- the statement of each new theorem, and which field of DivisionCoordinates or DivisionLocalModel it supplies;
- what the later join needs from the global algebra and order, stated exactly;
- a Known-issues section;
- a section "Manuscript check": one line per manuscript step you formalize or rely on, with its tex lines and one verdict: OK (right as written), gap filled (what was missing), error (what is wrong), or unverified (why).
Commit on your branch wip/rc-local-division (only that branch) with the report (a background job pushes it; do not run git push), and give the final SHA in your last message and in .fleet/rc-local-division.md.

Output and commits: besides the report, keep a results log at scratch/rc-local-division/log.md (statements, findings, compile outcomes; no narrative), and at the end write .fleet/rc-local-division.md (half a page: main result or scoped stop, what compiles, what remains). Commit as you go with git add of your own paths and git commit (never git add -A). Commit .fleet/rc-local-division.md last. Resuming: if scratch/rc-local-division/log.md exists, an earlier run was interrupted; read it and the report, and continue where it stopped. Keep working until .fleet/rc-local-division.md is written and committed.

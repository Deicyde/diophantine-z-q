rc-local-weights: Appendix F's local Schwartz functions (O.3) on the standard local models, and the coefficient ring 𝒪 (base: rc/thm53-proof-20261117 at 1ddd7c2ac7a579baf80026a2f48bb8206ce6cdf2).

Why: the owner said "I feel like we're spending way too much time re-reading literature and not nearly enough time trying to prove Elliot's manuscript", then approved the project's hosts taking Theorem 5.3's appendices. The cloud agent that owns Theorem 5.3's reduction (fork issue #83) asked the project for the construction behind the theta side of (O.7) (ThetaSide, comment 6967942444). The project claimed this piece (comment 6968946147). A sibling task, rc-eichler, builds the Eichler order, its class set, its unit groups and its neighbours under RC/Eichler/: do not touch that directory or redo its work. Do not overlap the cloud agent either: RC/Visibility/, RC/Odd/ and RC/GlueSweep/ are its lanes, and the sign α(−1) = 1 is already proved there.

Setup: your worktree is already on branch wip/rc-local-weights at 1ddd7c2ac7a579baf80026a2f48bb8206ce6cdf2. Origin refs in the shared repository are refreshed for you; do not run git fetch or git push yourself (a separate job pushes your commits). Your files go under ZInQKernel/Contrib/OneProof/RC/LocalWeights/ (a new directory).

What exists (read first):
- The manuscript, diophantine_zq.tex 8496-8577 (the finite Schwartz function), with 8462-8473 for B and R.
- RC/Odd/ThetaLocal.lean: the algebra of these local weights, already proved. Reuse it; do not reprove it.
  - centralizer_X0, quadraticChar_det_eq_of_conj, diag_conj_X0: the nilpotent sign at p | m (tex 8536-8549);
  - trace_zero_sq_not_square, legendre_extracted: the residue line at ℓ₀ (tex 8551-8561);
  - dyadic_affine, idempotent_zmod_two_pow: the dyadic rule (tex 8517-8531);
  - alpha_neg_one: α(−1) = 1 (tex 8579-8592).
- RC/GlueSweep/OddRootNumber.lean: α(−1) = 1 with the root number discharged.
- RC/Visibility/Theta.lean, structure ThetaStage:
  - f: the weights f z x = f(z⁻¹xz), with values in 𝒪;
  - f_conj: invariance under conjugation by R_z^×, which follows from f(u⁻¹xu) = χ_{h_*}(Nrd u)⁻¹ f(x) and Nrd u = 1 on the units of a definite order;
  - finite_supp.
- RC/Visibility/Models.lean:187, ThetaSide: the field ring_two, (2 : O)^M ∣ (z : O) → 2^M ∣ z.

Your work (tex 8496-8577):
1. The standard local models, as concrete objects. Use Mathlib's ℤ_[p] (PadicInt) and Matrix (Fin 2) (Fin 2).
   - At p not dividing 2Nmℓ₀: M_2(ℤ_p), the local maximal order, and its trace-zero part.
   - At odd p^e ∥ N: the local Eichler model {(a b; c d) ∈ M_2(ℤ_p) : p^e ∣ c}, with its cyclic level quotient.
   - At 2: the dyadic Eichler model, or M_2(ℤ_2) if 2 does not divide N.
   - At p | m: M_2(ℤ_p)^0.
   - At ℓ₀: the maximal order of the local division algebra, with residue field F_{ℓ₀²}.
   These models are the interface to rc-eichler, which will supply the isomorphisms R ⊗ ℤ_p ≅ model. State that interface as a structure or as hypotheses; do not prove it here.
2. The local functions f_p on these models, exactly as tex 8496-8566 defines them.
   - At p not dividing 2Nmℓ₀: 1_{R_p^0}.
   - At odd p^e ∥ N: the split integral unit support, weighted by α_p(r). The selected root r is the eigensummand chosen by the cyclic level quotient. The projectors (x ± r)/(2r) are integral, and r is locally constant modulo p^k, by reduction and Hensel.
   - At 2: the dyadic support e_x = (1+x)/2 ∈ R_2 with x² = r² ∈ ℤ_2^{×2}. The selected root comes from the projector that acts as the identity on the cyclic quotient.
   - At p | m: the support x ∈ M_2(ℤ_p)^0 with v_p Q_B(x) = 1, weighted by ε_p.
   - At ℓ₀: the support x ∈ R_{ℓ₀}^0 with nonzero reduction tβ, weighted by (t/ℓ₀).
3. The root character (O.3).
   - At odd p: a character α_p of (ℤ/p)^× (or ℤ_p^×) of finite 2-power order, with α_p(−1) = w_{p^e} χ_{h_*}(p)^e for either prescribed sign. It exists by the cyclic 2-primary part of F_p^× (tex 8508-8512).
   - At 2: either prescribed parity, from the trivial character or the character mod 4 (tex 8532-8534).
4. The rules (tex 8512-8516, 8545-8549, 8555-8559, 8571-8577).
   - Conjugation by a unit u of the local model multiplies f_p by the stated character: trivial at the split primes; the α_p rule at p | N, through r ↦ ur; (det u/p) at p | m; at ℓ₀, trivial for order units and −1 for the division uniformizer.
   - Scaling x ↦ vx by v ∈ ℤ_p^× multiplies f_p by α_p(v), (v/p) or (v/ℓ₀) respectively.
   - Each f_p is locally constant with compact open support: it depends only on x modulo p^k for a fixed k.
   - For f = ∏ f_p, over the finitely many special primes times the characteristic functions at the others, prove the global rules f(u⁻¹xu) = χ_{h_*}(Nrd u)⁻¹ f(x), for u in the product of the local units, and f(vx) = α(v) f(x), for v ∈ Ẑ^×. Use whatever finite form the models allow: a product over a finite set of primes that contains the special ones, with x global, is enough.
5. The coefficient ring 𝒪 (tex 8567-8570): the valuation ring at a place above two of the field generated by the fixed root-character values (a cyclotomic field of 2-power conductor). Prove 2^M 𝒪 ∩ ℤ = 2^M ℤ, which is ThetaSide.ring_two for this 𝒪. If constructing the valuation ring is large, prove ring_two for the subring ℤ[ζ_{2^k}] and say what the valuation ring needs.
Out of scope for this run:
- the global order R and its class set (rc-eichler);
- the join of the local models to R_z that gives ThetaStage.f, f_conj and finite_supp (a later run on top of both);
- P_M;
- the transformation law (tex 8623-9037).
Prints: none. This is the manuscript's own local algebra: prove each step, or make it the scoped stop.

RESOURCE LIMITS (hard rules; breaking one fails your task):
- At most ONE Lean process (lean, lake, repl, or a pytest run that starts real Lean) at a time. Never start Lean jobs in the background with &, xargs -P, or shards.
- A Lean REPL session gets at most 10 commands, then restart it. Or send the header once and pass "env" on later commands so it doesn't re-import.
- Check `uptime` and `sysctl vm.swapusage` before every Lean or pytest run. If load is above 40 or swap used is above 8 GB, don't start it; report that you were blocked.
- Ground-truth or differential checks use a sample of at most 30 inputs, run one after another.
Host note (devserver): check `uptime` and `free -g` instead of vm.swapusage; hold Lean only above load 120 or below 20 GB available memory; do not sleep and poll.

The owner's rules: follow the manuscript (diophantine_zq.tex) first, then the literature it cites. Label any step that is in neither as on-the-spot (provenance (c)). Cited prints become printed-form leaves exactly as Elliot uses them (the owner's Gross-Zagier ruling: "Follow the manuscript: CST Thm 1.1 and Kolyvagin Thm 1 become printed-form leaves exactly as Elliot cites them; we write no GZ argument of our own"). Reuse the print statements already in the tree (RC/PrintsArith, RC/PrintsAnalytic, RC/AppF/Prints.lean, the shared layer's Prints) and add only the prints named in this brief. No network is needed and you have none: mark page and theorem numbers you give from memory UNVERIFIED. If a source has a known issue, document it. Report any error you find in the manuscript or a source at once, first in the report and in .fleet/rc-local-weights.md.

Hygiene, for everything bound for the fork (Lean, report, commit messages): no session names, host names or user paths. Write paths relative to the repository root, and refer to people by role ("the lead", "the reviewer", "the cloud agent").

The stop rule, for this unattended run: if a step needs a large missing theory, build only the minimal faithful pieces the next step needs. Otherwise finish what can be finished and write a scoped report: what is missing, how large it is, the smallest faithful statement of it, and what would follow once it exists. Never add a leaf beyond the prints named here, and never weaken a statement to make it provable.

Deliverables: new files only, under ZInQKernel/Contrib/OneProof/RC/LocalWeights/. Never import ZInQKernel.OneProof.Main, and edit nothing outside that directory except the report, .fleet/rc-local-weights.md and scratch/rc-local-weights/. Compile each file with lake env lean (one Lean process at a time), with no sorry and no axiom, and give #print axioms of each new theorem (only propext, Classical.choice and Quot.sound). The report docs/research/rc-local-weights.md needs:
- the main result, or the scoped stop, first;
- the statement of each new theorem, and which field or ELLIOT input of the tree it supplies or prepares (ThetaStage.f, f_conj or finite_supp; ThetaSide.ring_two);
- the local-model interface that rc-eichler must supply, stated exactly;
- a Known-issues section;
- a section "Manuscript check": one line per manuscript step you formalize or rely on, with its tex lines and one verdict: OK (right as written), gap filled (what was missing), error (what is wrong), or unverified (why).
Commit on your branch wip/rc-local-weights (only that branch) with the report (a background job pushes it; do not run git push), and give the final SHA in your last message and in .fleet/rc-local-weights.md.

Output and commits: besides the report, keep a results log at scratch/rc-local-weights/log.md (statements, findings, compile outcomes; no narrative), and at the end write .fleet/rc-local-weights.md (half a page: main result or scoped stop, what compiles, what remains). Commit as you go with git add of your own paths and git commit (never git add -A). Commit .fleet/rc-local-weights.md last. Resuming: if scratch/rc-local-weights/log.md exists, an earlier run was interrupted; read it and the report, and continue where it stopped. Keep working until .fleet/rc-local-weights.md is written and committed.

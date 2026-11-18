# conrad-b3 results log

## Step 1. Consumers of TateTwistInvariantsInertia (VERIFIED, grep over the worktree and origin/wip/ht-merge, origin/main)
- ZInQKernel/: C8LocAlg.lean L90 (def), L98 `locAlgExponentEqWeight_of_tateInertia`; C8CFT.lean L506 `c8TwistFinite_of_leaves` (hypothesis hTT, used L515 only through L98);
  C8Poincare.lean L35 (field of `C8Inputs`), L43 (`g12DetPZ_of_inputs`); C8Printed.lean L28 (field of `C8Leaves`), L33, L41, L47.
- No other Lean consumer in the worktree. origin/main: none (C8 files not on main). origin/wip/ht-merge: the same five C8 files plus
  scratch copies (scratch/c8-conrad2, scratch/ht-abvar/HTDryRun.lean reads `C8Inputs`/`C8Leaves`).
- Tau Ceti Artin map normalization (VERIFIED, read): `isArithFrobeniusLift_of_mk_eq_artinMap_uniformizer` (Local/Unramified.lean L465): uniformizer -> arithmetic Frobenius;
  `localCyclotomicCharacter_artinMap_padic` (ExplicitCyclotomicSymbol/ArtinMap.lean L295): chi_cyc(Art u) = u^-1 for u in Z_p^x. Same normalization as Conrad p. 32 ("arithmetic normalization", page read 11-17 forwarded in the task).

## Step 2. Leaf ConradPropB3Qp and the merged leaf ConradAppB (new file ZInQKernel/Contrib/OneProof/C8ConradB.lean)
- `IsLocallyAlgebraicConrad p ψ n`: ∃ k, ∀ u ≡ 1 mod p^k, ∀ Artin lift σ of u, ψ σ = u^(-n) (Conrad p. 33, L = Q_p).
- `conradHTMult p ρ w := finrank Q_p (htSpace p ρ w)` (Conrad convention; chi_cyc has weight +1: H_w(Q_p(1)) ≠ 0 iff w = 1).
- `ConradPropB3Qp`: ψ : G_Qp → E^x continuous, IsLocallyAlgebraicConrad p ψ n → conradHTMult p (charRep ψ) n = [E:Q_p].
- `ConradAppB := ConradAppBQp ∧ ConradPropB3Qp`.
- definitional steps: `isLocallyAlgebraic_iff_conrad` (n ↔ -n, simp neg_neg); `htMult_eq_conradHTMult_neg` (rfl).
- `locAlgExponentEqWeight_of_conradPropB3 : ConradPropB3Qp → LocAlgExponentEqWeight`; `c8TwistFinite_of_conradB`.
- PR #86 (branch proof/poincare-complement-native-20261117 = 8050603bc, read with git show): FinalUnconditional.lean L24
  `theorem poincareComplement_proof : ZInQ.Contrib.AVB1.PoincareComplement := poincareComplement_of_square L6.NativeTheoremOfTheSquare_proof.{0}`;
  AVB1/Poincare.lean identical to HEAD (git diff empty). VERIFIED by reading; not merged, not compiled.

## Step 3. Compile (merged tree: origin/wip/ht-merge 027f637cd + conrad-b3; .lake/build reflink-copied from ~/dzq-wt/ht-merge, old base build kept as .lake/build-old-base)
- first build: C8ConradB L107 `Module.finrank_pos` failed (IsTorsionFree ℚ_[p] ↥E synthesis timeout); fixed with `finrank_pos_intermediateField` via `finrank_pos_iff_of_free` + `Module.Free.of_divisionRing`.
- `lake env lean ZInQKernel/Contrib/OneProof/C8ConradB.lean`: no output (no errors, no warnings). VERIFIED.
- `lake build ZInQKernel.Contrib.OneProof.C8Printed`: Build completed successfully (13414 jobs); C8ConradB, C8Poincare, C8Printed built. VERIFIED.
- `lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges ZInQKernel.Contrib.OneProof.ScholzeH1AbVar`: Build completed successfully (15983 jobs).
- `scratch/conrad-b3/Discharges.lean` (output discharges_out.txt): `#discharges: 30 open hypotheses, 11466 theorems checked, 16 discharge one`, none from the C8 files (expected: no bundle field is discharged by the C8 reroute); all nine #print axioms [propext, Classical.choice, Quot.sound]. VERIFIED.
- `scratch/conrad-b3/CBDryRun.lean` (output dryrun_out.txt): no errors; frozenTarget_cb, sixContactMin_of_open73CB, sixContactMin_of_open72_hm, locAlgExponentEqWeight_of_conradPropB3, c8TwistFinite_of_conradB, g12DetPZ_of_printed, c8Inputs_of_leaves: [propext, Classical.choice, Quot.sound]. The dry-run source mentions TateTwistInvariantsInertia nowhere (grep). VERIFIED.

## Step 4. Count (scratch/conrad-b3/count.py, count_out.txt; VERIFIED, computed)
- before (main 5f1fac790 kinds.tsv, H rows): 5/24 on 29.
- joint fold, ht-merge spec: 5/26 on 31 (5/25 on 30 with PR #86).
- joint fold, conrad-b3: 5/25 on 30 (5/24 on 29 with PR #86). Same numbers with the merged tree's kinds.tsv.

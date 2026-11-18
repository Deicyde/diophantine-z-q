# cox-lattice results log

- Base: origin/wip/cm-branch2 120fa22b (includes cm-branch2's CoxCore.lean); origin/main d435851d merged (0af3a3a6, clean).
- Target (verbatim): HDec.CMBranch.CoxProperLattice (ZInQKernel/Contrib/OneProof/CMBranch/ReducedPeriod.lean L65).
- 12:05 scratch/cox-lattice/Cox.lean (import Mathlib; verbatim copies of LeafQM.AV.conductor [made `noncomputable`:
  the original sits in a `noncomputable section`], IsImagQuadOrder, orderDisc, latticeMultipliers, CoxProperLattice;
  CoxCore discr_pair/ringOfIntegers_eq_closure/discr_order copied from cm-branch2 120fa22b) COMPILES:
  `HDec.CMBranch.CoxLattice.coxProperLattice_proof : CoxProperLattice`, axioms [propext, Classical.choice, Quot.sound].
  VERIFIED (lake env lean). Statement unchanged; no extra hypothesis needed.
  Proof steps: exists_nonint (f•ω ∈ R, ω ∈ 𝓞_k \ ℚ; AddSubgroup.nsmul_relIndex_mem) → α = φ(fω) ∉ ℤ multiplier →
  α = p+qτ, ατ ∈ ℤ+ℤτ, q ≠ 0 → integral quadratic for τ → exists_prim_form (divide by gcd, sign) →
  mem_mult_iff_order (Cox 7.5 elementary half: multipliers of c(ℤ+ℤτ) = ℤ+ℤaτ) → θ = φ⁻¹(aτ): R = ℤ+ℤθ,
  θ²+bθ+ac' = 0, θ ∉ ℚ (disc_neg) → discr_order: b²−4ac' = [𝓞_k:R]²·d_k = orderDisc R.
  The ring-isomorphism invariance of the discriminant is NOT needed: the isomorphism is used only to pull the
  generator aτ back to R, and the discriminant is computed in k.
- 12:13 ZInQKernel/Contrib/OneProof/CoxProperLattice.lean (imports CMBranch.PeriodLattice): lake build EXIT 0
  (11763 jobs). HDec.CMBranch.coxProperLattice_proof : CoxProperLattice; reducedCMPeriod_of_leaves_cox (t35,
  homLatticeCorr, t11b only). VERIFIED.
- 13:00 ZInQKernel/Contrib/OneProof/CoxProperLattice/Fold.lean (CMInputs3 = CMInputs2 \ coxProperLattice;
  sixContactMin_of_open72_cmbranch3): lake build EXIT 0 (15392 jobs). scratch/cox-lattice/Axioms.lean ->
  axioms-out.txt: all three theorems [propext, Classical.choice, Quot.sound]. VERIFIED.
- autofold.json: cm-branch2's hand-fold spec with the leaf coxProperLattice removed, 6th component filled by
  HDec.CMBranch.coxProperLattice_proof. Net vs cm-branch2: GLUE column 0, strict count (pending leaves = GLUE) -1,
  leaves -1. (Hand fold: autofold.py --dry-run does not apply; Fold.lean is the dry run.)
- Manuscript check L598-600: correct as written, no missing hypothesis (report §4). Label ELLIOT (uncited step);
  steps of the Lean proof on-the-spot (report §2).
- 13:05 origin/wip/cm-branch2 had pushed 8 commits (295488eb: cm-branch2 proved CoxProperLattice independently,
  CMBranch/CoxProof.lean, `HDec.CMBranch.coxProperLattice_proof`; CMBranch2.lean now defines CMInputs3; Open73).
  Merged (clean). Clash resolution: this task's theorem kept only as HDec.CMBranch.CoxLattice.coxProperLattice_proof
  (alias removed); Fold.lean rewritten over cm-branch2's CMInputs3: sixContactMin_of_open72_coxlattice.
  lake build Fold EXIT 0 (15396 jobs); axioms-out.txt standard; #discharges re-run: 30 open, 12378 checked,
  120 discharge one (16 pre-existing + 104 _r5 noise). autofold.json = cm-branch2's updated spec + alternative provider.

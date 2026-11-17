# carirr-odd log

- 2026-11-17 01:14 start. Base wip/r17-rebase 4095ce12; merged origin/main e1b31749 (a07d0e15) and
  origin/wip/carayol-herbrand 59f16e5e (499d2434, adds Contrib/OneProof/CarayolHerbrand.lean), no conflicts.
- The reviewer verdict file crowd-kit/ckpt/leaf-review/queue10-verdict.md is not in this tree nor in any origin/* ref
  (checked with git ls-tree on every remote branch): worked from the brief's summary of it.
- VERIFIED (read): main's open field is `carayolThmA : CarayolPrinted.CarayolThmA` (TailZ62 OpenResearchLeaves38,
  kinds.tsv row: consequence, GLUE/GLUE). r17-rebase's `CarayolThmAIrr` and carayol-herbrand's `CarayolThmAIrrDDT`
  are not folded.
- VERIFIED (read): Mathlib `cyclotomicCharacter L p : (L ≃+* L) →* ℤ_[p]ˣ`, `modularCyclotomicCharacter L hn`;
  Tau Ceti (vendored) `TauCeti.cyclotomicCharacter_eq_neg_one` (inverting all p-power roots ⇒ -1) and
  `TauCeti.char_neg_one_of_mem_cuspFormCharSpace` (χ(-1) = (-1)^k for a nonzero form);
  `DSCoeffExt.mem_fieldRange_of_isIntegral`.
- COMPILED scratch/carirr-odd/Odd1.lean (6 s, no errors): cycN, cycL, exists_complexConj, cycL_eq_neg_one,
  cycN_eq_neg_one, chi_neg_one_eq_one, irreducible_of_absIrreducible, padicInt_ringHom_ext.
- COMPILED ZInQKernel/Contrib/OneProof/CarayolDDTOdd.lean (lake build OK, no warnings from the file). Axioms of all 13
  declarations standard (axioms.txt). Leaves: CarayolDDT.CarayolDDT31 (absolutely irreducible over
  AlgebraicClosure K_λ; ∃ continuous ι : ℤ_ℓ → K_λ with det ρ(σ) = ψ(cycN σ)·ι(cycL σ) where ψ(cycN σ) ∈ K_f;
  unramified/trace; DDT-integral conductor), CarayolDDT31Cond (condExp conductor). carayolDDT31_iff_cond proved.
- autofold dry runs (autofold.json, autofold-cond.json; field carayolThmA): strict 16/18 on 34 -> 17/17 on 34,
  strictest 16/18 -> 17/17.
- COMPILED lake build +OneProof.Main +OneProof.Discharges +CarayolDDTOdd: 14276 jobs OK (build-main.txt; first attempt
  stopped by the harness's background time limit, rerun resumed).
- #discharges (discharges.txt): DISCHARGES [OpenResearchLeaves38.carayolThmA] by CarayolDDT.carayolThmA_of_DDT31,
  still assumes [CarayolDDT.CarayolDDT31], standard axioms; same for ..._of_DDT31Cond.
- COMPILED AutofoldDryRun.lean (dry-run output minus line 1): sixContactMin_of_open56 standard axioms.

# r17-bypass (2026-11-15)

**Verdict:** `r17 : LadicCond.CarayolR17'` (Carayol) cannot be removed. It is used once, in `G0ModNewform.g15` (step D5, from the conductor to the level), at ℓ = 5 (every p ≠ 5) and ℓ = 3 (p = 5). There `f` is the newform from Pan's eigenform and `N` is arbitrary, so the instances are general: neither vacuous nor special. g15 needs only `v_p(N) ≤ a(ρ|G_{ℚ_p})` for `p ∣ N`. This weakest form is `CarayolLevel.CarayolLevelLe`, the deep half of Carayol's equality. No bundle field gives it: R14, R16 and NOS say nothing about `ρ_f` at `p ∣ N`.

**Main result: an autofold-compatible discharge.** `CarayolLevel.carayolR17'_of_newformRepConductor : NewformRepConductor → LadicCond.CarayolR17'` is in `ZInQKernel/Contrib/OneProof/CarayolLevel.lean` (kernel imports only). The new leaf is the existence form: some semisimple ρ attached to `f` has conductor `v_p(N)` at every p ≠ ℓ. That is how the result is printed, for ρ_{f,λ} itself. The transport to every semisimple attached ρ is now proved in Lean:
- Brauer–Nesbitt and T18, from the kernel;
- new: `condExp_eq_of_intertwine`, which needs no `SwanIndependent`.

The converse is also in Lean (with R14's existence), so the leaf is no stronger than r17. The leaf's kind is `published`, flagged `pending reading` (DDT 1997 §3.1 and Carayol §0, UNVERIFIED). It counts GLUE until someone reads the print, so the count stays at 46/10 now. If a reading confirms the print, the strict GLUE count drops by one.

**Compiles (VERIFIED):**
- the contribution, with no warnings in the file;
- `scratch/r17-bypass/Bypass.lean`: `g15_of_levelLe` … `afterG7_of3_levelLe`, the consumer chain up to `afterG7_of3` from `CarayolLevelLe`, standard axioms;
- `#discharges`: `DISCHARGES [OpenResearchLeaves21.r17] … still assumes: [CarayolLevel.NewformRepConductor]`, standard axioms;
- the autofold dry run of `scratch/r17-bypass/autofold.json` gives `sixContactMin_of_open29`, which compiles with standard axioms.

**Remains:**
- reading the conductor packaging in print, to clear the flag;
- the fold itself (integrator);
- a bypass fold to `CarayolLevelLe` is not recommended: it would not change the count.

Report: docs/research/r17-bypass.md.

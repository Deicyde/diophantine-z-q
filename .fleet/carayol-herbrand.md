# carayol-herbrand (fleet summary)

**Result.** r17-rebase's leaf `CarayolPrinted.CarayolThmAIrr` is now proved equivalent in Lean to DDT 1997 Thm 3.1 with
DDT's own conductor, `codim V^{I_p} + ∫₀^∞ codim V^{I_p^u} du` (upper numbering). The Herbrand step is a theorem, not a
reading risk. New file `ZInQKernel/Contrib/OneProof/CarayolHerbrand.lean`, no sorry, axioms
`[propext, Classical.choice, Quot.sound]`:

* `adaptedExists_of_norm`: adapted finite levels exist for continuous `ρ : G_{ℚ_p} → GL_n(K)`, where `K` is ultrametric
  with `‖ℓ‖ < 1` and `ℓ ≠ p`. The kernel had this only for `ℚ̄_ℓ`; this covers `K_{f,λ}` = Mathlib's `adicCompletion`.
* `condExp_eq_ddt`: `condExp ρ = codim V^{I_p} + ∫₀^∞ codim V^{upperAbs p u} du`, from the kernel's proved Swan/Herbrand
  glue in `OneProof/H/TailB.lean`. That glue is the finite-level change of variables, `G^u ⊆ P` for `u > 0`, and
  Herbrand's theorem with compactness.
* `CarayolThmAIrrDDT` (new leaf, conductor in DDT's form), `carayolThmAIrr_iff_DDT`, and
  `carayolR17'_of_DDT : CarayolThmAIrrDDT → EigenformCoeffFieldFinite → LadicCond.CarayolR17'`.

**Checks (VERIFIED).**
* `#discharges` on merged main: `DISCHARGES [OpenResearchLeaves31.r17] by CarayolHerbrand.carayolR17'_of_DDT`, standard
  axioms.
* autofold dry run (`scratch/carayol-herbrand/autofold.json`): 11/18 → 12/17 in both the strict and the strictest
  count (**GLUE −1**). The generated module compiles (`sixContactMin_of_open49`, standard axioms).
* `autofold-after-r17rebase.json` covers the case where r17-rebase's fold lands first (count-neutral).

**Leaf rating.** `carayolThmAIrrDDT` is in printed form, published, flag `unread`. The conductor clause transcribes DDT
§2 p. 54. The other clauses are unchanged from `CarayolThmAIrr`. DDT's page and theorem numbers come from the task's
reading; I could not re-read DDT (no network), so they are UNVERIFIED.

**Remaining.**
* A statement check of DDT 1997 §2 p. 54 (the conductor definition) and Thm 3.1 (a)–(d): irreducible, `det = ψε`,
  `Frob_p` normalization, (d).
* `eigenformCoeffFieldFinite` is unchanged (composite).
* The fold itself is the integrator's step.

Report: `docs/research/carayol-herbrand.md`.

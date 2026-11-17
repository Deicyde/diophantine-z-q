# gamma0-qexp: done. hQ is proved (−1, no new leaf)

**Verdict.** `ZInQ.GZAlg.Gamma0QExpansion`, the `q`-expansion principle for `Γ₀(N)` and the frozenTarget binder
`hQ`, is proved in Lean as stated, for every `N ≥ 1`. Its proof uses no new hypotheses, and its axioms are
`[propext, Classical.choice, Quot.sound]`:
`ZInQ.Contrib.Gamma0QExp.gamma0QExpansion_proof` in `ZInQKernel/Contrib/OneProof/Gamma0QExpansion.lean`. The
helpers are in `ZInQKernel/Contrib/OneProof/Gamma0QExp/` (6 files, 87 KB). The proof is the classical one, all
glue proved in Lean:
1. Holomorphic and meromorphic level-one functions are rational in `j`: Mathlib's `hasSum_qExpansion` and FLT's
   `coeff_eq_zero_of_hasSum_of_slash_invariant`, plus pole clearing on the truncated fundamental domain with
   Riemann's removable singularity theorem.
2. Symmetric functions over `SL₂(ℤ)/Γ₀(N)` give `B(j,j_N)·g = A(j,j_N)`, with `B` nonzero by Bézout reduction
   and separation of the conjugates of `j(Nτ)`.
3. The identity passes to `q`-expansions by a shift and continuity argument.
4. A `ℚ`-linear functional `ℂ → ℚ` descends it from `ℂ((q))` to `ℚ(jq, jqN)`.

**What compiles (VERIFIED, on 0e3c3125).**
* `lake build +ZInQKernel.Contrib.OneProof.Gamma0QExpansion` succeeds.
* `#discharges` reports `DISCHARGES [hQ] by ZInQ.Contrib.Gamma0QExp.gamma0QExpansion_proof`, with
  `still assumes: []` and standard axioms (`scratch/gamma0-qexp/discharges.out`).
* `scratch/gamma0-qexp/FoldCheck.lean` proves `ZInQ.FrozenTarget` without `hQ` (`frozenTarget_noQ`), with
  standard axioms.
* `scratch/gamma0-qexp/Statement.lean` holds verbatim copies of the Prop, checked by `rfl`.

**What remains.** The integrator's manual fold of `ZInQKernel/OneProof/Main.lean`, written out in
`docs/research/gamma0-qexp.md` §5: add the import, drop the `hQ` binder, and pass `gamma0QExpansion_proof`. After
that, OPEN.md row `hQ` (issue elliotglazer #76) can be closed. Nothing is unproved.

Report: `docs/research/gamma0-qexp.md`. Log: `scratch/gamma0-qexp/log.md`.

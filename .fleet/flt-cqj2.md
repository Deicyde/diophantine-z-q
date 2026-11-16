# flt-cqj2 — fleet summary

**Result: `FltCqj.ModularEquationGeneric` is proved, and with it `ZInQ.RLeaf.X0Transitive`, using only the standard
axioms. Igusa's theorem (`igusaGL2`) can leave the single proof, and no leaf replaces it.**

- **Port.** Anthropic FLT's proof cone of
  `WeierstrassCurve.bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j` has 661 modules. The 414
  that were missing are now ported from `~/flt-src` @6e837e75 (Lean 4.33.1) to Lean 4.35 / Mathlib v4.35, under
  `ZInQKernel/Contrib/CloudB2X0Transitive/Vendor/AnthropicFLT/`. All of them build, and no module failed to port.
  - Twelve kinds of API change were needed; each is marked `-- [port]` and sits inside a proof, an import or an
    instance name.
  - 24 FLT names clash with Tau Ceti. They are renamed `…_aflt`, which also fixes one auto-generated instance name.
  - LICENSE is unchanged. A new NOTICE file carries a "Modified for the Z-in-Q kernel" paragraph, and
    `SOURCE_MANIFEST.flt-cqj2.json` records each module's upstream sha256.
  - A diff audit against upstream explains every changed line.
  - The `MapsTo` half has no smaller cone: FLT's proof runs by induction on `N`, and that induction uses injectivity.
- **Deliverable.** `ZInQKernel/Contrib/OneProof/ModularEquationGeneric.lean` proves three theorems:
  `FltCqj2.cyclicQuotientJBijOn_proof`, `modularEquationGeneric_proof` and `x0Transitive_proof`.
  - The build succeeds (9990 jobs).
  - Verbatim copies of the statements match by `Iff.rfl`, and all three proofs use only the standard axioms.
  - `#discharges` finds 3 discharges, none from this file. That is expected: `igusaGL2`'s type is the stronger
    `IgusaGL2`, so autofold cannot apply.
- **Fold.** `scratch/flt-cqj2/FoldProved.lean` is the flt-cqj bypass fold with the field `igusaGL2` deleted and
  `x0Transitive := FltCqj2.x0Transitive_proof`. It compiles against `Main`.
  - `frozenTarget_cqj2` has the same binders as `frozenTarget`, except that `t` is the bundle without `igusaGL2`.
    It uses only the standard axioms.
  - A metaprogram confirms that the bundle fields are the original ones minus `igusaGL2`, with the same types.
  - Main.lean edit for the integrator: switch `frozenTarget` to this bundle generation.
  - Counts: one fewer published LEAF, and no new leaf or glue.
- **What remains.** The integrator still has to fold this into `OneProof/H` and `Main`, and `Main` would then import
  the 661-module vendored cone. Nothing in this task's scope is left open.
- Report: `docs/research/flt-cqj2.md`. Log: `scratch/flt-cqj2/log.md`.

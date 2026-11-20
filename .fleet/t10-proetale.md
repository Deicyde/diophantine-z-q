**Scoped stop: `t10TateDuality` remains GLUE. Count delta: 0.** Lean now has the forward local lift construction for degree-one classes, the canonical reductions to the finite pro-étale groups, and their compatibility with the row's transport. The identification with classical étale cohomology remains open.

**Citation gap (UNVERIFIED against the source):** `diophantine_zq.tex:10967–10972` cites Milne's 2008 Part I, Theorem 12.1(a) alone for equivariance. The earlier audit points separately to Remark 12.5. The 1986 draft is unchanged; its exact printed wording and semilinear scope are unverified.

All three new modules compile. `ExtensionFibres.lean` represents Ext¹ classes by lifts from an injective presentation and proves local existence and unique translation. `Tower.lean` gives compatible reductions from the row's cohomology, proves they commute with its actual scheme transport, and proves the surjectivity of the degree-zero difference map. `Transport.lean` checks that the classical pullback is along `1 × Spec(σ)`, that the normalized graph transforms by `σ⁻¹` on points, and that the two required squares compose. The check file reports only the three standard axioms for all 20 theorems.

The remaining work is to compare finite degree-one cohomology on the two sites using representable torsors, prove that the compatible reductions give an isomorphism in degree one, and justify semilinear naturality for the same Milne family. Neither the row nor its consumers were changed.

[Scoped report](../docs/research/t10-proetale.md) · [Verification output](../scratch/t10-proetale/axioms-output.txt). Lean implementation: `83f8086db`. Report: `2302b7f21`.

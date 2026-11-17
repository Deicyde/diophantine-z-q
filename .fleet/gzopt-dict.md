# gzopt-dict (fleet summary)

**Verdict: target met.** gz-optimal's GLUE-rated leaf `GZOptimal.GrossZagierModuliOptCd` (analytic `φ = (X, Y)`
on `ℍ`) is proved in Lean, with standard axioms, from two leaves in printed form
(`ZInQKernel/Contrib/OneProof/GrossZagierAlgebraic.lean`):

- `GZAlg.GrossZagierAlgOptCd`: Gross–Zagier (1986, Thm I.6.3 and V.2.1), strong Weil case, with `φ` a morphism
  over `ℚ` of the algebraic curve `X₀(N)`, given as `φ^* : ℚ(E) →ₐ[ℚ] ℚ(X₀(N))`. Here `ℚ(X₀(N)) = ℚ(j, j_N)` is
  FLT's `modularFunctionField` (`q`-expansions), `φ(∞) = O` means `ord_q φ^*x < 0`, and the complex points come
  through the uniformization.
- `GZAlg.Gamma0QExpansion`: the `q`-expansion principle for `Γ₀(N)` (Shimura 1971 Prop. 6.9 / DS §7.5–7.6,
  UNVERIFIED locators).

**Theorems:**
- `grossZagierModuliOptCd_of_alg : Gamma0QExpansion → GrossZagierAlgOptCd → GrossZagierModuliOptCd`;
- `grossZagierFormulaCd_of_alg : GrossZagierAlgOptCd → Gamma0QExpansion → EtaW32Character → GrossZagierFormulaCd`,
  through period-odd.

So `hL3` in route A rests on printed leaves only. GLUE −1, no new glue.

**What the bridge proves:**
- the consumer's `X, Y` have rational `q`-expansions;
- the Weierstrass equation transfers to them (uniqueness of Taylor coefficients, gz-heegner's `tay` calculus);
- the pole at `∞` transfers;
- `(x, y)` gives an injective map from the coordinate ring (`x` transcendental, going up), and so `φ^*`.

**Bonus (helper `GrossZagierAlgebraic/X0Model.lean`).** `ker((X, Y) ↦ (jq, jq(q^N))) = (Φ_N)` and
`X0Field N ≃+* Frac(ℚ[X, Y]/(Φ_N))`. Also, the generators of `X0Field N` are the `q`-expansions of `j(τ)` and
`j(Nτ)`.

**Checks:**
- `lake build` passes;
- `#print axioms` is standard for all main theorems;
- `scratch/gzopt-dict/MainEdit.lean` proves `ZInQ.FrozenTarget` from the current Main hypotheses, with `hL3`
  replaced by the `C_d` chain and the three leaves;
- `#discharges`: `56 open, 3984 checked, 10 discharge one`, none by `GZAlg`. This is expected: the field exists only
  after the `C_d` split is folded.

**autofold specs:**
- `scratch/gzopt-dict/autofold.json`: field `grossZagierModuliOptCd`, two published leaves;
- `autofold-formula.json`: field `grossZagierFormulaCd`, three leaves.

Both dry runs report "not a field of the current bundles", as for period-odd.

**What remains:**
- folding the `C_d` split;
- optimality is still analytic (`IsOptimalParam`, gz-optimal's form), because Mathlib has no `J₀(N)`;
- `Gamma0QExpansion` itself is not formalized.

Report: `docs/research/gzopt-dict.md`.

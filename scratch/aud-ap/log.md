# aud-ap log

## Step 0 (start)
- Worktree at c399a64 (ap-lean report commit). No .lake; need `lake exe cache get` + build.

## Step 1 (scope)
- Diff merge-base(main)..HEAD in ZInQKernel/, lean/, scripts/: only new files (PrimeAP.lean, AP/*.lean, AP.lean)
  plus Main.lean (+23: imports, docstring bullet, new theorem) and ZInQKernel.lean (+1 import). Target.lean,
  SixContactMin, CertifiedRank, FrozenTarget untouched. CORRECT.
- Variant signature: (hH : SixContactMin) (hCR : CertifiedRank) (hAP : GoodPrimeAP) : FrozenTarget — same
  conclusion and same two other hypotheses as `exists_bounded_integer_polynomial_defining_integers_of`. CORRECT.
- S_b = S_ht ∪ catalogue, S_ht = primes ≤ 324 (filter of range 325), catalogue = catalogueFinset W 22 324 (Finset,
  so finite; nonempty since contains 2). Coe to catalogueSet proved (Syntax.catalogueSet_eq). No junk: S_b is the
  paper's S_b. CORRECT (to double-check catalogueFinset def).
- Build: started `lake build ZInQKernel` (Mathlib packages copied from a sibling worktree, cache get had no network).

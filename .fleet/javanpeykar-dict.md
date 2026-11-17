# javanpeykar-dict (2026-11-16)

**Verdict: `javanpeykarBound` is back to LEAF.** The field `ZInQ.HeightSplit.JavanpeykarBound` (bundle
`OpenResearchLeaves26`) is proved, standard axioms only, from two theorems in printed form:

    JavanpeykarDict.javanpeykarBound_of_printed_stichtenoth :
      JavanpeykarPrinted → ConstantFieldExtensionUnramified → ZInQ.HeightSplit.JavanpeykarBound

* `JavanpeykarPrinted`: Javanpeykar 2014 Thm 1.1.1 at `X = X₀ ×_K ℚ̄`, with `Jac(X)` the vendored `Pic⁰`
  representative, `g = dim H¹(X_ℚ̄, 𝒪)`, a Belyi function of `X_ℚ̄` over `ℚ̄`; rated printed form (unread flag).
* `ConstantFieldExtensionUnramified`: Stichtenoth, Thm 3.6.3(a) (constant field extensions are unramified), in
  valuation-subring form; printed form, theorem number UNVERIFIED (not read).

All three dictionary steps of the 11-16 pass are proved in Lean: (1) kernel Jacobian ≅ `Pic⁰` (isj1-dict's proof,
copied) plus a new proof that `IsStableFaltingsHeight` is an isomorphism invariant; (2) `dim J = genus of X_ℚ̄`
(vendored smooth dimension + genus base change); (3) `K`-rational Belyi function → Belyi function of `X_ℚ̄`, same
degree, via a new proof that `ℚ̄(X_ℚ̄) = K(X) ⊗_K ℚ̄` (`functionField_baseChange`, Mathlib affine base change of
sections) and field theory of the constant field extension, from Stichtenoth.

**Compiles:** `ZInQKernel/Contrib/OneProof/JavanpeykarDict.lean` + `JavanpeykarDict/{Basic,BelyiAlgebra,FunctionField}.lean`
(lake build OK); `#discharges` shows the discharge (scratch/javanpeykar-dict/Discharges-output.txt); autofold spec
`scratch/javanpeykar-dict/autofold.json` — dry-run strict count 34/11 on 45 → 35/11 on 46 (no GLUE rise), generated
module compiles with `sixContactMin_of_open36` on standard axioms.

**Remains:** human readings of both leaves (Stichtenoth's number unverified); `locators.md`/`kinds.tsv` rows for the
integrator (proposed in docs/research/javanpeykar-dict.md §5); the archimedean height dictionary (height-dict) is untouched.
Report: docs/research/javanpeykar-dict.md.

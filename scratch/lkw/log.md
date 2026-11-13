# lkw results log

## Step 1 (2026-11-13 03:20 PST)
- VERIFIED (grep of tc-oct16/nov01/main): no local Kronecker–Weber and no norm group of ℚ_p(μ_m) in Tau Ceti.
- VERIFIED: PadicAlgCl p := AlgebraicClosure ℚ_[p] (Mathlib Padics/Complex.lean:54); TC's G_K = Gal(AlgebraicClosure K/K).
- Needed TC modules (all oct16, all in kw-rest.txt ⇒ vendored by tc-port): Local.Reciprocity, Local.ArtinMap,
  Local.Cyclotomic, Local.ExplicitCyclotomicSymbol.ArtinMap. Closure of the last at oct16: 559 modules (closure.py).
- Derivation written in docs/research/lkw.md (Lemmas A, B, C). Local existence not needed.

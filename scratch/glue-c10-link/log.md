# glue-c10-link results log

## 11:45 PST — Link.lean §§1-3 compile (VERIFIED, `lake env lean`, no errors)
Imports ZInQKernel.HDecomp.{Objects, C10.C10, C10.Trace, Descent.ProjRep} (built with
`lake build` of those four modules, 60 s).
- `subRep u ρ hc : Representation E G u.W` — r = ρ|_{e₀₀V}.
- `conj_splitEquiv` — splitEquiv.conj (ρ g) = prodMap (r g) (r g).
- `trace_eq_two_mul_trace_subRep` — tr ρ(g) = 2·tr r(g) (FiniteDimensional E V).
- `trace_rho` — tr (rho T a β g) = (β g)⁻¹ * a g * tr (T g).
- `finite_of_baseChange` — E ⊗_K M finite over E ⇒ M finite over K.
- `endE φ ℓ E` := ((homT φ).baseChange ℚ_ℓ).baseChange E.
- `trace_endE_indep` (from CharPolyIndepOfEll) — ∃ t : ℤ, ∀ ℓ ≠ char k, ∀ E ⊇ ℚ_ℓ with
  E ⊗ V_ℓ(A) finite, tr_E (endE φ ℓ E) = t.

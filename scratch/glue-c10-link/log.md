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

## 11:55 PST — Link.lean §§4-5 compile (VERIFIED, no errors)
- `rhoL` — ρ_ℓ = rhoRep T (ι∘c) (ι∘ε) (ι∘a) (ι∘β) with the cocycle relations stated in C.
- `rhoL_commute`, `rL` (r_ℓ = subRep of rhoL).
- `FrobCompare ℓ Tσ α N` := ∃ Φ : V ≃ₗ[E] E ⊗[ℚ_ℓ] V_ℓ(Ā), Φ.conj (N • Tσ) = endE α ℓ E.
- `trace_T_of_frobCompare` — ∃ t : ℤ, ∀ ℓ ≠ char k, FrobCompare ℓ Tσ α N → N·tr Tσ = t.
- `trace_link` — ∃ t : ℤ, ∀ ℓ ≠ char k, ∀ descent data, FrobCompare ℓ (T σ) α N, N ≠ 0 →
  tr r_ℓ(σ) = ι((β σ)⁻¹ * a σ * (t/N) / 2).  [c_p = ½ β(σ)⁻¹ a_σ tr α_σ, tr α_σ = t/N]

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

## 11:51 PST — Link.lean §§6-7 compile (VERIFIED, `lake env lean`, no errors; one style warning)
- `trace_link` strengthened: ∃ t : ℤ, (∀ ℓ ≠ char k, ∀ E, tr_E (endE α ℓ E) = t) ∧ (link).
  E, V, G, C in `Type` (one universe; the ∃ t must serve ℓ = 3 and 5 at once).
- `cast_ne_zero_of_charP` — (ℓ : k) ≠ 0 for CharP k p, p ≠ ℓ primes.
- `trace_link_three_five` — given 3, 5 ∈ S, p ∉ S, and (k, CharP k p, Ā, α', N ≠ 0) with
  FrobCompare at 3 and 5: ∃ x : C, tr r₃(g) = ι₃ x ∧ tr r₅(g) = ι₅ x.
- `c10_of_trace_link` — GlueC10.c10 applied with r_ℓ := rL … and c := a_f; hr₅ from h₅ + hρ₅,
  hr₃ from trace_link_three_five + injectivity of ι₅. Conclusion r₃ ≅ ρ₃ as k₃[G_ℚ]-modules.
- non-vacuity `example : FrobCompare ℓ (endE α ℓ E) α 1` (Φ = refl).
- `#print axioms` on trace_eq_two_mul_trace_subRep, trace_endE_indep, trace_link,
  trace_link_three_five, c10_of_trace_link: [propext, Classical.choice, Quot.sound].
Pitfall: the existential `∃ t` fixes universes; mixing Type* in callers gave a whnf timeout.

## 11:56 PST — Link.lean §8 compiles (VERIFIED, no errors, no warnings)
- `homComp f g` (pkg-I3 Hom composition, Hom.mk' (f.hom ≫ g.hom)); `homT_homComp`.
- `Vmap ℓ f` := (homT f).baseChange ℚ_ℓ; `conj_baseChange`.
- `frobCompare_of_squares` — from hΨ : Ψ.conj (N • Tσ) = (Vmap μ' ∘ σ_*) ⊗ E,
  hS1 : red' ∘ σ_* = Vmap F ∘ red, hS2 : red ∘ Vmap μ' = Vmap μ̄' ∘ red'  ⟹
  FrobCompare ℓ Tσ (homComp F μ̄') N.  Axioms: propext, Classical.choice, Quot.sound.

## 11:58 PST — Link.lean complete (VERIFIED, `lake env lean`, no errors, no warnings)
- `FrobSquares ℓ μ' F μ̄' Tσ N` := ∃ σ_* red red' Ψ, hS1 ∧ hS2 ∧ hΨ.
- `frobCompare_of_frobSquares`.
- `c10_of_squares` — c10_of_trace_link with hFrob replaced by hSq (∃ L k [CharP k p] A Aσ μ' Ā Ā'
  F μ̄' N ≠ 0, FrobSquares at 3 and 5).
- `#print axioms` (7 theorems): [propext, Classical.choice, Quot.sound].

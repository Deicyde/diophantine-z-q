# Route 1 of nt-h §4.2 (Serre's argument at large ℓ): an audit against the sources

Labels. **CORRECT**: checked here, step by step, against the manuscript `diophantine_zq.tex`
(frozen 11/5 line numbers) and against the source statement as quoted. **GAP**: missing or wrong;
the text says what fails and how to repair it. **UNCHECKED**: the source could not be read here, so
its exact statement and numbering are not confirmed. Secondary restatements that were read are
named, and the primary statement is then still marked UNCHECKED.

## Verdict

**Proved after the listed repairs, with the constants unchanged.** The repaired argument still
rests on three primary statements that could only be read through published restatements:
Serre's conjecture in its strong form, Raynaud's bound on the inertia exponents of finite flat
vector space schemes, and Serre's weight recipe. All three are marked UNCHECKED below.

Route 1 does what nt-h claims. For each non-CM fibre it gives a weight-2 newform `f` of level
`N_f ≤ QM²` with `tr r_λ(Frob_p) = a_p(f)` for almost all `p`, and that is everything the transfer
step (lines 858-905) consumes. It replaces Pan's Theorem 1.0.4 (A011, modular part) and removes the
de Rham comparison (A009), Berger's theorem (A010), Conrad's local algebraicity and the separate
Carayol leaf. Li and Shimura (the rest of A011) and the Faltings Hom theorem (A063) stay. No
constant of lines 858-966 changes, since they depend on `f` only through `N_f ≤ QM²`.

None of the seven steps fails. The findings are about citations and justifications:

- **F1 (moderate).** Step 5 cites Khare–Wintenberger alone. The published proof of Serre's
  conjecture also uses Kisin, *Modularity of 2-adic Barsotti–Tate representations*, Invent. Math.
  178 (2009) 587-634, for even conductor. Nothing makes `N(r̄_λ)` odd: `2 ∈ T` always, `A` may be
  bad at 2, and `β` may ramify at 2 (line 708). So Kisin's theorem must be cited too. If Khare and
  Wintenberger's published statement has only the weak form, the classical level and weight
  optimization belongs to the citation as well. Either way the trust base gains Kisin's paper.
- **F2-F4 (minor).** Step 3 (weight 2) is true, but its written proof has three defects. It works
  over `O_{L_v}`, where the representation is not the Tate action. It cites Raynaud's uniqueness
  (§3.3) for a descent the argument does not need, and omits the inputs it does need: Raynaud's
  inertia exponents (§3.4) and "finite flat implies peu ramifiée". It asserts the determinant
  without proof.
- **F5 (minor).** Step 4 cites "Serre 1987, §1.2" for "reduction does not raise the conductor".
  That attribution is unconfirmed, and the step does not need it: the manuscript's local bounds
  apply word for word to `r̄_λ`.
- **F6 (minor).** Step 6 needs two lines of bookkeeping: pigeonhole over pairs (newform, embedding),
  and note that `t_p` is an algebraic integer.
- **F7 (minor, framing).** Khare–Wintenberger and Kisin use `p`-adic Hodge theory (finite flat and
  potentially Barsotti–Tate deformation rings) inside their proofs. So "no `p`-adic Hodge theory
  left in H" (nt-h route 2) is true of the direct citations only, just as Carayol stays inside the
  citation.

## 1. The objects (manuscript, lines 610-857; CORRECT as read)

Fix `u ∈ ℚ \ 𝒞` with a non-CM fibre: `A/K`, `End⁰(A_ℚ̄) = B = (2,-3)`, `O = ℤ[i,(1+j)/2] ⊂ End(A_ℚ̄)`.

- `K` is normal, `[K:ℚ] ≤ 324!`, and unramified outside `T = S ∪ supp M_S(u)`. `A` has good
  reduction outside the places over `S` (lines 562-567). `S` contains every prime `≤ 324`.
- `L ⊇ K` defines all geometric endomorphisms and all the conjugacy isogenies `μ_σ`, and is
  unramified outside `T` (lines 581-593).
- `β : G_ℚ → μ_{2m}` has `β² = χ`, coboundary `ε`, and is unramified outside `T` (lines 668-710; the
  final twist removes its inertia outside `T`). `L'` is the kernel field of `β|_{G_L}`. It is Galois
  over `ℚ`, unramified outside `T`, and has degree `≤ QM`.
- For each `ℓ` and each embedding `ι_ℓ : C → ℚ̄_ℓ`,
  `ρ_ℓ(σ) = β(σ)^{-1} a_σ μ_σ ∘ σ` on `V_ℓ(A) ⊗ E_λ` is a representation of `G_ℚ`, and
  `ρ_ℓ ≅ r_ℓ ⊕ r_ℓ` by matrix units. **On `G_{L'}`, `ρ_ℓ` is the Tate action of `A`** (line 732).
  On `G_L` it is the Tate action twisted by the character `β^{-1}|_{G_L}`.
- For `p ∉ T`, `p ≠ ℓ`: `t_p = ½ β(σ)^{-1} a_σ tr(μ̄_σ ∘ F)` is one element of `C` with
  `ι_ℓ(t_p) = tr r_ℓ(Frob_p)` for every `ℓ ≠ p` (lines 781-790). The manuscript states this for
  `ℓ = 3, 5`, but its argument works for every `ℓ ≠ p`: it uses only good reduction at `p` and the
  `ℓ`-independence of characteristic polynomials of endomorphisms.
- `r_ℓ` is odd (lines 742-752; `r_ℓ(c)` has eigenvalues `1, -1`), and is unramified outside
  `T ∪ {ℓ}`.
- Local conductor bounds (lines 796-857), for `p ≠ ℓ`. If `p ≤ R`, every absolute upper ramification
  group `G^u_{ℚ_p}` with `u > U_0` acts trivially through `ρ_ℓ`. If `p > R` and `p ∈ T`, wild inertia
  acts trivially. If `p ∉ T`, `ρ_ℓ` is unramified. These proofs use only that wild inertia above
  `U_0` acts trivially on `V_ℓ(A)` for `ℓ ≠ p`, plus a separate analysis of `β`. So they hold for
  every `ℓ ≠ p`.

`r̄_λ` denotes the semisimplified reduction of `r_ℓ` (for the embedding `ι_ℓ`, `λ` the induced
prime). Once step 1 shows it is absolutely irreducible, it does not depend on the lattice.

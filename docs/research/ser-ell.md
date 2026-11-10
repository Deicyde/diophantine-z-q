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
  bad at 2, and `β` may ramify at 2 (line 707). So Kisin's theorem must be cited too. If Khare and
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
  `ρ_ℓ ≅ r_ℓ ⊕ r_ℓ` by matrix units. **On `G_{L'}`, `ρ_ℓ` is the Tate action of `A`** (line 731).
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

## 2. Audit records for steps 1-7

Each record follows the format of `docs/theorem-application-audit/`: source, statement, hypotheses
checked, conventions, and the object consumed downstream. Fix a prime `ℓ ∉ T` (so `ℓ > 324`) that
lies above the Masser–Wüstholz threshold of R1. Infinitely many such `ℓ` exist.

### R1. Residual absolute irreducibility (step 1): CORRECT

- **Source.** Masser–Wüstholz, *Refinements of the Tate conjecture for abelian varieties* (Abelian
  varieties, Egloffstein 1993, de Gruyter 1995), §1, Corollaries 1 and 2: UNCHECKED, not readable
  here. It was read as restated in Zywina, *An effective open image theorem for abelian varieties*,
  arXiv:1910.14171, **Theorem 2.4** (numbering confirmed from the source). The non-effective
  versions are due to Faltings and Zarhin (UNCHECKED). The audited A008 (Faltings 1983, Satz 3, 4)
  is the `ℓ`-adic statement and does **not** give this.
- **Statement (Zywina 2.4).** Let `A/K` be an abelian variety over a number field and `L/K` finite.
  There are `c, γ > 0`, depending only on `dim A`, such that for `ℓ ≥ c·max([L:ℚ], h(A))^γ` the
  `𝔽_ℓ[G_L]`-module `A[ℓ]` is semisimple and `End(A_L) ⊗ 𝔽_ℓ → End_{𝔽_ℓ[G_L]}(A[ℓ])` is an
  isomorphism. Here `h` is the stable Faltings height.
- **Hypotheses checked.** Apply it with `L = L'`. Then `End(A_{L'}) = End(A_ℚ̄)` because `L ⊆ L'`
  defines every geometric endomorphism (line 591). That ring is an order of `B` containing `O`, and
  `O` is maximal, so it equals `O`. The Gram determinant of the reduced trace on the basis
  `(1, i, (1+j)/2, (i+ij)/2)` is `-36`, so the reduced discriminant is 6 (computation A of §6).
  For `ℓ ∤ 6`, `O/ℓO` is central simple of dimension 4 over `𝔽_ℓ`, hence `≅ M₂(𝔽_ℓ)` by Wedderburn.
  Matrix units then give `A[ℓ] ≅ W ⊕ W` with `dim W = 2` and `End_{G_{L'}}(W) = 𝔽_ℓ`. A semisimple
  module with commutant `𝔽_ℓ` is absolutely irreducible: over `𝔽̄_ℓ` it stays semisimple and its
  commutant is `𝔽̄_ℓ`.
- **Passage to `r̄_λ`.** On `G_{L'}`, `ρ_ℓ` is the Tate action, so
  `(ρ̄_ℓ|_{G_{L'}})^{ss} ≅ (W ⊗ k_λ)²`. Also `ρ_ℓ ≅ r_ℓ ⊕ r_ℓ`. Jordan–Hölder gives
  `(r̄_λ|_{G_{L'}})^{ss} ≅ W ⊗ k_λ`, which is absolutely irreducible. So `r̄_λ` is an absolutely
  irreducible representation of `G_ℚ`.
- **Conventions.** `h(A)` and `[L':ℚ]` enter only the threshold. Route 1 needs infinitely many `ℓ`,
  not an explicit one, so the threshold never enters a constant.
- **Consumed downstream.** In R5, `r̄_λ : G_ℚ → GL₂(𝔽̄_ℓ)` absolutely irreducible for infinitely many
  `ℓ`. In R7, irreducibility of `r_λ`, which follows.

### R2. Oddness (step 2): CORRECT

- **Source.** Manuscript, lines 742-752 (internal).
- **Statement and check.** `r_ℓ(c)` has eigenvalues `1, -1`. Both lie in `ℤ` and are distinct mod
  `ℓ > 2`, so `r̄_λ(c)` has eigenvalues `1, -1` and `det r̄_λ(c) = -1`.
- **Consumed downstream.** In R5, the hypothesis "odd".

### R3. Weight 2 (step 3): CORRECT after repairs F2-F4

- **Sources.**
  - (a) The `ℓ`-torsion of an abelian scheme is a finite flat group scheme (standard).
  - (b) Raynaud, *Schémas en groupes de type (p, …, p)*, Bull. SMF 102 (1974), §3.4: the tame
    inertia characters of a simple finite flat `𝔽`-vector space scheme over a base with absolute
    ramification `e < ℓ - 1` are products of fundamental characters with exponents in `[0, e]`.
    UNCHECKED (numbering Théorème 3.4.3 recalled, not read). Restated and used in Gee,
    arXiv:1402.7197, §3, and in Buzzard–Diamond–Jarvis (BDJ), arXiv:0810.2106v5, §3.
  - (c) Raynaud 1974, §2: generic fibres of finite flat group schemes are closed under subobjects
    and quotients. UNCHECKED; standard.
  - (d) Serre, Duke Math. J. 54 (1987), §2: the recipe for `k(ρ̄)`, and its value 2 on finite flat
    representations with cyclotomic determinant on inertia. UNCHECKED. Read through BDJ Theorem
    3.17 and its proof (arXiv v5 numbering). That proof lists the Serre weights of every
    `ρ̄|_{G_{ℚ_ℓ}}` and contains the converse statement: "if `ρ` is modular of weight 2 and level
    prime to `ℓ`, then `ρ|_{G_{ℚ_ℓ}}` arises from a finite flat group scheme over `ℤ_ℓ`". BDJ also
    state, just before Conjecture 3.14, that the weight set depends only on the restriction to
    inertia.
- **Hypotheses checked.**
  1. `ℓ ∉ T`, so `L'` is unramified at `ℓ`. `L` is unramified outside `T`, and `β` is unramified
     outside `T` after the final twist at lines 703-708. So for a place `w | ℓ` of `L'`, `I_{L'_w} = I_ℓ`.
  2. On `G_{L'_w}`, `ρ_ℓ` is the Tate action (line 731), and `A` has good reduction at `w`
     (`ℓ ∉ S`). Let `Λ ⊂ r_ℓ` be a `G_ℚ`-stable `O_λ`-lattice. A suitable multiple of `Λ ⊕ Λ` lies
     between `ℓ^n(T_ℓA ⊗ O_λ)` and `T_ℓA ⊗ O_λ`. So `Λ/λΛ` is a subquotient of
     `A[ℓ^{n+1}] ⊗ O_λ`, which is the generic fibre of a finite flat group scheme over `O_{L'_w}`.
     By (c), `r̄_λ|_{G_{L'_w}}` (any lattice) is finite flat over `O_{L'_w}`, which has `e = 1`.
  3. By (b), with `e = 1 < ℓ - 1`, the semisimplification of `r̄_λ|_{I_ℓ}` is either `ψ ⊕ ψ^ℓ`
     (`ψ` a fundamental character of level 2) or `ω^α ⊕ ω^β` with `α, β ∈ {0, 1}`.
  4. Determinant (repair F4). `det V_ℓ(A) = ω_ℓ²` (Weil pairing), and `det(r ⊕ r) = (det r)²`.
     So on `G_{L'}`, `det r_ℓ = χ_ℓ η` with `η` quadratic, and `det r̄_λ|_{I_ℓ} = ω·η|_{I_ℓ}`. By 3,
     the determinant lies in `{1, ω, ω²}` on inertia. `ω^{±1}` is not quadratic for `ℓ > 3`, so
     `η|_{I_ℓ} = 1` and `det r̄_λ|_{I_ℓ} = ω` (computation C).
  5. The cases are therefore: `ψ ⊕ ψ^ℓ`; `ω ⊕ 1`; or a non-split extension. A non-split extension
     must have sub `ω` and quotient `1`, because the connected–étale sequence puts the étale part
     in the quotient. In the opposite orientation the connected part splits off over `ℤ_ℓ^{ur}`.
     That extension is peu ramifiée: its Kummer class comes from `H¹_fppf(O_{L'_w^{ur}}, μ_ℓ)`,
     which is the units modulo `ℓ`-th powers (BDJ Remark 3.11 records this
     identification for `ℓ`-divisible groups; the finite flat case is the same Kummer sequence).
  6. Serre's recipe gives `k = 2` in all three cases (computation B). A très ramifiée extension,
     which is excluded here, would give `ℓ + 1`. Determinant `1` or `ω²` would give `ℓ` or `ℓ + 2`.
- **Conventions.** Serre's `k(ρ̄)` depends only on `ρ̄|_{I_ℓ}`. So no descent of the finite flat
  model from `O_{L'_w}` to `ℤ_ℓ` is needed, contrary to nt-h's appeal to Raynaud §3.3. The descent
  is true (full faithfulness for `e < ℓ - 1` plus étale descent) but unused.
- **Consumed downstream.** In R5 and R6, `k(r̄_λ) = 2` for every `ℓ` as above, independent of `ℓ`.

### R4. Level `N(r̄_λ) ≤ QM²` (step 4): CORRECT, with a simpler justification (F5)

- **Source.** Serre 1987, §1 (definition of `N(ρ̄)`: the prime-to-`ℓ` Artin conductor) is
  UNCHECKED. The same definition is read in Gee, arXiv:1402.7197, §2 (the paragraph defining
  `𝔫(ρ̄)` through the lower ramification filtration, and "`N(ρ̄)` … is just the prime-to-`p` part of
  the Artin conductor"). nt-h also cites "Serre 1987, §1.2" for `a_p(r̄) ≤ a_p(r)`. That attribution
  is UNCHECKED and in doubt: the usual references are Livné (1989) and Carayol (1989). It is not
  needed.
- **Check.** Fix `p ≠ ℓ`. The manuscript's three local arguments (lines 812-857) are statements
  about subgroups of `G_{ℚ_p}` that act trivially through `ρ_ℓ`, and they pass to every reduction.
  - For `p ≤ R`: `G^u_{ℚ_p}` with `u > U_0` acts trivially on `V_ℓ(A)`, hence on `T_ℓ(A)`, hence on
    `A[ℓ]`. `a_σμ_σ = 1` and `β = 1` on these groups. So `r̄_λ` is trivial on them,
    `sw(r̄_λ) = ∫_0^∞ codim (r̄_λ)^{G^u} du ≤ 2U_0`, and `a_p(r̄_λ) ≤ 2 + 2U_0 ≤ E_0`.
  - For `p > R`, `p ∈ T`: `L_v/ℚ_p` is tame, `A` has good reduction (`p ∉ S`), and `β` is tame. So
    wild inertia acts trivially and `a_p(r̄_λ) = codim (r̄_λ)^{I_p} ≤ 2`.
  - For `p ∉ T`: `r̄_λ` is unramified.

  `N(r̄_λ)` is prime to `ℓ` by definition. Hence
  `N(r̄_λ) ≤ ∏_{p≤R} p^{E_0} · ∏_{p∈supp M, p>R} p² ≤ R^{RE_0} M² = QM²`.
- **Conventions.** For `ℓ ≠ p` the residual Swan conductor is computed by the same upper-numbering
  integral, since wild inertia is pro-`p` and acts semisimply in characteristic `ℓ`.
- **Consumed downstream.** In R6, the bound `N(r̄_λ) ≤ QM²`, uniform in `ℓ`.

### R5. Serre's conjecture, strong form (step 5): CORRECT as an application; citation incomplete (F1)

- **Sources.** Khare–Wintenberger, *Serre's modularity conjecture (I), (II)*, Invent. Math. 178
  (2009) 485-504 and 505-586: UNCHECKED (not readable here; not on arXiv; the 2004 preprint
  math/0412076 was read and has neither the theorem nor its numbering). Kisin, *Modularity of
  2-adic Barsotti–Tate representations*, Invent. Math. 178 (2009) 587-634: UNCHECKED, and
  **missing from nt-h**. Restatements read:
  - Gee, arXiv:1402.7197, §3 (opening paragraphs). The weak conjecture "has been proved only in the case `F = ℚ`. This
    was achieved by Khare, Wintenberger, and Kisin" [KW I, KW II, Kisin]. The implication from weak
    to strong "has essentially been known since the late 1970's except for a few cases where
    `p = 2`" (Deligne, Fontaine, Edixhoven).
  - Dieulefait, arXiv:0712.1317, end of §3 ("The level 1 case"). Kisin's characteristic-2 lifting results "allow to
    cover also the remaining cases of Serre's conjecture, i.e., the cases of even level".
  - BDJ, arXiv:0810.2106v5, Theorem 3.17. For a modular `ρ` over `ℚ`, the weights in which `ρ` is
    modular (level prime to `ℓ`) are exactly `W(ρ)`.
- **Statement used.** Let `ρ̄ : G_ℚ → GL₂(𝔽̄_ℓ)` be continuous, odd and absolutely irreducible,
  with `ℓ > 2`. Then there is a newform `g` of weight `k(ρ̄)`, level `N(ρ̄)` and character `ε(ρ̄)`,
  and an embedding of its coefficient field into `ℚ̄_ℓ`, such that `ρ̄_g ≅ ρ̄`.
- **Hypotheses checked.** Continuous: yes. Odd: R2. Absolutely irreducible: R1. `ℓ > 2`: `ℓ > 324`.
  `ℓ ∤ N(ρ̄)`: automatic, since `N(ρ̄)` is prime to `ℓ` by definition. The theorem has **no
  hypothesis on the residual image** (such as irreducibility on `G_{ℚ(ζ_ℓ)}` or non-dihedral image).
  Those hypotheses belong to the modularity lifting theorems inside its proof, not to its
  statement. `k(r̄_λ) = 2` (R3) and `N(r̄_λ) ≤ QM²` (R4).
- **Why Kisin is needed.** `2 ∈ S ⊆ T`. `A` may have bad reduction at 2, and `β` "possibly" ramifies
  at 2 (line 707). So `N(r̄_λ)` may be even. By the two restatements above, the even-level case of
  the weak conjecture rests on Kisin's 2-adic theorem.
- **Strong form.** If the published statement of Khare–Wintenberger is the weak form, the passage
  to level `N(ρ̄)` and weight `k(ρ̄)` for `ℓ > 2` uses classical optimization theorems. These are
  Ribet's level lowering (Invent. Math. 100 (1990)), Carayol (Duke 1989), Diamond's refinement
  (1995), Mazur's principle and Edixhoven (Invent. Math. 109 (1992)). BDJ's proof of Theorem 3.17
  uses Deligne and Fontaine (Edixhoven, Theorems 2.5, 2.6), Mazur's principle (Edixhoven 2.8),
  Edixhoven 4.5 and Gross's companion forms. In the weight-2 finite flat case the companion forms
  are not needed: the split case reaches weight 2 by Mazur's principle. All of these are UNCHECKED
  here and belong inside the citation of the strong form. The audit record should quote whichever
  statement is actually printed.
- **Conventions.** Serre's normalization is `tr ρ_g(Frob_p) = a_p(g)` and `det ρ_g = ε χ_ℓ^{k-1}`,
  with `Frob_p` arithmetic. This matches the Tate-module convention of `r_ℓ` (`det = χ_ℓ ×` finite).
  Any mismatch is absorbed in R6, because the set of newforms is closed under `g ↦ ḡ` (R7).
- **Consumed downstream.** In R6, for each `ℓ` in the infinite set, a newform `g_ℓ` of weight 2,
  level `≤ QM²`, and a prime `λ'` of `ℚ(g_ℓ)` above `ℓ` with `ρ̄_{g_ℓ,λ'} ≅ r̄_λ`.

### R6. Pigeonhole over newforms (step 6): CORRECT after bookkeeping (F6)

- **Source.** Elementary. It uses that `S₂(Γ₁(N))` is finite-dimensional (Shimura, *Introduction to
  the arithmetic theory of automorphic functions*, 1971, Ch. 2; standard), and that a nonzero
  algebraic integer lies in only finitely many prime ideals.
- **Check.** Let `𝓕` be the set of pairs `(g, τ)`, where `g` is a newform of weight 2, level
  `≤ QM²` and any character, and `τ : ℚ(g) → ℚ̄` is an embedding. `𝓕` is finite. For each `ℓ` in
  the infinite set, R5 gives `g_ℓ` and `λ'`. The embeddings `ι_ℓ : C → ℚ̄_ℓ` (fixed) and
  `ℚ(g_ℓ) → ℚ̄_ℓ` (from `λ'`) together define a ring map `C ⊗ ℚ(g_ℓ) → ℚ̄_ℓ`. It factors through
  one compositum, that is, through a pair (the fixed `C ⊂ ℚ̄`, some `τ_ℓ`). Pigeonhole gives one
  `(g, τ) ∈ 𝓕` for an infinite set `Λ` of `ℓ`. For `p ∉ T ∪ supp N_g`, put `δ_p = t_p - τ(a_p(g))`
  in `E = C·τ(ℚ(g))`. For every `ℓ ∈ Λ` with `ℓ ≠ p`, the image of `δ_p` in `𝔽̄_ℓ` is
  `tr r̄_λ(Frob_p) - tr ρ̄_{g,λ'}(Frob_p) = 0`. Both `t_p` and `a_p(g)` are algebraic integers:
  `t_p` is the trace of `r_λ(Frob_p)` for every `λ`, and a continuous representation of a compact
  group has `λ`-integral traces. So `δ_p` lies in primes of `E` of infinitely many residue
  characteristics, and `δ_p = 0`.
- **Conventions.** nt-h's phrase "with all their Galois conjugates … one embedding" expresses this.
  The explicit form above is what an audit record should state.
- **Consumed downstream.** One newform `g' = g^τ` with `N_{g'} ≤ QM²` and `t_p = a_p(g')` for all
  `p ∉ T ∪ supp N_{g'}`.

### R7. Identification and transfer (step 7): CORRECT

- **Sources.**
  - Chebotarev density and Brauer–Nesbitt (standard).
  - The Eichler–Shimura relation and Shimura's construction (A011: Shimura, *On the factors of the
    jacobian variety of a modular function field*, Theorem 1, as audited). They put `ρ_{g',ι}` in
    `V_ℓ(J₁(N_{g'})) ⊗ ℚ̄_ℓ`.
  - The Faltings Hom theorem (A063), unchanged.
- **Check.** By R6, `r_λ` and `ρ_{g',ι}` have equal traces on a density-one set of Frobenius
  elements, so their semisimplifications agree. `r_λ` is irreducible because `r̄_λ` is (R1), and
  for `λ` outside `Λ` one still gets `r_λ^{ss} ≅ ρ_{g',ι}^{ss}`, which is all the transfer needs. On
  Hecke conventions: `V_ℓ(J₁(N))` contains both `ρ_{g'}` and `ρ_{ḡ'}` (`ḡ'` is the newform with
  conjugate coefficients). So whichever of `T_p` or `T_p^*` normalizes Eichler–Shimura, `r_λ|_{G_{L'}}`
  is a constituent of `V_ℓ(J₁(N_{g'})) ⊗ ℚ̄_ℓ`. This is the hypothesis "common constituent of
  `V(A)` and `V(J)`" of line 861, with `N = N_{g'} ≤ QM²`. Lines 860-966 then go through verbatim.
  They use `N` only through `N ≤ QM²` (index bound `N²`, Javanpeykar `h_F(J) ≤ 1.3·10⁷N^{12}`,
  `g ≤ N²`).
- **What is no longer used.** The twist removal (Conrad, A011): KW's `g_ℓ` matches `r̄_λ` itself,
  not a twist, and the pigeonhole compares traces directly. Weight bookkeeping `{0,-1}` against
  `{0,1-k}`: `k = 2` comes from R3. Carayol's bound on the primitive level: the level is `N(r̄_λ)`
  by R5. Li's Fricke stability serves Shimura's quotient `A_f` (A011). The transfer at line 861
  targets `J₁(N)`, so it appears dispensable as well. That is a separate question, not examined
  here; nt-h keeps it.
- **Consumed downstream.** The non-CM part of the height estimate (lines 858-904), unchanged.

## 3. Findings, with severity

| # | Severity | Step | Finding | Repair |
| --- | --- | --- | --- | --- |
| F1 | moderate | 5 | Serre's conjecture is cited to Khare–Wintenberger alone. Its even-level case also rests on Kisin, Invent. Math. 178 (2009) 587-634, and `N(r̄_λ)` may be even (`2 ∈ T`, `β` may ramify at 2). If the printed KW statement is the weak form, the level and weight optimization (Ribet 1990, Carayol 1989, Diamond 1995, Edixhoven 1992 with Mazur's principle) is also part of the citation. | Cite KW I, KW II and Kisin 2009 together as "Serre's conjecture (strong form)". Record the exact printed statement in a new audit record once the papers can be read. |
| F2 | minor | 3 | The argument is written over `O_{L_v}`, but on `G_L` the representation is the Tate action twisted by `β^{-1}`. The parenthetical "the twisting cocycle is unramified at `ℓ`" is not an argument. | Work over `L'`, the kernel field of `β|_{G_L}`. It is unramified at `ℓ ∉ T`, and there `ρ_ℓ` is the Tate action (line 731). Then `I_{L'_w} = I_ℓ` (R3, items 1-2). |
| F3 | minor | 3 | nt-h cites Raynaud's uniqueness (§3.3) to make `r̄_λ` finite flat over `ℤ_ℓ`. That descent is not needed, because `k(ρ̄)` depends only on `ρ̄|_{I_ℓ}`. The inputs actually needed are missing: closure under subquotients (for an arbitrary `G_ℚ`-stable lattice), Raynaud's inertia exponents (§3.4), and "finite flat ⇒ peu ramifiée". | R3, items 2, 3, 5 and 6. |
| F4 | minor | 3 | "Its determinant is the mod-`ℓ` cyclotomic character times a finite character unramified at `ℓ`" is asserted without proof. | R3, item 4 (`ℓ > 3`). Alternatively use the crystalline determinant, but that reintroduces `p`-adic Hodge theory. |
| F5 | minor | 4 | "Reduction does not increase the conductor exponent; Serre 1987, §1.2": attribution unconfirmed. | Not needed: apply lines 812-857 to `r̄_λ` directly (R4). |
| F6 | minor | 6 | The embedding bookkeeping and the integrality of `t_p` are left implicit. | R6. |
| F7 | minor (framing) | §4.3, route 2 | "No `p`-adic Hodge theory left in H" and "one theorem from 2009". KW and Kisin use finite flat and potentially Barsotti–Tate deformation theory (Breuil–Kisin modules) internally, and the citation is three papers. | Say: route 1 removes the *direct* uses of A009, A010 and Conrad. `p`-adic Hodge theory stays inside the citation of Serre's conjecture, as Carayol does. |

No finding affects a constant. No hypothesis of the cited theorems fails. In particular, KW needs
no condition on the residual image, and `ℓ ∤ N(r̄_λ)` holds by definition.

## 4. Repaired text of steps 3-6

**Step 3 (weight).** Let `ℓ ∉ T`, `ℓ > 3`, and let `w | ℓ` be a place of `L'`. `L'` is unramified at
`ℓ`, so `I_{L'_w} = I_ℓ`. On `G_{L'}`, `ρ_ℓ` is the Tate action of `A`, and `A` has good reduction at
`w`. Every `G_ℚ`-stable lattice of `r_ℓ` therefore reduces to a subquotient of some
`A[ℓ^n] ⊗ O_λ`. So `r̄_λ|_{G_{L'_w}}` is the generic fibre of a finite flat group scheme over
`O_{L'_w}`, whose absolute ramification index is `1 < ℓ - 1`. By Raynaud's theorem on vector space
schemes (§3.4), the semisimplification of `r̄_λ|_{I_ℓ}` is `ψ ⊕ ψ^ℓ` or `ω^α ⊕ ω^β` with
`α, β ∈ {0,1}`. Since `det V_ℓ(A) = χ_ℓ²`, the determinant `det r̄_λ|_{I_ℓ}` is `ω` times a
quadratic character, and it lies in `{1, ω, ω²}`. For `ℓ > 3` this forces it to be `ω`. In the
non-semisimple case, the connected–étale sequence and Kummer theory over `O_{L'_w}^{ur}` show that
`r̄_λ|_{I_ℓ}` is a peu ramifiée extension of `1` by `ω`. In every case Serre's recipe gives
`k(r̄_λ) = 2`; it depends only on `r̄_λ|_{I_ℓ}`.

**Step 4 (level).** For `p ≠ ℓ`, the subgroups of `G_{ℚ_p}` shown at lines 812-857 to act trivially
through `ρ_ℓ` act trivially on every reduction. So `a_p(r̄_λ) ≤ E_0` for `p ≤ R`,
`a_p(r̄_λ) ≤ 2` for `p > R` in `T`, and `a_p(r̄_λ) = 0` for `p ∉ T`. Hence `N(r̄_λ) ≤ QM²`.

**Step 5 (Serre's conjecture).** By Khare–Wintenberger (Invent. Math. 178 (2009) 485-504, 505-586)
and Kisin (Invent. Math. 178 (2009) 587-634), together with the classical level and weight
optimization for `ℓ > 2`, the representation `r̄_λ` arises from a newform of weight `k(r̄_λ) = 2`
and level `N(r̄_λ)`.

**Step 6 (pigeonhole).** As in R6, over the finite set of pairs (newform of weight 2 and level
`≤ QM²`, embedding of its coefficient field).

## 5. Corrected trust-base table (replaces the route-1 rows of nt-h §4.3)

| h-leaves §5.1 row | Present use | After route 1 (audited) |
| --- | --- | --- |
| 9 (A008, `ℓ = 3, 5`) | absolute irreducibility of `r_ℓ`; conductor at 5 from `r₃` | replaced by mod-`ℓ` Faltings for large `ℓ`: MW95 §1, Cor. 1, 2 (UNCHECKED), read as Zywina, arXiv:1910.14171, Thm 2.4 (VERIFIED as restated). Faltings–Zarhin (non-effective) also suffices. The conductor at 5 no longer needs `r₃`. |
| 10 (A009) | de Rham, weights `0, -1`, for Pan | removed (direct use) |
| A010 (Berger) | potentially semistable, for Pan | removed |
| 11 (A011): Pan, Thm 1.0.4 | `ℓ`-adic modularity at `ℓ = 5` | replaced by Serre's conjecture, strong form: **KW I, KW II and Kisin 2009** (all UNCHECKED primary; restated in Gee 1402.7197 §3, Dieulefait 0712.1317 §3, BDJ 0810.2106v5 Thm 3.17), plus the pigeonhole R6 |
| 11 (A011): Conrad / Serre 1968 | twist removal, `k = 2` | removed |
| 11 (A011): Li, Shimura | `r ⊂ V(A_f)` | Shimura (Eichler–Shimura) kept; Li kept as in nt-h (possibly dispensable, R7) |
| 17 (I1, Carayol) | `N_f ≤` conductor | no separate leaf; inside the strong-form citation (level optimization) |
| new | | Raynaud 1974, §2 (subquotients) and §3.4 (inertia exponents, `e = 1`): UNCHECKED. Serre 1987, §1 (`N(ρ̄)`) and §2 (`k(ρ̄)`, peu/très ramifiée): UNCHECKED, read through BDJ Thm 3.17 and Gee §2. Chebotarev, Brauer–Nesbitt. |

nt-h's table cites "Raynaud 1974 (finite flat models)" and "Serre 1987 (conductor of a
reduction)". Per F3 and F5, the Raynaud entry should be §2 and §3.4, not the uniqueness of §3.3,
and the Serre entry should be the definitions only.

## 6. Computations

Computation A checks a fact about the order `O` directly. B and C evaluate Serre's recipe and a
small exponent argument as restated here. They confirm the case analysis of R3, but they are not
evidence for the source statements themselves.

`scratch/ser-ell/checks.py` (pure Python, independent of earlier scripts; output in
`checks.output.txt`):

- **A.** `O = ℤ[i,(1+j)/2] ⊂ (2,-3)` is closed under multiplication. The Gram determinant of `Trd`
  on `(1, i, (1+j)/2, (i+ij)/2)` is `-36`, so the reduced discriminant is 6 and `O/ℓ ≅ M₂(𝔽_ℓ)`
  for `ℓ ∤ 6` (R1).
- **B.** Serre's recipe on every inertia type that Raynaud allows for `e = 1`, for all primes
  `5 ≤ ℓ < 120`. With `det = ω` on inertia, finite flat types always give weight 2. The très
  ramifiée type gives `ℓ + 1`, and determinants `1` or `ω²` give `ℓ` or `ℓ + 2` (R3).
- **C.** A quadratic character `η` of `I_ℓ` with `ωη ∈ {1, ω, ω²}` must be trivial for every prime
  `5 ≤ ℓ < 60`. For `ℓ = 3` it need not be (R3, item 4).

## 7. Sources

Read here (arXiv): Zywina 1910.14171; Buzzard–Diamond–Jarvis 0810.2106v5; Gee 1402.7197;
Dieulefait 0712.1317; Khare–Wintenberger math/0412076 (the 2004 preprint, which has no Inventiones
numbering).

Not readable here, hence UNCHECKED: Khare–Wintenberger, Invent. Math. 178 (2009) I and II; Kisin,
Invent. Math. 178 (2009) 587-634; Serre, Duke Math. J. 54 (1987), including §2.8; Raynaud, Bull.
SMF 102 (1974); Masser–Wüstholz 1995; Faltings 1983 (mod-`ℓ` form); Zarhin 1985; Carayol 1989;
Ribet 1990; Diamond 1995; Edixhoven 1992. nt-h's locators "Serre 1987, §2.8", "§1.2" and "Raynaud
§3.3" remain unconfirmed. The last is replaced above by §2 and §3.4, whose numbering is also
unconfirmed.

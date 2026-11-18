# rc-appE-phase: the fields of `Even.EvenPhaseData` for `E_ℓ` (Appendix E, tex 7792–8134)

## Main result

Lane RC11's structure `EvenPhaseData E L σ D₀` (`ZInQKernel/Contrib/OneProof/RC/Even/EvenPhase.lean`,
imported, not restated) is filled for the curve `E_ℓ` of section 7, for every sign `σ` and every
positive squarefree `D₀` prime to `2N` with `L_*(σD₀) ≠ 0`. The retained set is the manuscript's
whole `S₀` filter, `S₀ = primes(2N)`, and the phase is the manuscript's `z_D`:

```lean
theorem evenPhaseData_Ecurve (hWN : WaldspurgerNonvanishingTwoPower) (hW : WaldspurgerCor2)
    (hR : RamseyAlgebraicModel) (hTw : HalfIntegralTwist) (hM : ModularNewform)
    (hH : HasseConvergence) {ℓ : ℕ} (hℓ : 0 < ℓ)
    (L : CentralNormalization (Ecurve ℓ)) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    {N₀ : ℕ} {w₀ : ℤ} (h₀ : RootNumberAt (Ecurve ℓ) N₀ w₀)
    {D₀ : ℕ} (hD₀ : 0 < D₀) (hsq₀ : Squarefree D₀) (hD₀S : ∀ p ∈ (2 * N₀).primeFactors, ¬ p ∣ D₀)
    (hL₀ : L.Lstar (σ * D₀) ≠ 0) :
    ∃ P : EvenPhaseData (Ecurve ℓ) L σ D₀,
      P.retained = {D | S0Filter (2 * N₀).primeFactors D₀ D} ∧ P.z = phase P.N P.η D₀
```

(`ZInQKernel/Contrib/OneProof/RC/AppE/Assembly.lean`; `exists_rootNumberAt_Ecurve` supplies `N₀`.)
It compiles with no `sorry` and no axiom; `#print axioms` gives `[propext, Classical.choice,
Quot.sound]` for all 25 new theorems (`scratch/rc-appE-phase/axioms.txt`).

**Inputs.**
- Prints already in the tree: `WaldspurgerCor2`, `ModularNewform` (lane RC8); the GLUE
  `HasseConvergence` (lane RC8).
- One new print, the one the brief names: `RamseyAlgebraicModel` (Ramsey, Ann. Inst. Fourier 56,
  Def. 3.1, Thm 4.2, Rem. 4.4, in the form Elliot uses it; locators UNVERIFIED).
- `WaldspurgerNonvanishingTwoPower`: lane RC8's print `WaldspurgerNonvanishing` with one more
  conjunct, "ψ has two-power order". The manuscript states this conclusion (tex 7920–7922, 7944)
  and `z_root` needs it (Known issue 1). `waldspurgerNonvanishing_of_twoPower` proves that it is
  the tree's print plus that conjunct.
- **One GLUE hypothesis that is not proved (scoped stop):** `HalfIntegralTwist`. It says that
  twisting a weight-3/2 form by a Dirichlet character modulo its level gives a form of character
  ψν² at a level with the same prime support (tex 8099–8103). See "What is missing".

**Two findings about the tree's statements** (in Known issues, and reported in
`.fleet/rc-appE-phase.md`):
1. The tree's print `WaldspurgerNonvanishing` cannot supply `EvenPhaseData` as the structure is
   written. It omits the two-power order of ψ, and `z_root` together with `z_sq` forces
   ψ(D/D₀) ∈ μ_{2^∞}.
2. `EvenPhaseData` does not constrain `retained` from below. `evenPhaseData_singleton`
   (`AppE/Vacuity.lean`) inhabits it with `retained = {D₀}` and `z = 1`, using the tree's print
   alone. A consumer must ask for `P.retained = {D | S0Filter S₀ D₀ D}`, which this lane's
   theorems record.

No error was found in the manuscript.

## What is missing (scoped stop): `HalfIntegralTwist`

```lean
def HalfIntegralTwist : Prop :=
  ∀ N : ℕ, 0 < N → 4 ∣ N → ∀ ψ ν : DirichletCharacter ℂ N, ∀ f : ℍ → ℂ,
    IsHalfIntegralWeightCuspForm 3 N ψ f →
    ∃ (M : ℕ) (hNM : N ∣ M), 0 < M ∧ (∀ p : ℕ, p.Prime → p ∣ M → p ∣ N) ∧
      ∃ f' : ℍ → ℂ, IsHalfIntegralWeightCuspForm 3 M ((ψ * ν ^ 2).changeLevel hNM) f' ∧
        ∀ n : ℕ, hiwCoeff f' n = ν n * hiwCoeff f n
```

- **What it is.** The standard twisting lemma (Shimura, Ann. of Math. 97 (1973), Lemma 3.6, for
  primitive characters; UNVERIFIED locator). An imprimitive ν adds a sieve to indices prime to
  `N`, which is the twist by the trivial character at each prime of `N`. The manuscript treats it
  as GLUE ("this follows as well by writing it as the finite additive translation sum using the
  Gauss sum", tex 8101–8103).
- **Why it is not proved.** On lane RC8's definition, with j(γ, z) = θ(γz)/θ(z), the
  translation-sum proof needs j(γ', z + u'/m) = j(γ, z) for the conjugate γ' = T^{u/m} γ T^{−u'/m}.
  That is the explicit theta-multiplier formula j(γ, z) = ε_d⁻¹ (c/d) √(cz+d) on Γ₀(4), or
  equivalently the transformation law of the theta series Σ e(n²u/m) q^{n²} on Γ₀(4m²). Neither is
  in Mathlib. Mathlib has θ's S- and T²-transformations, but no Gauss-sum or Poisson-summation
  route to all of Γ₀(4m²).
- **How large it is.** Several thousand lines (the theta transformation formula with quadratic
  reciprocity), the size of a separate project.
- **What follows once it exists.** `evenPhaseData_Ecurve` holds with only prints as hypotheses.
  Nothing else in this lane is open.

## New files and theorems (all under `ZInQKernel/Contrib/OneProof/RC/AppE/`)

Each entry gives the theorem and the field or input of the tree's statements it supplies.

### `Phase.lean`: the fields `retained`, `retained_spec`, `D₀_mem`, `z`, `z_root`, `z_sq`

- `S0Filter S₀ D₀ D` (def). The retained parameters (tex 7812–7817): D > 0 squarefree, prime to
  `S₀`, with DD₀ ≡ 1 (mod 8) and DD₀ a nonzero square modulo every odd p ∈ S₀. Supplies the field
  `retained`.
- `S0Filter.spec`. At a level with prime support in `S₀`, a retained D is prime to the level and in
  the unit classes of D₀ at its primes. Supplies the field `retained_spec`.
- `S0Filter.self`. D₀ is retained. Supplies the field `D₀_mem`.
- `isSquare_zmod_of_local`. A unit that is ≡ 1 (mod 8) and a square modulo each odd prime of N is a
  square in `ZMod N`. Proved with Mathlib's `hensels_lemma` in ℤ_p and the Chinese remainder
  theorem.
- `sqrtRatio`, `phase` (defs). z_D = η(w) with w² D₀ = D in `ZMod N`. By the Chinese remainder
  theorem this is ∏_{p | cond η} η_p(u_p) with u_p² = D/D₀ (tex 8116–8121). Another choice of
  roots changes z_D by a sign, as the manuscript says. Supplies the field `z`.
- `phase_sq_eta`. z_D² = η(D)η(D₀)⁻¹ (tex 8124).
- `phase_sq`. z_D² = ψ(D)ψ(D₀)⁻¹, because χ_{−σ} is trivial on D/D₀ (tex 8136–8138). Supplies the
  field `z_sq`.
- `phase_root`. z_D is a two-power root of unity when ψ^{2^k} = 1. Supplies the field `z_root`.

### `Linear.lean`: the weight-3/2 spaces are vector spaces, and the full-space comparison

- `hiwForm_periodic` / `hiwForm_periodic_comp`. Shimura forms have period 1. The proof needs no
  nonvanishing of θ.
- `hiwForm_analyticAt`, `hiwCoeff_add`, `hiwCoeff_smul`, `hiwCoeff_sum`. The Fourier coefficients
  are linear.
- `hiwForm_add`, `hiwForm_smul`, `hiwForm_sum`, `eigen_add`, `eigen_smul`, `eigen_sum`. The cusp
  spaces and the eigenspaces are closed under linear combinations.
- `proportional_of_waldspurgerCor2` (tex 8029–8039, 8104–8110). For f₁, f₂ in one eigenspace,
  a_{f₁}(D) a_{f₂}(D₀) = a_{f₂}(D) a_{f₁}(D₀), from `WaldspurgerCor2` at f₁, f₂ and f₁ + f₂ and
  F₀(1) ≠ 0.

### `Ramsey.lean`: the new print and the algebraic vector

- `RamseyAlgebraicModel` (PRINT). It has two clauses:
  - (R-span): every complex form in S_{3/2}(N, ψ) is a finite complex combination of such forms
    with algebraic coefficients.
  - (R-conj): for τ ∈ Aut(ℚ̄/ℚ), conjugating the coefficients of an algebraic form of character ψ
    gives a form of character ψ^τ.
- `exists_algebraic_normalized` (tex 8053–8083). The eigenspace contains an algebraic g′ with
  a_{g′}(D₀) = 1.
- `dirichlet_mem_Qbar`, `heckeT3_sum`. Supporting lemmas.
- `unary_eigenvalue_ne`. Proves 2√p < p + 1, the inequality in tex 8053–8059.

### `Galois.lean`: the conjugate and the twist

- `HalfIntegralTwist` (GLUE, open; above).
- `hiwForm_changeLevel`, `eigen_changeLevel`. Level raising.
- `eta_sq_eq`, `twist_chars`. η² = ψ², and ψν² = ψ^e, ην² = η^e for ν = η^{(e−1)/2} (tex 8099–8100).
- `exists_odd_exponent`, `tau_dirichlet` (tex 8086–8088). An odd e with τ(ζ) = ζ^e on the values of
  ψ and η.
- `conj_mem_eigenspace` (tex 8090–8093). g′^τ lies in the eigenspace of ψ^e, η^e. It follows from
  (R-conj); the eigenvalues are proved.
- `twist_mem_eigenspace` (tex 8099–8103). g′ ⊗ ν lies in the eigenspace of ψν², ην². It follows
  from `HalfIntegralTwist`; the eigenvalues are proved.

### `Rational.lean`: the field `rational`

- `rational_of_ramsey` (tex 8086–8134). For g in the eigenspace with a_g(D₀) ≠ 0 and D in the
  level filter, a_g(D)/a_g(D₀) = z_D r with r ∈ ℚ. The steps: the algebraic g′; the conjugate and
  the twist at a common level; τ(a(D)) = ν(D/D₀)a(D) = z_D^{e−1} a(D); τ(z_D) = z_D^e; then
  `galois_fixed_div` (tree) and `InfiniteGalois.mem_range_algebraMap_iff_fixed` (Mathlib).
  Supplies the field `rational`.

### `Assembly.lean`: the structure

- `WaldspurgerNonvanishingTwoPower` and `waldspurgerNonvanishing_of_twoPower` (above).
- `F_one_ne_zero_of_lstar`. L_*(σD₀) ≠ 0 gives F₀(1) ≠ 0.
- `evenPhaseData_of_prints`. Any elliptic `E`, with retained = the `S₀` filter. Supplies the fields
  `N, hN, ψ, η, hψη, g, hg, ha₀` from the print and the rest from the files above.
- `evenPhaseData_of_prints_levelFilter`. The same with retained = the whole filter at the level
  (a superset of the `S₀` filter).
- `hcond_primeFactors`. The print's hypothesis "every prime of the level of every functional
  equation lies in `S₀`" holds for S₀ = primes(2N₀), by `rootNumberAt_unique` (from
  `ModularNewform`).
- `evenPhaseData_Ecurve`, `exists_rootNumberAt_Ecurve`. For E = E_ℓ.

### `Vacuity.lean`

- `evenPhaseData_singleton`. Inhabits `EvenPhaseData` with `retained = {D₀}` (Known issue 2).

**Brief item 1, the print's hypotheses for E_ℓ.**
- `RootNumberAt`: holds by `hcond_primeFactors`, from `ModularNewform`.
- `AnalyticRank (qtwist E (σD₀)) 0`: follows from L_*(σD₀) ≠ 0 by `lstar_ne_zero_iff_of_bcdt`
  (BCDT from `ModularNewform`, plus `HasseConvergence`).
- Ellipticity of E_ℓ: `PoleRC.curve_isElliptic`.
- Nothing else is missing except the two-power conjunct (Known issue 1).

## Known issues

1. **The tree's print omits the two-power order.** `WaldspurgerNonvanishing`
   (`RC/PrintsAnalytic/Waldspurger.lean`) does not state that ψ (hence η) has two-power order.
   - The manuscript asserts it for Elliot's construction (tex 7920–7922, 7944).
   - `EvenPhaseData` needs it: `z_root` and `z_sq` force ψ(D)ψ(D₀)⁻¹ ∈ μ_{2^∞}.
   - Without it the structure cannot be filled on the whole filter. Twisting an eigenform by a
     cubic character stays inside a good-Hecke eigenspace (characters ψν², ην²) and multiplies
     a(D)/a(D₀) by ν(D/D₀) ∈ μ₃.
   - Proposed fix: add the conjunct `∃ k, ψ ^ (2 ^ k) = 1` to the print, as
     `WaldspurgerNonvanishingTwoPower` does.
2. **`EvenPhaseData` does not pin down its retained set.** The structure is satisfiable with
   `retained = {D₀}` (`evenPhaseData_singleton`).
   - `EvenPhaseData.minimum` is a minimum over `P.retained` and is meaningful only when
     `P.retained` is the manuscript's filter.
   - Proposed fix: consumers should use `evenPhaseData_of_prints` / `evenPhaseData_Ecurve`, which
     record `P.retained = {D | S0Filter S₀ D₀ D}`; or the structure should get a field
     `∀ D, S0Filter S₀ D₀ D → D ∈ retained`.
3. **`HalfIntegralTwist` is an open GLUE hypothesis** (above). It is a standard, true statement,
   and its proof on the tree's definitions needs the theta-multiplier formula.
4. **`RamseyAlgebraicModel` is not read in the print** (no copy, no network). Its clauses are what
   Elliot uses. (R-conj) includes the integral-weight Galois action that Elliot's θ-reduction
   invokes (tex 8093–8098), which the manuscript does not cite separately; it is a consequence of
   the ℚ-rationality of Ramsey's model, its q-expansion and its diamond operators.
5. **Route differences (provenance (c)).** These have the same conclusions as the manuscript by
   shorter routes:
   - `proportional_of_waldspurgerCor2` replaces the polynomial-ring domain argument (tex 8033–8037)
     by an explicit linear combination of the three Corollaire 2 identities.
   - `exists_algebraic_normalized` replaces "a finite basis of the defining equations" by linear
     independence over ℚ̄.
   - `phase` is the manuscript's product of local factors, written through the Chinese remainder
     theorem.
6. **Convention for η_p.** The identity z_D² = η(D/D₀) (tex 8124) forces η_p to be the
   prime-power factor of the Dirichlet character. The local component of the idelic character is
   its inverse on units, which would give z_D² = η(D/D₀)⁻¹. `phase` uses the forced convention.
7. **No consumer imports these files yet.** The orthogonality to unary theta series
   (tex 8053–8059) is not needed by the tree's eigenspace, which lies in the full cusp space;
   only Elliot's inequality is proved.

## Manuscript check

| tex | step | verdict |
|---|---|---|
| 7792–7811 | statement of `ex:app-even-phase` (retained filter, z_D ∈ μ_{2^∞}, r_D ∈ ℚ) | OK (filled, with the filter recorded) |
| 7812–7820 | the `S₀` filter of D₀; retained D | OK |
| 7821–7835 | nonzero D₀-functional from Waldspurger's theta theorem | unverified (print `WaldspurgerNonvanishing`, not read) |
| 7837–7925 | local scalar K₀-type; ψ of two-power order | unverified (Elliot's local construction, not formalized; enters as the conjunct of `WaldspurgerNonvanishingTwoPower`) |
| 7942–7955 | ψ, η = ψχ_{−σ}, both of two-power order; full eigenspace V | OK (η two-power from ψ two-power and χ_{−σ}² = 1; used in `phase_root`) |
| 7968–8028 | Corollaire 2, (E.10) | unverified (lane RC8's print, used as stated) |
| 8029–8039 | proportional functionals on all of V | OK (proved, `proportional_of_waldspurgerCor2`, different route) |
| 8041–8052 | Ramsey's section model; algebraic linear conditions | unverified (Ramsey not read; leaf `RamseyAlgebraicModel`) |
| 8053–8059 | V orthogonal to unary theta series by the eigenvalue bound | OK (2√p < p+1 proved; unary eigenvalue p+1 STANDARD, not formalized) |
| 8060–8063 | an algebraic g with a(D₀) = 1 | OK (proved from (R-span), `exists_algebraic_normalized`) |
| 8064–8076 | flat field extension of Ramsey's sections via an affine cover | unverified (about Ramsey's sheaves; inside the leaf; the Čech argument is standard) |
| 8076–8083 | a basis vector with nonzero reference value | OK (proved) |
| 8086–8088 | an odd e describing τ on the values of ψ, η | OK (proved, `exists_odd_exponent`) |
| 8090–8093 | g^τ has character ψ^e and eigenvalues η(p)^e a_p(E) | OK (eigenvalues proved; modularity from (R-conj)) |
| 8093–8098 | reduction of conjugation to integral weight via θ (θ⁴ trivial character) | unverified (in the leaf; θ⁴ ∈ M₂(Γ₀(4)) with trivial character checked by hand) |
| 8099–8100 | g ⊗ ν has character ψν² = ψ^e and the same eigenvalues | OK (proved, `twist_chars`, `twist_mem_eigenspace`) |
| 8101–8103 | the twist is modular at a level supported on `S₀` | unverified (GLUE `HalfIntegralTwist`, not proved: needs the θ-multiplier formula) |
| 8104–8113 | τ(a(D)) = ν(D/D₀) a(D); no vanishing denominator | OK (proved in `rational_of_ramsey`) |
| 8114–8121 | definition of z_D | OK (formalized as η(w), w² = D/D₀ mod N; equal by the Chinese remainder theorem up to the sign the manuscript allows) |
| 8122–8127 | z_D ∈ μ_{2^∞}, z_D² = η(D/D₀), τ(z_D) = z_D^e, ν(D/D₀) = z_D^{e−1} | OK (proved; the first needs ψ two-power) |
| 8128–8130 | independence of the representative e | OK (not needed: e is fixed for each τ) |
| 8131–8134 | a(D)/z_D fixed by every τ, hence rational; sign of the choice | OK (proved, infinite Galois theory) |
| 8136–8138 | ψ/η = χ_{−σ} trivial on D/D₀, so ψ(D/D₀) = z_D² | OK (proved, `phase_sq`; D ≡ D₀ mod 8) |
| 8139–8142 | (E.11) | OK (tree's `EvenPhaseData.E11`, unchanged) |

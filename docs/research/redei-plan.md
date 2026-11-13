# Rédei's formula in Lean: target, Mathlib inventory, routes, plan

This note decides whether and how Rédei's formula (tyz-5b Proposition 2.3) can be proved in Lean on top
of Mathlib v4.35.0, so that the hypothesis `CertifiedRankTYZ` (task cr5b-sec3,
`ZInQKernel/RouteK/Rank5b/Sec3/TYZ.lean`) can be stated with class numbers of imaginary quadratic
fields, as Tian–Yuan–Zhang state it, and Rédei's formula leaves its trust statement.

The probe `scratch/redei-plan/Probe.lean` holds every statement named below. It compiles with
`lake env lean` against Mathlib and `ZInQKernel.RouteK.Rank5b.Sec3.TYZ`. The plumbing (§1.3) and a few
API checks (§2.1) are proved there; the rest is `sorry`.

## Verdict

- **It can be done on top of Mathlib v4.35.0, with no new deep input.** The chosen route (§3, route (c))
  is genus theory in the ring of integers. It uses Dirichlet's theorem on primes in progressions, which
  is in Mathlib, in place of Hasse–Minkowski or Legendre's theorem, which are not. It needs no Hilbert
  symbol, no binary quadratic forms and no explicit integral basis.
- **Estimated size: about 2,700 lines; budget 3,500.** That is 8 modules, about as large as cr5b-sec3
  (4,150 lines). The mathematical risk is low and the engineering risk moderate (§3.4).
- **Recommendation (§5): do not start the full formalization now.** The payoff is modest: one classical,
  numerically cross-checked input leaves the trust statement, while TYZ and Gross–Zagier–Kolyvagin
  stay. A cheap step is worth taking now: state `CertifiedRankTYZCl` (class numbers) and the Prop
  `RedeiFormula` (= the statement of `gCl_eq_gBit`) in Lean. That makes the citation exact for about
  100 lines, and the probe already contains it.

## 1. The target

### 1.1 What TYZ use (VERIFIED against the arXiv source)

I read the LaTeX source of arXiv:1411.4728v1 (`Period7.tex`, downloaded to a temporary directory
outside the repo), lines 361–366:

> we show that `𝓛(n)` is an integer, and give a criterion for when it is odd in terms of the parities of
> the genus class numbers `g(d) := #(2Cl(ℚ(√−d)))` of positive divisors `d` of `n`. It is clear that
> `g(d)` is odd if and only if `Cl(ℚ(√−d))` has no element of exact order 4. Thus by Rédei [Re], the
> parity of `g(d)` can be computed in terms of the Rédei matrix …

`2Cl` is the subgroup of squares, not the 2-torsion. Line 998 sums the characters of `Cl_n/2Cl_n` to
`2^{h₂(n)}δ_{2Cl(K_n)}`, the indicator of the squares. With the 2-torsion, "odd iff no element of
order 4" would be false. `Cl(ℚ(√−d))` is the ideal class group of the field, that is, of its ring of
integers. So TYZ's `g(d)` is `Nat.card` of the range of `x ↦ x²` on `ClassGroup (𝓞 ℚ(√−d))`. The
theorem used (tyz-5b §1.2, Proposition 1.1) uses `g` only through this definition. tyz-5b's "`g(d) =
#2Cl mod 2`" is the same quantity.

By genus theory `#Cl[2] = 2^{t−1}` (`t` = number of primes dividing the discriminant), so `#2Cl =
h/#Cl[2] = h(−d)/2^{t−1}`. The plan proves `#Cl[2] = 2^{t−1}` along the way (§3.2, step 8), so the form
`h(−d)/2^{t−1}` is a corollary. The target uses `#2Cl`, as TYZ do.

### 1.2 Lean statements (probe §§1–2)

```lean
abbrev QNeg (n : ℕ) : Type := QuadraticAlgebra ℚ (-(n : ℚ)) 0          -- ℚ(√−n)
instance factNeg (n : ℕ) [NeZero n] : Fact (¬ IsSquare (-(n : ℚ)))      -- proved; gives `Field`
instance (n : ℕ) [NeZero n] : NumberField (QNeg n) where                 -- proved (fields inferred)

/-- TYZ's genus class number `g(n) = #(2 Cl(ℚ(√−n)))`. -/
def gCl (n : ℕ) [NeZero n] : ℕ :=
  Nat.card (powMonoidHom 2 : ClassGroup (𝓞 (QNeg n)) →* ClassGroup (𝓞 (QNeg n))).range

instance neZero_dProd {d : ℕ} (B : Finset d.primeFactors) : NeZero (dProd B)   -- proved

/-- Target: Rédei's formula, tyz-5b Proposition 2.3. -/
theorem gCl_eq_gBit {d : ℕ} (hd : Odd d) (hsq : Squarefree d) {B : Finset d.primeFactors}
    (hB : B.Nonempty) : ((gCl (dProd B) : ℕ) : ZMod 2) = gBit d B
```

Notes on the choices:

- **The field.** Mathlib's `QuadraticAlgebra ℚ a b` (`ω² = a + bω`) is a `Field` once
  `Fact (¬ IsSquare a)` holds (`Mathlib/Algebra/QuadraticAlgebra/Basic.lean`, instances at lines 607
  and 623). The probe proves the `Fact` for `a = −n`, `n ≠ 0`. `CharZero`, `FiniteDimensional ℚ`,
  `IsGalois ℚ` and `Fintype (ClassGroup (𝓞 _))` are all inferred, and `NumberField` needs only an
  empty `where`. `Zsqrtd` is a ring, not a field, and `AdjoinRoot` would need irreducibility; neither is
  better. The statement is invariant under isomorphism of fields, so the concrete model does not matter
  for faithfulness to TYZ.
- **`B = ∅` is excluded.** There `d_B = 1`, `gCl 1 = 1` but `redeiG _ _ _ ∅ = 0`. Blocks of a
  `Finpartition` are nonempty, so `T5b` never meets `B = ∅`.
- **A binary-form class group is not easier.** Defining Gauss composition and proving the group laws is
  itself a project of more than 2,000 lines, and the identification with `ClassGroup` would come on top
  (§3, route (b)).

### 1.3 The hypothesis in class-number form (probe §2, proved modulo `gCl_eq_gBit`)

```lean
def T5bCl (d : ℕ) : ZMod 2 :=
  ∑ P : Finpartition (Finset.univ : Finset d.primeFactors),
    if Admissible5bNat d P then ∏ B ∈ P.parts, ((gCl (dProd B) : ℕ) : ZMod 2) else 0

def CertifiedRankTYZCl : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → (Sel2 d).ncard = 8 → T5bCl d = 1 →
    ∀ ab ∈ Sel2 d, Loc ℚ d ab.1 ab.2

theorem T5bCl_eq_T5b {d : ℕ} (hd : Odd d) (hsq : Squarefree d) : T5bCl d = T5b d
theorem certifiedRankTYZ_iff : CertifiedRankTYZCl ↔ CertifiedRankTYZ
```

`T5bCl d` is TYZ's coefficient of `τ(1/2)` with their own `g`: the sum of `g(d₀)g(d₁)Π g(d_i)` over
unordered factorizations `d = d₀d₁⋯d_ℓ` with `d₀ ≡ 7`, `d₁ ≡ 3` and `d_i ≡ 1 (mod 8)`. For squarefree
`d`, factorizations are set partitions of the primes (tyz-5b Notation). Once `gCl_eq_gBit` is proved,
the trust statement of `CertifiedRankTYZCl` cites only Tian–Yuan–Zhang (the form proved in their
Theorem 3.5(2)) and Gross–Zagier–Kolyvagin. `certifiedRankTYZ_iff` and Theorem 3.6 then feed the
existing chain to the main theorem.

The probe proves `T5bCl_eq_T5b` and `certifiedRankTYZ_iff` from `gCl_eq_gBit`, using only
`Finpartition.ne_bot`. So the plumbing from the target to the hypothesis is settled.

## 2. Mathlib v4.35.0 inventory

Paths are relative to `.lake/packages/mathlib/Mathlib/`. "Probe" means that the declaration was used
in a compiled proof in `Probe.lean`.

### 2.1 Present

| Ingredient | Declarations | Notes |
| --- | --- | --- |
| Quadratic field for variable `d` | `QuadraticAlgebra` (`Algebra/QuadraticAlgebra/Defs.lean`), `QuadraticAlgebra.omega`, `omega_mul_omega_eq_algebraMap`, `finrank_eq_two`, `QuadraticAlgebra.norm`, `norm_def`, `star`, `det_toLinearMap_eq_norm` (`NormDeterminant.lean`), `isField_iff_not_isSquare_discr` (`Discriminant.lean`), `Algebra.IsQuadraticExtension` | probe: `card_gal`, `isIntegral_omega`, `algNorm_eq`, `norm_nonneg` |
| Number field instances | `NumberField` (fields inferred), `IsQuadraticExtension.isGalois` (`FieldTheory/Galois/Basic.lean:793`), `IsGalois.card_aut_eq_finrank` | probe |
| Ring of integers | `NumberField.RingOfIntegers` (`𝓞 K`); `MulSemiringAction G (𝓞 K)` from one on `K` (`NumberField/Basic.lean:125`); `IsIntegral.of_pow`, `isIntegral_algebraMap`, `Algebra.isIntegral_norm` | no description of `𝓞 ℚ(√D)` (none is needed, §3.2) |
| Class group, finiteness | `ClassGroup`, `ClassGroup.mk0`, `mk0_surjective`, `mk0_eq_mk0_iff`, `mk0_eq_one_iff` (`RingTheory/ClassGroup/Basic.lean`); `NumberField.RingOfIntegers.instFintypeClassGroup`, `NumberField.classNumber` (`NumberField/ClassNumber.lean`) | probe |
| Galois action on primes | `Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`, `Ideal.exists_smul_eq_of_isGaloisGroup`, `ramificationIdx_eq_of_isGaloisGroup`, `inertiaDeg_eq_of_isGaloisGroup` (`NumberTheory/RamificationInertia/Galois.lean`); `IsGaloisGroup (K ≃ₐ[ℚ] K) ℤ (𝓞 K)` is inferred | probe: `fundamental_identity` (`#primesOver · e · f = 2`), `exists_conj_eq` |
| Factorization of `p𝓞` | `Ideal.map_algebraMap_eq_finsetProd_pow` (`RingTheory/DedekindDomain/Factorization.lean:804`), `UniqueFactorizationMonoid.induction_on_prime`, `Ideal.IsPrime.mul_le`, `Finset.prod_dvd_of_coprime` | |
| Norms of ideals | `Ideal.absNorm` (multiplicative), `Ideal.absNorm_span_singleton`, `Ideal.absNorm_eq_one_iff`, `Ideal.absNorm_eq_pow_inertiaDeg` (`RamificationInertia/Inertia.lean:199`); `Ideal.relNorm`, `relNorm_smul`, `relNorm_eq_pow_of_isPrime_isGalois`, `relNorm_int` (`RingTheory/Ideal/Norm/RelNorm.lean`); `FractionalIdeal.absNorm` | |
| Element norm via Galois | `Algebra.norm_eq_prod_automorphisms` (`RingTheory/Norm/Transitivity.lean:270`) | |
| Ramification and discriminant | `NumberField.discr`, `NumberField.not_dvd_discr_iff_isUnramifiedIn` (`Discriminant/Different.lean:191`) | not needed: §3.2 decides ramification by hand |
| Kummer–Dedekind | `NumberField.Ideal.primesOverSpanEquivMonicFactorsMod` (`NumberField/Ideal/KummerDedekind.lean`) | not needed |
| Fundamental discriminants | `Int.IsFundamentalDiscr`, `isFundamentalDiscr_iff_squarefree` (`NumberTheory/FundamentalDiscriminant.lean`) | elementary arithmetic only, not linked to fields |
| Quadratic reciprocity, Jacobi | `legendreSym.quadratic_reciprocity`, `legendreSym.at_two`, `legendreSym.eq_one_iff`, `jacobiSym.quadratic_reciprocity`, `jacobiSym.at_neg_one`, `jacobiSym.mul_left/right` (`NumberTheory/LegendreSymbol/`); `FiniteField.exists_nonsquare` | the project has `legBit`, `legBit_mul`, `legBit_prod`, `legBit_reciprocity` (`ZInQKernel/RouteK/Slots/Symbols.lean`) |
| **Dirichlet's theorem** | `Nat.forall_exists_prime_gt_and_eq_mod`, `Nat.forall_exists_prime_gt_and_zmodEq`, `Nat.infinite_setOfPred_prime_and_eq_mod` (`NumberTheory/LSeries/PrimesInAP.lean`) | the deep input of route (c), already in Mathlib |
| Group theory | `powMonoidHom`, `exists_prime_orderOf_dvd_card'`, `orderOf_dvd_natCard`, `Subgroup.orderOf_coe` | probe: `odd_card_range_sq_iff` proved |
| Hilbert 90 | `groupCohomology` Hilbert 90 (`RepresentationTheory/Homological/GroupCohomology/Hilbert90.lean`) | not needed; the quadratic case is two lines by hand |

### 2.2 Missing

Size estimates are for this project's use (`ℚ(√−n)`, `n` odd squarefree), not for Mathlib-general
versions.

| Ingredient | Status | Nearest Mathlib material | Size if built |
| --- | --- | --- | --- |
| `𝓞 ℚ(√D) = ℤ[(D+√D)/2]`, `discr = D` | absent (no `IsIntegralClosure` for any quadratic order) | `QuadraticAlgebra.Int` (`ℤ`-order, `IsFractionRing`), `Algebra.discr`, the Eisenstein criterion used for cyclotomic integers (`NumberField/Cyclotomic/`) | 300–400; **avoided** by route (c) |
| Splitting law of primes in quadratic fields | absent | Galois fundamental identity (above), Kummer–Dedekind | 250 for the trichotomy plus ramified-iff-divides-`D` (needed, §3.2 Primes) |
| `𝔞 σ(𝔞) = (N𝔞)` | absent (no "`map relNorm = Π σ•I`") | `relNorm_eq_pow_of_isPrime_isGalois`, `map_algebraMap_eq_finsetProd_pow` | 150 (needed) |
| Genus theory (ambiguous classes, genus characters, principal genus theorem) | absent | — | 1,400 (needed; the bulk of the plan) |
| Hilbert symbol `(a, b)_v` | absent | `padicValRat`, `legendreSym`, `Padic` | 300 (definition, bilinearity at odd `p`, `p = 2` by tables); **avoided** |
| Hasse–Minkowski | absent | — | many thousands; **avoided** |
| Legendre's theorem `ax² + by² + cz² = 0` | absent | `Nat.Prime.sq_add_sq` (Gaussian integers), Minkowski's convex body theorem `MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure` | 700–1,000 (pigeonhole proof); **avoided** |
| Binary quadratic forms, composition | absent | `Matrix.SpecialLinearGroup` action, `ModularGroup` | 2,000+ for composition and group laws; **avoided** |
| "every class has an integral ideal prime to `𝔪`" | absent | `ClassGroup.mk0_surjective`, Dedekind ideal arithmetic | 60 (needed, only for `𝔪 = 𝔭_q`) |

## 3. Routes

### 3.1 Comparison

The three routes share the core: the field, the prime trichotomy, the ramified primes and `(√−n) =
Π 𝔭_p`, `𝔞σ𝔞 = (N𝔞)`, the bridge to the bits, and the 𝔽₂ linear algebra. They differ in how they get the
**principal genus theorem** (`2Cl` = the classes whose norm is a local norm everywhere), which is the
only deep step.

- **(a) Genus theory as in tyz-5b §2.2.** Uses (G1) ambiguous classes, (G2) "`[𝔞]` is a square iff
  `N𝔞` is a global norm", and (G3) Hasse–Minkowski for `x² + ny² = n'z²`. In Lean, (G3) would be
  Legendre's theorem for diagonal ternary forms (700–1,000 lines, the riskiest piece: pigeonhole and
  case analysis with irrational bounds). The `(n, n') → (g, n₁, n₁')` reduction to the coprime form, and the
  translation of Legendre's conditions into bits, add 250. (G2) needs coprime-quotient arguments with
  fractional ideals (200), and the kernel of `ψ` needs the explicit integral basis (250 + 300).
  **About 3,600 lines.**
- **(b) Gauss's genus theory of binary quadratic forms.** Composition of forms, the group law, reduction
  theory, then genus theory over forms, and finally an isomorphism with `ClassGroup (𝓞 K)` to match TYZ.
  **Over 5,000 lines.** Rejected.
- **(c) Genus characters plus Dirichlet's theorem (chosen).** Replaces (G2) and (G3) by:
  - genus characters `χ_q([𝔞]) = (N𝔞/q)` for the primes `q ∣ n`. They are homomorphisms, so they kill `2Cl`;
  - Dirichlet's theorem: `χ` takes `2^{t−1}` values. Pick a prime `p` with prescribed residues; it
    splits, and a prime above it has the prescribed characters;
  - counting: `[Cl : 2Cl] = #Cl[2] ≤ 2^{t−1} ≤ #im χ = [Cl : ker χ] ≤ [Cl : 2Cl]`, so `2Cl = ker χ`
    and `ker ψ = {0, e_n}`.

  This is the classical proof of "number of genera = `2^{t−1}`" (as in Cox, *Primes of the form
  `x² + ny²`*, §6), with the principal genus theorem obtained by counting. **About 2,700 lines.** The
  deep input, Dirichlet's theorem, is already in Mathlib. The kernel of `ψ` comes out of the count, and
  the residue-field arguments of §3.2 replace the explicit ring of integers.

Two further simplifications, both checked on paper:

- Only the odd characters `χ_q`, `q ∣ n`, are needed, even when `n ≡ 1 (mod 4)` and 2 ramifies. Their
  image is all of `𝔽₂^r` (size `2^r = 2^{t−1}`) when `n ≡ 1 (mod 4)`, and the hyperplane `Σε = 0` when
  `n ≡ 3 (mod 4)` (size `2^{r−1} = 2^{t−1}`). Choose `p ≡ 1` or `3 (mod 4)` to make `(−n/p) = 1`; this
  uses Jacobi reciprocity.
- `χ_q` is well defined using integral ideals only. If `span{β}J = span{α}I` with `I, J, β ∉ 𝔭_q`, then
  `α ∉ 𝔭_q`. For `α ∉ 𝔭_q`, `N(α) = ασ(α) ≡ m² (mod 𝔭_q)` because `σ` acts trivially on
  `𝓞/𝔭_q = 𝔽_q`. So `N(α)` is a nonzero square mod `q`. No coordinates are needed.

### 3.2 The chosen route: steps and modules

Write `K = QNeg n`, `O = 𝓞 K`, `σ` the nontrivial automorphism, `ω = √−n`, `θ = (1+ω)/2`. Here `n` is
odd squarefree (in the application `n = d_B ≥ 3`), `r = #primes of n`, `ramSet n` = primes of `n`
plus `2` if `n ≡ 1 (mod 4)`, and `t = #ramSet n`. Statement names are those of `Probe.lean` §3.

1. **`Redei/Field.lean`** (250). The instances (done in the probe); `card_gal` (done);
   `isIntegral_omega` (done); `isIntegral_theta` for `n ≡ 3 (4)`; `algNorm_eq` (done);
   `norm_eq_mul_conj` (`Algebra.norm_eq_prod_automorphisms`); `norm_nonneg` (done); norms of integral
   elements are integers; `O ∩ ℚ = ℤ`, so the rational units of `O` are `±1`; `σ ω = −ω`.
2. **`Redei/Primes.lean`** (500).
   - `prime_trichotomy`: split (`σP ≠ P`, `P·σP = pO`, `N P = p`), inert (`P = pO`, `N P = p²`) or ramified
     (`P² = pO`, `N P = p`). From `fundamental_identity` (done) and `map_algebraMap_eq_finsetProd_pow`.
   - `dvd_of_ramified`: if `f = 1` then `ℤ → O/P` is onto, so `x − σx ∈ P` for all `x`. Take `x = ω`
     (`p ∣ 4n`) and, for `p = 2`, `x = θ` (forces `n ≡ 1 (mod 4)`).
   - For `p ∣ n`: `ω ∈ P` for every `P` over `p`. The split and inert cases give `p ∣ ω`, hence `p² ∣ n`; so
     `p` ramifies. For `n ≡ 1 (mod 4)`: `α = 1 + ω` has `N(α/2) = (1+n)/4 ∉ ℤ`, so `2` ramifies.
   - `ramIdeal`, `ramIdeal_spec`, `span_omega : (ω) = Π_{p∣n} 𝔭_p` (divisibility plus equal norms).
   - `mul_conj_ideal : I·σI = (N I)`, by induction on primes and the trichotomy.
3. **`Redei/Ambiguous.lean`** (400), the step (G1).
   - Hilbert 90 at the integral level: `x σI = y I` gives `N x = N y` (cancel `I·σI`; rational units are
     `±1`; norms are `≥ 0`); then `ν = σx (x + y)` has `y σν = x ν`, so `νI` is σ-invariant.
   - `mem_range_psi_of_conj_eq`, by strong induction on `N I`: peel off `pO` for split and inert primes,
     and `𝔭_p` for ramified ones.
   - `psi`, `psi_single`, `psi_ones`, `range_psi : im ψ = Cl[2]`; hence `#Cl[2] ≤ 2^{t−1}`.
4. **`Redei/Genus.lean`** (400).
   - `exists_mk0_coprime` (take `β ∈ J ∖ J𝔭_q` for `J` in the inverse class).
   - `chi`, `chi_mk0`, the homomorphism property.
   - `chi_psi`: `χ_q(ψ e) = Σ_p R_{qp} e_p` with `R_{qp} = (p/q)`, `R_{qq} = ((n/q)/q)`, `R_{q2} = (2/q)`,
     using `[𝔭_q] = Π_{p≠q}[𝔭_p]` from `span_omega`.
5. **`Redei/Dirichlet.lean`** (350).
   - `exists_absNorm_eq_of_isSquare`: `p ∤ 2n` is not ramified (step 2); it is not inert, because
     `(m+ω)(m−ω) ∈ pO` and `σ` give `p ∣ 2m`.
   - `exists_chi_eq`: residues mod each `q` (`FiniteField.exists_nonsquare`), a residue mod 4, CRT mod
     `4n`, Dirichlet (`Nat.forall_exists_prime_gt_and_zmodEq`), and `jacobiSym.quadratic_reciprocity`
     for `(−n/p) = 1`.
6. **`Redei/FourRank.lean`** (250).
   - `odd_card_range_sq_iff` (done in the probe).
   - `#(G/G²) = #G[2]`.
   - `range_sq_eq_ker_chi` (the count above).
   - `odd_gCl_iff`: `g(n)` is odd iff the kernel of the Rédei matrix `R` is `{0, e_n}`. This is Rédei's
     theorem in its 4-rank-0 form.
7. **`Redei/Kernel.lean`** (250), in the generic `Sec3` setting, independent of 1–6.
   `kernel_trivial_iff_redeiG`: the kernel of `(L_B | z_B)` (column `z_B` only if `y(B) = 0`) is the
   trivial one iff `redeiG = 1`. This is tyz-5b §2.2 Cases 1 and 2. It uses `Sec3.pmin_lapl_offdiag`
   (Lemma 2.2(2)), `Sec3.kappa_eq_kappa` (2.2(1)), `Matrix.exists_mulVec_eq_zero_iff`, and the
   row-sum and column-sum facts (`Sec3.colSum_lapl`).
8. **`Redei/Bridge.lean`** (250).
   - Reindex `(dProd B).primeFactors` to `B ⊆ d.primeFactors`.
   - `n % 4 = 3 ↔ Σ_B y = 1` (`lam8_prod`); `R` becomes `lapl (aBit d) B`, and `zBit` (`legBit_prod`).
   - `gCl_eq_gBit`.
   - `T5bCl`, `CertifiedRankTYZCl`, `certifiedRankTYZ_iff` (done in the probe).

Dependencies: 1 → 2 → {3, 4} → 5 → 6 → 8 ← 7. Step 7 can run in parallel with everything else.

### 3.3 Size

| Module | Lines |
| --- | --- |
| Field | 250 |
| Primes | 500 |
| Ambiguous | 400 |
| Genus | 400 |
| Dirichlet | 350 |
| FourRank | 250 |
| Kernel | 250 |
| Bridge | 250 |
| **Total** | **≈ 2,650** |

Budget 3,500 for overruns; this project's Lean files have tended to come in 1.3–1.5 times the
estimate. As fleet tasks: (i) Field + Primes; (ii) Ambiguous + Genus; (iii) Dirichlet + FourRank +
Bridge; (iv) Kernel, in parallel with (i).

### 3.4 Risks

- **Ideal bookkeeping in `𝓞 K`.** Pointwise `σ • I` on products and powers, cancellation in
  `Ideal O`, and `absNorm (σ • I) = absNorm I` (via `relNorm_smul` and `relNorm_int`). These are routine
  but verbose. The probe confirms that the Galois machinery instantiates on `𝓞 (QNeg n)` with no
  extra setup (`fundamental_identity`, `exists_conj_eq` compile).
- **Choice-based `chi`.** It is defined through a chosen representative prime to `q`; the homomorphism
  property needs the well-definedness lemma twice. This is moderate.
- **Jacobi bookkeeping in step 5.** Signs `qrSign`, `χ₄`; casts between `ℕ`, `ℤ` and `ZMod`. This is
  moderate; the project already has `legBit` lemmas.
- **Reindexing in step 8.** `(dProd B).primeFactors` against `B : Finset d.primeFactors`, and `Fin`-free
  sums. This is known friction (cr5b-sec3 handled similar things).
- **Elaboration cost.** It is low: the probe, with all statements and the instance checks, elaborates in
  about 6 s including imports.
- **No mathematical risk was found.** Every step was checked on paper above, including the edge cases
  `n = 3` (units `±ζ₆` do not matter: only rational units enter), `t = 1`, and both residues of `n` mod 4.
  Spot checks of `odd_gCl_iff`: `n = p ≡ 3 (4)` gives `g` odd; `n = p ≡ 5 (8)` gives `g` odd
  (`h(−20) = 2`); `n = p ≡ 1 (8)` gives `g` even (`h(−68) = 4`, cyclic).

### 3.5 First leaf

`Redei/Primes.lean: prime_trichotomy` and `dvd_of_ramified`, on top of the Field facts. They exercise
the Galois/ideal API that every later step uses. If they go through at about the estimated size, the
rest is ordinary work. If not, the plan should be re-costed before starting steps 3–6. Step 7 (`Kernel`)
is the safe parallel leaf: pure 𝔽₂ linear algebra on existing `Sec3` lemmas.

## 4. What the probe checks

`scratch/redei-plan/Probe.lean` (342 lines, 24 declarations with `sorry`), compiled with `lake env lean`
after `lake build ZInQKernel.RouteK.Rank5b.Sec3.TYZ`:

- **Inferred instances on `QNeg n`:** `Field`, `CharZero`, `FiniteDimensional ℚ`, `NumberField`
  (empty `where`), `IsGalois ℚ`, `Fintype (ClassGroup (𝓞 _))`.
- **Proved:** `factNeg`, `neZero_dProd`, `card_gal`, `isIntegral_omega`, `algNorm_eq`, `norm_nonneg`,
  `fundamental_identity`, `exists_conj_eq`, `odd_card_range_sq_iff`, `T5bCl_eq_T5b`,
  `certifiedRankTYZ_iff`.
- **Typechecked with `sorry`:** the target `gCl_eq_gBit`, and every intermediate statement of §3.2
  (`prime_trichotomy`, `dvd_of_ramified`, `ramIdeal_spec`, `span_omega`, `mul_conj_ideal`, `psi`,
  `range_psi`, `exists_mk0_coprime`, `chi`, `chi_mk0`, `chi_psi`, `exists_absNorm_eq_of_isSquare`,
  `exists_chi_eq`, `range_sq_eq_ker_chi`, `odd_gCl_iff`, `kernel_trivial_iff_redeiG`).

## 5. Recommendation

**Payoff.** One classical input leaves the trust statement of CR₃: Rédei 1934, textbook genus
theory. It is already cross-checked numerically: pc-audit compared Smith's Table 1 with PARI class
groups on all squarefree `n < 20000`, and tyz-5b §6 checks it inside the genus sums. The deep inputs,
TYZ (Waldspurger, Yuan–Zhang–Zhang's Gross–Zagier, Tian's induction) and Gross–Zagier–Kolyvagin, stay.
So the trust profile of CR₃ does not change in kind. What improves is the precision of the citation:
the hypothesis would be TYZ's statement verbatim, with `g(d) = #2Cl(ℚ(√−d))`, rather than its
translation into Legendre bits.

**Cost.** About 2,700 lines (budget 3,500), three or four fleet tasks, low mathematical risk.

**Verdict: not worth doing now; worth doing later as a background project.** Open items with larger
payoff remain: SixContactMin, the UNCHECKED journal statement of TYZ Theorems 1.2/3.5(2) (tyz-5b §1),
and the reading `d₁ = 1`.

**Cheap step worth taking now** (about 100 lines, by a later task, since this task does not edit
`ZInQKernel/`):
- move `QNeg`, `gCl`, `T5bCl`, `CertifiedRankTYZCl` and a Prop `RedeiFormula` (the statement of
  `gCl_eq_gBit`) into `ZInQKernel/RouteK/Rank5b/Sec3/`;
- prove `RedeiFormula → (CertifiedRankTYZCl ↔ CertifiedRankTYZ)`; the probe's proof works verbatim.

Then the trust statement cites Rédei through an exact Lean statement instead of prose. A later
formalization would discharge `RedeiFormula` without touching anything else.

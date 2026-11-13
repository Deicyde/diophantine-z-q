# gz-theta: the leaf `HeckeThetaNewform` (L1 of gz-decomp)

Status: research note (task gz-theta, 2026-11-13), branch `wip/gz-theta` (base `wip/gz-decomp`
dcddd423, merged with `origin/wip/gz-license` 7f3880af). Lean: new files
`ZInQKernel/Contrib/GZTheta/{Basic,BadCoeff,Eta,Eta32,EtaForm32,Main,ThetaUnique,TripleProduct,
JacobiGauss,HeckeComb,EtaTheta,Final,Split}.lean`. Axiom
check `scratch/gz-theta/Check.lean` (output `scratch/gz-theta/out_check_axioms.txt`). Log
`scratch/gz-theta/log.md`. No existing file of the project was edited, and no Tau Ceti module
was modified. One Tau Ceti module was vendored unmodified from tc-oct16 (5a01f5fe),
`Newforms/BadPrime/Vanishing.lean` (list `scratch/gz-theta/tc-modules.txt`; NOTICE entry added
after merging `wip/gz-license`; `diffcheck2.py`: IDENT, 0 MOD-UNNOTED). §2-3 are the plan written before building (step 1); §0 and §4 report
what was built.

Marks: **VERIFIED** (read in a source named here, computed, or compiled), **STANDARD**
(published, reference given), **SPECULATIVE**. No network on this host: every theorem number
of the literature below is **UNVERIFIED**.

## 0. Main result

**Hecke's theorem for `ψ₁` is proved, and the leaf `HeckeThetaNewform` is reduced to newness
alone.** The theta series `∑ heckeCoeff 1 n qⁿ` of the Hecke character of `y² = x³ − x` is the
cusp form `η(4τ)²η(8τ)² ∈ S₂(Γ₀(32))` (`cmForm32`). Its twists `f_d = f₁ ⊗ (·/d)` are Hecke
eigenforms of every `T_n` on `Γ₁(32 d²)` with trivial nebentypus and `q`-expansion
`∑ heckeCoeff d n qⁿ` (`exists_eigenform_heckeCoeff`). The only part of L1 left open is the
newness of `f_d` at level `32 d²` (`NewCM`), equivalently the bad-prime coefficients of its
newform (`BadCoeffCM`); `NewCM` is further reduced to newness at level 32 (`NewAt32`) and the
Atkin–Li twist theorem (`AtkinLiTwistNew`).

Every theorem below compiles, and `#print axioms` gives exactly
`[propext, Classical.choice, Quot.sound]` for each (VERIFIED: `scratch/gz-theta/Check.lean`,
`Check2.lean`, outputs `out_check_axioms.txt`, `out_check_axioms2.txt`).

```lean
-- ZInQKernel/Contrib/GZTheta/EtaTheta.lean, Final.lean, Split.lean
theorem ZInQ.GZTheta.etaThetaIdentity : EtaThetaIdentity
  -- ∀ τ : ℍ, HasSum (fun n => heckeCoeff 1 n * cexp (2πiτ) ^ n) (η (4τ) ^ 2 * η (8τ) ^ 2)
theorem ZInQ.GZTheta.cmForm32 : CMForm32
  -- ∃ F : CuspForm ((Gamma0 32).map (mapGL ℝ)) 2, ∀ n, (qExpansion 1 F).coeff n = heckeCoeff 1 n
theorem ZInQ.GZTheta.exists_eigenform_heckeCoeff (d : ℕ) [NeZero d] (hd4 : d % 4 = 1)
    (hsq : Squarefree d) :
    ∃ E : HeckeRing.GL2.Eigenform (32 * d ^ 2) 2, E.χ = 1 ∧
      ∀ n : ℕ, (qExpansion 1 E.toCuspForm).coeff n = heckeCoeff d n
theorem ZInQ.GZTheta.heckeThetaNewform_of_newCM : NewCM → ZInQ.GZDecomp.HeckeThetaNewform
theorem ZInQ.GZTheta.heckeThetaNewform_of_badCoeffCM : BadCoeffCM → ZInQ.GZDecomp.HeckeThetaNewform
theorem ZInQ.GZTheta.newCM_of_newAt32_atkinLi : NewAt32 → AtkinLiTwistNew → NewCM
theorem ZInQ.GZTheta.heckeThetaNewform_of_newAt32_atkinLi :
    NewAt32 → AtkinLiTwistNew → ZInQ.GZDecomp.HeckeThetaNewform
theorem ZInQ.GZTheta.frozenTarget_of_sixContactMin_tyzThm35ReadingA_newCM_gzLeaves :
    ZInQ.SixContactMin → ZInQ.Literature.TYZThm35ReadingA → NewCM →
      ZInQ.GZDecomp.FHNonvanishing → ZInQ.GZDecomp.GrossZagierHeegner → ZInQ.FrozenTarget
-- the analytic ingredients
theorem ZInQ.GZTheta.jacobiTheta₂_eq_jtpP {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    jacobiTheta₂ z τ = jtpP τ z                       -- Jacobi's triple product (TripleProduct.lean)
theorem ZInQ.GZTheta.hasSum_jacobi {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n : ℤ => (n : ℂ) * jacobiTheta₂_term n ((1 + τ) / 2) τ) (jtpA τ ^ 3)
theorem ZInQ.GZTheta.hasSum_gauss {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n : ℤ => jacobiTheta₂_term n (1 / 2) τ)
      (gp (qJ τ) (-1) 2 2 * gp (qJ τ) (-1) 2 1 * gp (qJ τ) (-1) 2 1)   -- (JacobiGauss.lean)
theorem ZInQ.GZTheta.eq_zero_of_theta_fe {τ : ℂ} {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h1 : ∀ z, f (z + 1) = f z) (hτ : ∀ z, f (z + τ) = cexp (-π * I * (τ + 2 * z)) * f z)
    (h0 : ∫ x : ℝ in (0 : ℝ)..1, f x = 0) : f = 0       -- (ThetaUnique.lean)
def ZInQ.GZTheta.etaForm32 : CuspForm ((Gamma0 32).map (mapGL ℝ)) 2   -- ⇑etaForm32 = η(4τ)²η(8τ)²
theorem ZInQ.GZTheta.etaQuot32_slash_eq {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 32) :
    etaQuot32 ∣[(2 : ℤ)] γ = etaQuot32                                   -- (Eta32.lean)
theorem ZInQ.GZTheta.eta_sq_mobius : ∀ (fuel : ℕ) (a b c d : ℤ), c.natAbs ≤ fuel →
    a * d - b * c = 1 → ∀ z : ℂ, 0 < z.im →
      η ((a * z + b) / (c * z + d)) ^ 2 = zeta12 ^ etaSqExp fuel a b c d * (c * z + d) * η z ^ 2
```

The remaining Props (all STANDARD, none proved here):

```lean
-- newness of the theta series of ψ_d at level 32 d²  (Basic.lean)
def NewCM : Prop :=
  ∀ (d : ℕ) [NeZero d], d % 4 = 1 → Squarefree d →
    ∀ F : CuspForm ((Gamma1 (32 * d ^ 2)).map (mapGL ℝ)) 2,
      (∀ n : ℕ, (qExpansion 1 F).coeff n = heckeCoeff d n) → F ∈ TauCeti.cuspFormsNew (32 * d ^ 2) 2
-- equivalent route: the bad-prime coefficients of the newform of ψ_d  (BadCoeff.lean)
def BadCoeffCM : Prop :=
  ∀ d : ℕ, d % 4 = 1 → Squarefree d →
    ∀ (M : ℕ) [NeZero M] (g : Newform M 2), g.χ = 1 →
      (∀ p : ℕ, p.Prime → ¬ p ∣ 2 * d → coeff g p = heckeCoeff d p) →
      ∀ p : ℕ, p.Prime → p ∣ 2 * d → p ∣ M ∧ coeff g p = 0
-- NewCM ⇐ NewAt32 ∧ AtkinLiTwistNew  (Split.lean)
def NewAt32 : Prop :=
  ∀ F : CuspForm ((Gamma1 32).map (mapGL ℝ)) 2,
    (∀ n : ℕ, (qExpansion 1 F).coeff n = heckeCoeff 1 n) → F ∈ TauCeti.cuspFormsNew 32 2
def AtkinLiTwistNew : Prop :=
  ∀ (M : ℕ) [NeZero M] (g : Newform M 2), g.χ = 1 →
    ∀ (r : ℕ) [NeZero r], r % 4 = 1 → Squarefree r → Nat.Coprime r M →
      CuspForm.twist (jacobiChar r) (dvd_twist_left M r) (dvd_twist_right M r) g.toCuspForm ∈
        TauCeti.cuspFormsNew (M * r ^ 2) 2
```

So: **L1 ⇐ NewCM**, and **NewCM ⇐ NewAt32 ∧ AtkinLiTwistNew** (Atkin–Li, Invent. Math. 48
(1978), Thm 3.1; UNVERIFIED locator). Together with gz-decomp:
`FrozenTarget ⇐ SixContactMin ∧ TYZThm35ReadingA ∧ NewCM ∧ FHNonvanishing ∧ GrossZagierHeegner`.

What is proved, informally:
1. **Jacobi's triple product identity** for Mathlib's `jacobiTheta₂`, by a uniqueness theorem
   for entire functions with the functional equations of `θ` (Fourier coefficients and Cauchy's
   theorem on rectangles) and the classical `c(τ) = c(4τ)` normalization; then Jacobi's `η³`
   identity (derivative at the zero `(1+τ)/2`) and Gauss's identity (`z = 1/2`).
2. **The `q`-series identity** `η(4τ)²η(8τ)² = ∑_{α ≡ 1 mod (2+2i)} α q^{N α} = ∑ heckeCoeff 1 n qⁿ`
   (product of the two identities at `8τ`, regrouped by `N = (2n+1)² + (2m)²`, and a
   combinatorial identity for `heckeCoeff 1 N` over the four associates).
3. **`η(4τ)²η(8τ)² ∈ S₂(Γ₀(32))`** from Mathlib's two generator laws of `η` only: the
   multiplier of `η²` by the Euclidean algorithm, Schreier generators of `Γ₀(32)` checked by
   `decide`, and the cusps by a Hermite decomposition (§4.2).
4. **Twist and eigenform**: `f_d = f₁ ⊗ (·/d)` on `Γ₁(32 d²)`, trivial nebentypus, eigen for all
   `T_n` (§4.1).
5. **The leaf from newness** (directly, or via Tau Ceti's Diamond–Shurman 5.8.4 and the bad-prime
   coefficients).

## 1. The leaf

```lean
def ZInQ.GZDecomp.HeckeThetaNewform : Prop :=
  ∀ d : ℕ, d % 4 = 1 → Squarefree d →
    ∃ (N : ℕ) (_ : NeZero N) (f : Newform N 2), f.χ = 1 ∧
      ∀ n : ℕ, n ≠ 0 → coeff f n = ZInQ.Contrib.HeckeFE.heckeCoeff d n
```

(`ZInQKernel/Contrib/GZDecomp/Decomp.lean`, VERIFIED by reading.) `Newform N k` is Tau Ceti's
(`Newforms/Newform.lean`): a nonzero cusp form on `Γ₁(N)` in `cuspFormCharSpace k χ`, eigen for
the Hecke-ring elements `T_n`, `(n, N) = 1`, in `TauCeti.cuspFormsNew N k` (the Petersson
complement of the level raises), with `a₁ = 1`. `coeff f n` is the `n`-th coefficient of
Mathlib's `qExpansion 1`. `heckeCoeff d n = ¼ ∑_{a²+b²=n} (n/d)·unitOf(a,b mod 4)·(a+bi)`
(`HeckeFE/Basic.lean:473`).

## 2. Mathematics (plan)

Write `ψ = ψ_d` for the Hecke character of `ℚ(i)` of `C_d`: `ψ_d((α)) = (Nα/d)·α'` with `α'` the
primary associate of `α` (`α' ≡ 1 mod (2+2i)`), conductor `(1+i)³·d` (STANDARD; Ireland–Rosen
Ch. 18, UNVERIFIED locator). Its theta series is

  `f_d(τ) = ∑_{n ≥ 1} heckeCoeff d n · qⁿ = ¼ ∑_{α ∈ ℤ[i]} ψ_d(α) q^{N α}`.

### 2.1 Reduction to `d = 1` by a quadratic twist (proved here)

Since `N(α) = n` on the fibre, `(N α / d) = (n/d)` factors out:

  `heckeCoeff d n = (n/d) · heckeCoeff 1 n`  (Jacobi symbol `(n/d)`).

For squarefree `d ≡ 1 (mod 4)` the map `n ↦ (n/d)` is a Dirichlet character `χ_d` modulo `d`
(multiplicative in `n`, periodic mod `d`, zero exactly off the units), with `χ_d² = 1` on units.
So `f_d = f_1 ⊗ χ_d`. Tau Ceti's `CuspForm.twist` (`Twist/Basic.lean`, vendored) maps
`S_2(Γ₁(32), χ)` to `S_2(Γ₁(L), χ·χ_d²)` for `32·d ∣ L`, `d² ∣ L`, with
`aₙ(f ⊗ χ_d) = χ_d(n)·aₙ(f)` (`CuspForm.qExpansion_twist_coeff`,
`CuspForm.twist_mem_cuspFormCharSpace`). Take `L = 32 d²`. With trivial `χ`, the character
`χ·χ_d²` is trivial. So **modularity of the single form `f_1 ∈ S_2(Γ₀(32))` gives
`f_d ∈ S_2(Γ₁(32 d²), 1)` with the right coefficients, for every `d`.**

### 2.2 Hecke eigenform (proved here, from the coefficients)

`heckeCoeff d` is multiplicative (`HeckeFE.heckeMult`, proved) and satisfies
`a_{p^{k+2}} = a_p a_{p^{k+1}} − [p ∤ 2d]·p·a_{p^k}` (`HeckeFE.HeckePrimePow`, proved for odd
squarefree `d` from `heckePrimePow_of_split`, `heckePrimePowSplit`). At level `L = 32 d²` the
trivial character extended by zero is `p ↦ [p ∤ 2d]`, and the weight factor is `p^{k−1} = p`. So
Tau Ceti's `Eigenform.exists_toCuspForm_eq_and_χ_eq_of_qExpansion_coeff_mul_of_prime_pow_add_two`
(`Newforms/Coefficient.lean`, Diamond–Shurman Prop. 5.8.5) makes `f_d` an eigenform of **every**
`T_n` (bad `n` included), nonzero because `a₁ = heckeCoeff d 1 = 1` (`HeckeFE.heckeCoeff_one`).

### 2.3 Newness (not proved; a remaining Prop)

`f_d` is new at level `32 d²` because `ψ_d` is primitive of conductor `𝔣 = (1+i)³ d` and
`|d_K| N𝔣 = 4 · 8 d² = 32 d²` (Miyake, *Modular forms*, Thm 4.8.2; Shimura 1971 §3.6; Iwaniec,
*Topics*, Thm 12.5; all UNVERIFIED locators, STANDARD content). The proof in the literature uses
the functional equations of the twists `f_d ⊗ χ` (Weil's converse theorem / Atkin–Li), or local
representation theory (the local component at `p ∣ 2d` is a ramified principal series or a
supercuspidal of conductor exponent `≥ 2`). None of this is in Mathlib or the vendored Tau
Ceti. Two equivalent ways to leave it:

* **(NewCM)** every cusp form on `Γ₁(32d²)` with coefficients `heckeCoeff d` lies in
  `TauCeti.cuspFormsNew (32 d²) 2`;
* **(BadCoeffCM)** a newform of trivial character whose eigenvalues at the primes `p ∤ 2d` are
  `heckeCoeff d p` has level divisible by `p` and `a_p = 0` at every `p ∣ 2d` (that is, `p² ∣`
  level). With Tau Ceti's Diamond–Shurman 5.8.4 (`exists_newform_comp_unitsMap_eq_and_eigenvalue_eq_of_forall_heckeTCuspNat_eq_smul`,
  vendored by wip/t25-newform) this gives the leaf as well; it isolates the local content at
  the bad primes.

### 2.4 Modularity of `f_1` (not proved; a remaining Prop, the analytic core)

  **(CMForm32)** there is `F ∈ S_2(Γ₀(32))` with `aₙ(F) = heckeCoeff 1 n` for all `n`.

This is Hecke's theorem for `ψ_1`, i.e. modularity of `y² = x³ − x`
(`f_1 = η(4τ)²η(8τ)²`). Classical proof: theta series with the harmonic polynomial `α` of the
coset `α ≡ 1 mod (2+2i)`; its transformation under `γ ∈ Γ₀(32)` comes from splitting the lattice
modulo `c`, Poisson summation (the Fourier transform of `α e^{πiτ|α|²}` is
`(i/τ)²·ᾱ…`-type, Hecke's identity for harmonic polynomials) and the evaluation of the resulting
quadratic Gauss sums (Schoeneberg, *Elliptic modular functions*, Ch. IX; Iwaniec, *Topics*,
Thm 10.9; Miyake Cor. 4.9.5; all UNVERIFIED).

What exists (VERIFIED by reading):
* the project's `HeckeFE` proves the Poisson/Mellin functional equation of `∑ c(α) α N(α)^{−s}`
  on the imaginary axis only (`gaussTheta_one_div`, `lambdaC_two_sub`), i.e. the Fricke
  involution, not the `Γ₀(N)` law;
* Mathlib: `jacobiTheta₂`, `jacobiTheta₂'` with the inversion law (rank one, `S` and `T` only);
* Tau Ceti oct16/nov01: lattice theta series `Θ_L`, `θ_{γ+L}` with the inversion and translation
  laws (nov01, `ThetaSeries/`), no general level, no harmonic polynomial; Tau Ceti main (reference
  only, not vendorable here) has the Hecke–Schoeneberg theorem for even lattices of even rank
  (`ThetaSeries/GeneralLevel.lean`), still without harmonic polynomials; Dedekind `η` with an
  abstract multiplier (`DedekindEta/Transformation.lean`), not the explicit Rademacher formula.
* There is no theta series of a Grössencharacter and no eta-quotient modularity anywhere.

Size estimate (SPECULATIVE): the `Γ₀(32)` law for `f_1` from first principles (coset splitting,
Poisson with the harmonic polynomial in rank 2 or with `jacobiTheta₂'` in rank 1, Gauss sums with
signs) is several thousand lines; it is not attempted in this task.

## 3. Lean plan

`ZInQKernel/Contrib/GZTheta/Basic.lean` (new):

1. `jacobiChar d : DirichletCharacter ℂ d`, `jacobiChar d n = (n/d)`; `jacobiChar_sq` on units.
2. `heckeCoeff_eq_jacobiSym_mul : heckeCoeff d n = (n/d) * heckeCoeff 1 n`.
3. `CMForm32 : Prop` (§2.4) and the Γ₁/char-space version (`TauCeti.restrict_mem_cuspFormCharSpace_one`).
4. `cmForm` construction: twist, its coefficients, its character space `1`.
5. `exists_eigenform_cm : CMForm32 → ∀ d, d % 4 = 1 → Squarefree d →
   ∃ F : Eigenform (32 d²) 2, F.χ = 1 ∧ ∀ n, aₙ(F) = heckeCoeff d n`.
6. `NewCM : Prop` and `heckeThetaNewform_of_cmForm32_newCM : CMForm32 → NewCM → HeckeThetaNewform`.
7. If time: `BadCoeffCM` and `heckeThetaNewform_of_cmForm32_badCoeffCM`.

(Plan change after step 6, recorded in the log: the modularity of `f_1` turned out to be
reachable through the eta quotient `η(4τ)²η(8τ)²`, see §4.2.)

## 4. What was built

### 4.1 The twist, the eigenform, the leaf (`Basic.lean`, `BadCoeff.lean`)

* `jacobiChar d : DirichletCharacter ℂ d`, `jacobiChar d n = (n/d)` (`jacobiChar_natCast`), with
  `(u/d)² = 1` on units (`jacobiChar_sq_unit`).
* `heckeCoeff_eq_jacobiSym_mul : heckeCoeff d n = (n/d) * heckeCoeff 1 n` (the Jacobi symbol of
  `N α = n` factors out of the fibre sum).
* `cmForm F d := CuspForm.twist (jacobiChar d) _ _ (restrict32 F)` at level `32 d²`;
  `qExpansion_cmForm_coeff : aₙ(cmForm F d) = heckeCoeff d n` (Tau Ceti
  `CuspForm.qExpansion_twist_coeff`); `cmForm_mem_cuspFormCharSpace` with character `1` (Tau Ceti
  `CuspForm.twist_mem_cuspFormCharSpace`, character `1·(·/d)² = 1`, and
  `TauCeti.restrict_mem_cuspFormCharSpace_one`).
* `exists_eigenformAway_cmForm`, `exists_eigenform_cmForm`: Tau Ceti's Diamond–Shurman 5.8.5
  (`exists_toCuspForm_eq_and_χ_eq_of_qExpansion_coeff_mul_of_prime_pow_add_two`) fed with
  `HeckeFE.heckeMult` and `HeckeFE.heckePrimePow_of_split` (the recursion
  `a_{p^{k+2}} = a_p a_{p^{k+1}} − [p ∤ 2d] p a_{p^k}` matches the trivial character extended by
  zero at level `32 d²`, since `p ∣ 32 d² ↔ p ∣ 2d`).
* `heckeThetaNewform_of_cmForm32_newCM`: the newform is the eigenform with `isNew` from `NewCM`
  and `a₁ = heckeCoeff d 1 = 1`.
* `heckeThetaNewform_of_cmForm32_badCoeffCM`: Tau Ceti's
  `Newform.exists_newform_comp_unitsMap_eq_and_eigenvalue_eq_of_forall_heckeTCuspNat_eq_smul`
  gives a newform `g` of level `M ∣ 32 d²`, character `1`, eigenvalues `heckeCoeff d p` at
  `p ∤ 2d`; `BadCoeffCM` gives `p ∣ M` and `a_p(g) = 0` at `p ∣ 2d`; then
  `coeff_eq_heckeCoeff_of_good_bad` identifies all coefficients (both sides multiplicative, same
  prime-power recursions; `Newform.toEigenform` and Diamond–Shurman 5.8.5 for `g`).

### 4.2 Modularity of `η(4τ)²η(8τ)²` (`Eta.lean`, `Eta32.lean`, `EtaForm32.lean`)

* **Multiplier of `η²`.** `η²` has weight 1, so `η²(γz) = ψ(γ)(cz + d)η²(z)` with a root of
  unity `ψ(γ)` and no square-root ambiguity. `etaSqExp` computes `ψ(γ) = ζ^{etaSqExp}`,
  `ζ = e^{πi/6}`, by the Euclidean algorithm: for `c ≠ 0`, `γ = T^q S γ₃` with `q = ⌊a/c⌋`,
  `γ₃ = (c, d; −(a mod c), −(b − qd))`, so `etaSqExp γ = q − 3 + etaSqExp γ₃`; for `c = 0`,
  `γ = ±T^{±b}`. `eta_sq_mobius` proves the law by induction from Mathlib's
  `η(z+1) = e^{πi/12}η(z)` and `η(−1/z) = (√i)⁻¹√z η(z)` (`eta_comp_eq_csqrt_I_inv`). The
  exponent is defined by structural recursion on fuel, so the kernel evaluates it.
* **`Γ₀(32)`-invariance.** For `γ ∈ Γ₀(32)`, `4γτ = γ'(4τ)`, `8γτ = γ''(8τ)` with
  `γ' = (a, 4b; c/4, d)`, `γ'' = (a, 8b; c/8, d)`, so `f(γτ) = ζ^{E(γ)}(cτ + d)² f(τ)`
  (`etaQuot32_slash`). `E ≡ 0 (mod 12)` on all of `Γ₀(32)` by **Schreier's lemma** (Mathlib
  `Subgroup.closure_mul_image_eq`, with `SpecialLinearGroup.SL2Z_generators`): the 48 matrices
  `(1 0; x 1)` (`x < 32`) and `(0 −1; 1 2j)` (`j < 16`) form a transversal (`isComplement_R32`;
  the representative of `g` is computed from its bottom row with `d⁸ ≡ 1 (mod 32)` for odd `d`),
  and `E ≡ 0 (mod 12)` on the 96 Schreier generators is checked by `decide`
  (`schreier_check_A`, `schreier_check_B`). The set of `γ` fixing `f` is a subgroup, so it
  contains `Γ₀(32)` (`etaQuot32_slash_eq`).
* **Cusps.** `diag(m, 1)γ = γ₁(α β; 0 δ)` with `γ₁ ∈ SL(2, ℤ)`, `α, δ > 0` (`exists_hermite`),
  so `f ∣[2] γ = C·η(w₁)²η(w₂)²` with `Im wᵢ → ∞`; `η → 0` at `i∞` from Mathlib's
  `discriminant_isZeroAtImInfty`. Mathlib's `OnePoint.isZeroAt_iff_forall_SL2Z` then gives
  `zero_at_cusps'`, as in Mathlib's `CuspForm.discriminant`.
* `cmForm32_of_etaThetaIdentity`: coefficients by `ModularFormClass.qExpansion_coeff_unique`.

The method (Euclidean multiplier of `η²`, Schreier generators checked by `decide`) proves the
modularity of any eta quotient of even weight built from `η²`-factors at any level, with no
Dedekind sums. **Numerics** (VERIFIED): the eta law on 33 random `γ` and `E ≡ 0 (mod 12)` on 3000
random `γ ∈ Γ₀(32)` (`scratch/gz-theta/eta_exp_check.py`).

# Mathlib inventory for an explicit 2-descent on y^2 = x^3 - d^2 x

Mathlib v4.35.0, rev 56a0058, at `/home/jackmccarthy/dzq/.lake/packages/mathlib/Mathlib`
(written `M/` below). Repo: `/home/jackmccarthy/dzq-wt/nt-prop0/ZInQKernel` (written `ZQ/`).
Found with grep/sed only; nothing was built. Line numbers are for this checkout.

Verdict key: EXISTS = usable as is; PARTIAL = the pieces are there but the statement we want is not;
MISSING = not in Mathlib.

---------------------------------------------------------------------------------------------------

## 1. p-adic numbers

### 1.1 Basic types and casts: EXISTS
- `Padic p` with notation `ℚ_[p]`: `M/NumberTheory/Padics/PadicNumbers.lean:534,539`. Instances:
  `normedField` (801), `NontriviallyNormedField` (873), `CompleteSpace ℚ_[p]` (1027),
  `CauSeq.IsComplete` (995), `CharZero` (566).
- ℚ → ℚ_[p] is plain `Rat.cast` (the field cast). Lemmas: `Padic.coe_inj` (563), `coe_add/mul/sub/div/neg`
  (573–589), `Padic.eq_padicNorm (q : ℚ) : ‖(q : ℚ_[p])‖ = padicNorm p q` (850),
  `norm_rat_le_one` (902), `norm_int_le_one` (919), `norm_intCast_lt_one_iff : ‖(k:ℚ_[p])‖ < 1 ↔ ↑p ∣ k` (924),
  `norm_intCast_eq_one_iff` (950), `rat_dense` (816), `denseRange_ratCast` (821).
- `PadicInt p` with notation `ℤ_[p]`: `M/NumberTheory/Padics/PadicIntegers.lean:71` (it is the subring `‖x‖ ≤ 1`).
  Coercion to ℚ_[p] (82), `Padic.lift x hx` (93), `completeSpace` (201), `NormedCommRing` (210),
  `IsDomain` (221), `IsLocalRing` (518), `IsDiscreteValuationRing ℤ_[p]` (540),
  `IsAdicComplete (maximalIdeal ℤ_[p]) ℤ_[p]` (551), `Algebra ℤ_[p] ℚ_[p]` (576),
  `IsFractionRing ℤ_[p] ℚ_[p]` (584).
- Local field: `instance : IsNonarchimedeanLocalField ℚ_[p]` (`M/NumberTheory/Padics/LocalField.lean:25`).
- Comparison with the adic completion: `Padic.adicCompletionEquiv`, `Rat.HeightOneSpectrum.padicEquiv`,
  `primesEquiv` (`M/NumberTheory/Padics/HeightOneSpectrum.lean:109,144,218,234`). Also
  `Padic.withValRingEquiv` (`M/NumberTheory/Padics/WithVal.lean:104`).

### 1.2 Valuations: EXISTS
- `padicValNat`, `padicValInt` (`M/NumberTheory/Padics/PadicVal/Basic.lean:88`), `padicValRat` (126).
  Lemmas: `padicValRat.mul` (223), `.pow` (240), `.inv` (249), `.div` (261), `.neg` (139),
  `min_le_padicValRat_add` (312), `add_eq_min` (319), `add_eq_of_lt` (329), `padicValInt.mul` (722),
  `padicValInt_dvd_iff` (709).
- **`Rat.isSquare_iff_even_factorization`** (`PadicVal/Basic.lean:394`):
  `IsSquare a ↔ 0 ≤ a ∧ ∀ (p : ℕ), p.Prime → Even (padicValRat p a)` (for `a : ℚ`). This is the
  local-global principle for squares in ℚ, with "local" meaning valuations plus sign.
- `Padic.valuation : ℚ_[p] → ℤ` (`PadicNumbers.lean:1041`). Lemmas:
  `norm_eq_zpow_neg_valuation : x ≠ 0 → ‖x‖ = (p : ℝ) ^ (-x.valuation)` (1054),
  `valuation_ratCast (q : ℚ) : valuation (q : ℚ_[p]) = padicValRat p q` (1066), `valuation_intCast` (1075),
  `valuation_natCast` (1079), `valuation_p` (1092), `le_valuation_add` (1095), `valuation_mul` (1107),
  `valuation_inv` (1117), `valuation_pow` (1127), `valuation_zpow` (1135),
  `norm_le_one_iff_val_nonneg` (1251). Also `Padic.mulValuation : Valuation ℚ_[p] ℤᵐ⁰` (1183) and
  `Padic.addValuation` (1223).
- `PadicInt.valuation (x : ℤ_[p]) : ℕ` (`PadicIntegers.lean:343`). Lemmas: `valuation_coe` (345),
  `valuation_mul` (355), `valuation_pow` (360),
  `norm_eq_zpow_neg_valuation {x : ℤ_[p]} (hx : x ≠ 0) : ‖x‖ = p ^ (-x.valuation : ℤ)` (363),
  `valuation_p_pow_mul` (368), `norm_le_pow_iff_le_valuation` (467), `mem_span_pow_iff_le_valuation` (472).

### 1.3 Units and unit decomposition: EXISTS for ℤ_[p], PARTIAL for ℚ_[p]
- `PadicInt.isUnit_iff {z : ℤ_[p]} : IsUnit z ↔ ‖z‖ = 1` (385), `not_isUnit_iff` (404), `mem_nonunits` (401),
  `norm_units` (418), `norm_lt_one_iff_dvd (x) : ‖x‖ < 1 ↔ ↑p ∣ x` (501),
  `maximalIdeal_eq_span_p` (525), `prime_p` (533), `irreducible_p` (538), `ideal_eq_span_pow_p` (545).
- `PadicInt.mkUnits {u : ℚ_[p]} (h : ‖u‖ = 1) : ℤ_[p]ˣ` (408), `mkUnits_eq` (415).
- `PadicInt.unitCoeff {x : ℤ_[p]} (hx : x ≠ 0) : ℤ_[p]ˣ` (422), with
  `unitCoeff_spec (hx : x ≠ 0) : x = (unitCoeff hx : ℤ_[p]) * (p : ℤ_[p]) ^ x.valuation` (432).
- ℚ_[p]: there is no `x = u * p^v` with `u : ℤ_[p]ˣ` for `x : ℚ_[p]`. You get it from
  `IsFractionRing` plus `unitCoeff`, or from the general DVR lemmas
  `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible` (`M/RingTheory/DiscreteValuationRing/Basic.lean:336`)
  and `unit_mul_pow_congr_unit` (387). There is no `mkUnits`-style constructor working straight from ℚ_[p]
  (only from `‖u‖ = 1`). Writing `x * p^(-v)` with norm 1 and then `mkUnits` takes a few lines.

### 1.4 Residue maps: EXISTS
`M/NumberTheory/Padics/RingHoms.lean`:
- `PadicInt.toZMod : ℤ_[p] →+* ZMod p` (301), `toZMod_spec` (319),
  `ker_toZMod : RingHom.ker toZMod = maximalIdeal ℤ_[p]` (328), `zmodRepr` (178),
  `PadicInt.residueField : IsLocalRing.ResidueField ℤ_[p] ≃+* ZMod p` (350),
  `toZMod_eq_residueField_comp_residue` (443).
- `PadicInt.toZModPow (n) : ℤ_[p] →+* ZMod (p ^ n)` (448), `ker_toZModPow` (460, kernel = span {p^n}),
  `cast_toZModPow` (497), `zmod_cast_comp_toZModPow` (479), `appr` (357), `appr_spec` (406),
  `ext_of_toZModPow` (714), `PadicInt.lift` (inverse limit, 659), `denseRange_intCast` (513).

### 1.5 Hensel's lemma: EXISTS (two forms)
- `hensels_lemma` (`M/NumberTheory/Padics/Hensel.lean:460`). Context (lines 446–450):
  `{p : ℕ} [Fact p.Prime] {R : Type*} [CommSemiring R] [Algebra R ℤ_[p]] {F : Polynomial R} {a : ℤ_[p]}`
  `(hnorm : ‖F.aeval a‖ < ‖F.derivative.aeval a‖ ^ 2)`:
  ```
  theorem hensels_lemma :
      ∃ z : ℤ_[p],
        F.aeval z = 0 ∧
          ‖z - a‖ < ‖F.derivative.aeval a‖ ∧
            ‖F.derivative.aeval z‖ = ‖F.derivative.aeval a‖ ∧
              ∀ z', F.aeval z' = 0 → ‖z' - a‖ < ‖F.derivative.aeval a‖ → z' = z
  ```
  This is the strong form `|f(a)| < |f'(a)|^2`. It gives squares in ℤ_[2] for `u ≡ 1 mod 8`: take
  `F = X^2 - u`, `a = 1`; then `|F(1)| ≤ 1/8 < |2|^2 = 1/4`.
- Henselian rings (`M/RingTheory/Henselian.lean`): `class HenselianRing (R) (I : Ideal R)` (94),
  `class HenselianLocalRing` (108), `HenselianLocalRing.TFAE` (119),
  `instance IsAdicComplete.henselianRing [IsAdicComplete I R] : HenselianRing R I` (170).
  With the instance at `PadicIntegers.lean:551` this gives `HenselianRing ℤ_[p] (maximalIdeal ℤ_[p])`
  automatically. The field of the class is
  `is_henselian : ∀ f, f.Monic → ∀ a₀, f.eval a₀ ∈ I → IsUnit (Ideal.Quotient.mk I (f.derivative.eval a₀)) → ∃ a, f.IsRoot a ∧ a - a₀ ∈ I`
  (the simple-root form, enough for odd p). There is no `HenselianLocalRing ℤ_[p]` instance, but
  `HenselianLocalRing.TFAE` builds one quickly.
- Generic local fields: `IsAdicComplete 𝓂[K] 𝒪[K]` for `IsNonarchimedeanLocalField`
  (`M/NumberTheory/LocalField/Basic.lean:178`).

### 1.6 Squares in ℚ_p and ℤ_p: MISSING
A grep for `IsSquare` in `NumberTheory/Padics`, `NumberTheory/LocalField` and `RingTheory/Henselian`
finds only `Rat.isSquare_iff_even_factorization`. None of the following exist:
- "for odd p, a unit u of ℤ_[p] is a square iff `toZMod u` is a square";
- "u ≡ 1 mod 8 implies u is a square in ℤ_[2]" (and its converse for units);
- "x ∈ ℚ_[p]ˣ is a square iff v(x) is even and the unit part is a square";
- square classes ℚ_pˣ/ℚ_pˣ² (order 4 for odd p, order 8 for p = 2), and anything on squares in local fields.

All of these follow from `hensels_lemma` / `HenselianRing` together with `unitCoeff` and `toZMod`/`toZModPow`, but
they have to be written. The repo has elementary integer versions (see 6.6).
- Real place: `Real.isSquare_iff : IsSquare x ↔ 0 ≤ x` (`M/Analysis/Real/Sqrt.lean:302`).

---------------------------------------------------------------------------------------------------

## 2. Legendre/Jacobi symbols, quadratic characters, character sums

### 2.1 Legendre symbol: EXISTS
`M/NumberTheory/LegendreSymbol/Basic.lean` (`legendreSym p a := quadraticChar (ZMod p) a`, line 109):
- `ZMod.euler_criterion {a : ZMod p} (ha : a ≠ 0) : IsSquare a ↔ a ^ (p / 2) = 1` (62), `euler_criterion_units` (50).
- `legendreSym.eq_pow` (116), `eq_one_or_neg_one` (135), `eq_zero_iff` (144), `at_zero/at_one` (148/151),
  `legendreSym.mul (a b) : legendreSym p (a*b) = legendreSym p a * legendreSym p b` (154),
  `legendreSym.hom` (159), `sq_one` (166), `sq_one'` (170), `legendreSym.mod` (176),
  `eq_one_iff {a : ℤ} (ha0 : (a : ZMod p) ≠ 0) : legendreSym p a = 1 ↔ IsSquare (a : ZMod p)` (180), `eq_one_iff'` (183),
  `eq_neg_one_iff : legendreSym p a = -1 ↔ ¬IsSquare (a : ZMod p)` (190),
  `card_sqrts (hp : p ≠ 2) (a) : ↑{x : ZMod p | x^2 = a}.toFinset.card = legendreSym p a + 1` (197),
  `eq_one_of_sq_sub_mul_sq_eq_zero` (216), `prime_dvd_of_eq_neg_one` (250).
- `legendreSym.at_neg_one (hp : p ≠ 2) : legendreSym p (-1) = χ₄ p` (274), `at_neg` (279),
  `ZMod.exists_sq_eq_neg_one_iff : IsSquare (-1 : ZMod p) ↔ p % 4 ≠ 3` (285).
- `M/NumberTheory/LegendreSymbol/QuadraticReciprocity.lean`: `legendreSym.at_two (hp : p ≠ 2) : legendreSym p 2 = χ₈ p` (60),
  `at_neg_two` (65, `= χ₈' p`), `ZMod.exists_sq_eq_two_iff (hp : p ≠ 2) : IsSquare (2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 7` (74),
  `exists_sq_eq_neg_two_iff` (80),
  `legendreSym.quadratic_reciprocity (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) : legendreSym q p * legendreSym p q = (-1) ^ (p / 2 * (q / 2))` (107),
  `quadratic_reciprocity'` (123), `quadratic_reciprocity_one_mod_four` (133), `quadratic_reciprocity_three_mod_four` (141),
  `ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one` (155), `..._three` (164).

### 2.2 Jacobi symbol: EXISTS
`M/NumberTheory/LegendreSymbol/JacobiSymbol.lean`: `jacobiSym` (86, notation `J(a | b)`),
`legendreSym.to_jacobiSym` (115), `mul_right` (131), `mul_left` (154), `eq_zero_iff` (177), `pow_left/right` (194/199),
`mod_left` (215), `nonsquare_of_jacobiSym_eq_neg_one` (272), `nonsquare_iff_jacobiSym_eq_neg_one` (280),
`isSquare_of_jacobiSym_eq_one` (286, prime modulus), `at_neg_one {b} (hb : Odd b) : J(-1 | b) = χ₄ b` (311),
`at_two : J(2 | b) = χ₈ b` (321), `at_neg_two` (325), `quadratic_reciprocity'` (404), `quadratic_reciprocity` (423),
`quadratic_reciprocity_one_mod_four` (429), `..._three_mod_four` (442), `quadratic_reciprocity_if` (448), `mod_right` (479).

### 2.3 χ₄, χ₈: EXISTS
`M/NumberTheory/LegendreSymbol/ZModChar.lean`: `ZMod.χ₄ : MulChar (ZMod 4) ℤ` (42), `χ₄_int_eq_if_mod_four` (65),
`χ₄_nat_one_mod_four` (88), `χ₄_eq_neg_one_pow` (77), `χ₈` (118), `χ₈_int_eq_if_mod_eight` (142), `χ₈_nat_eq_if_mod_eight` (150),
`χ₈'` (157), `χ₈'_int_eq_χ₄_mul_χ₈` (189).

### 2.4 Quadratic character of a finite field: EXISTS
`M/NumberTheory/LegendreSymbol/QuadraticChar/Basic.lean`: `quadraticChar F : MulChar F ℤ` (119),
`quadraticChar_one_iff_isSquare` (133), `quadraticChar_neg_one_iff_not_isSquare` (158), `quadraticChar_dichotomy` (148),
`quadraticChar_exists_neg_one` (164), `quadraticChar_eq_pow_of_char_ne_two` (180), `quadraticChar_isQuadratic` (198),
`quadraticChar_ne_one` (206),
`quadraticChar_card_sqrts (hF : ringChar F ≠ 2) (a : F) : #{x : F | x ^ 2 = a}.toFinset = quadraticChar F a + 1` (213),
`quadraticChar_sum_zero (hF : ringChar F ≠ 2) : ∑ a : F, quadraticChar F a = 0` (238), `quadraticChar_neg_one` (257),
`FiniteField.isSquare_neg_one_iff : IsSquare (-1 : F) ↔ Fintype.card F % 4 ≠ 3` (267).
`QuadraticChar/GaussSum.lean`: `quadraticChar_two` (37), `FiniteField.isSquare_two_iff` (43), `quadraticChar_neg_two` (56),
`quadraticChar_odd_prime` (93), `FiniteField.isSquare_odd_prime_iff` (103).
`M/FieldTheory/Finite/Basic.lean`: `FiniteField.isSquare_of_char_two` (770), `exists_nonsquare (hF : ringChar F ≠ 2) : ∃ a : F, ¬IsSquare a` (775),
`unit_isSquare_iff` (807), `isSquare_iff (hF : ringChar F ≠ 2) {a : F} (ha : a ≠ 0) : IsSquare a ↔ a ^ (Fintype.card F / 2) = 1` (831),
`ZMod.sq_add_sq (p) [Fact p.Prime] (x : ZMod p) : ∃ a b : ZMod p, a ^ 2 + b ^ 2 = x` (502), `CharP.sq_add_sq` (541),
`card_image_polynomial_eval` (72), `sum_pow_lt_card_sub_one` (312).

### 2.5 Character sums, Jacobi and Gauss sums: PARTIAL
- `jacobiSum` (`M/NumberTheory/JacobiSum/Basic.lean:48`), `jacobiSum_one_nontrivial` (127),
  `jacobiSum_nontrivial_inv {χ} (hχ : χ ≠ 1) : jacobiSum χ χ⁻¹ = -χ (-1)` (140),
  `jacobiSum_eq_gaussSum_mul_gaussSum_div_gaussSum` (194), `jacobiSum_mul_jacobiSum_inv` (204).
- `gaussSum` (`M/NumberTheory/GaussSum.lean:72`), `gaussSum_mul_gaussSum_eq_card` (188), `gaussSum_sq` (222),
  `FiniteField.two_pow_card` (342).
- MISSING: `∑_x χ(x^2 + b x + c) = -1` (for nonzero discriminant), sums of χ(cubic), point counts as
  `p + 1 + ∑ χ(f(x))`, the Hasse/Weil bound. The quadratic sum follows from `jacobiSum_nontrivial_inv`
  (χ quadratic, so χ⁻¹ = χ) after completing the square and a change of variables, but that has to be written.

---------------------------------------------------------------------------------------------------

## 3. Hilbert symbols, quadratic forms, Chevalley–Warning

### 3.1 Hilbert / norm-residue symbols: MISSING
`grep -ri hilbert` finds only Hilbert spaces, Hilbert's Theorem 90
(`M/RepresentationTheory/Homological/GroupCohomology/Hilbert90.lean`, e.g. `groupCohomology.exists_div_of_norm_eq_one`)
and a comment in SelmerGroup.lean. There is no Hilbert symbol, no `(a,b)_p`, no product formula, no norm-residue symbol.

### 3.2 Selmer group K(S,n): EXISTS (basic definition only)
`M/RingTheory/DedekindDomain/SelmerGroup.lean` (with local notation `K / n := Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range`):
- `IsDedekindDomain.selmerGroup : Subgroup (K / n)` (161): classes with `ord_v ≡ 0 mod n` for every `v ∉ S`.
- `HeightOneSpectrum.valuationOfNeZeroMod (n) : (K / n) →* Multiplicative (ZMod n)` (133), `selmerGroup.valuation` (175),
  `valuation_ker_eq` (180), `fromUnit` (191), `fromUnit_ker` (199), `fromUnitLift_injective` (231).
- TODO in the file: exactness and finiteness. This is `ℚ(S,2)`, the group where the descent images live. It is not
  the elliptic-curve 2-Selmer group, and it is stated over `HeightOneSpectrum R`, not over primes p.

### 3.3 Quadratic forms: PARTIAL
- `QuadraticMap.Anisotropic` (`M/LinearAlgebra/QuadraticForm/Basic.lean:1056`), `not_anisotropic_iff_exists` (1059).
- Classification over ℝ (`QuadraticForm/Real.lean:59–87`, e.g. `equivalent_one_neg_one_weighted_sum_squared`) and over
  algebraically closed fields (`AlgClosed.lean:49,59`).
- MISSING: isotropy over finite fields (any form of rank ≥ 3 is isotropic), the number of zeros of a quadratic form over
  𝔽_q, and isotropy over ℚ_p (the Hilbert symbol criterion). There is no theory of conics (`grep -i conic` finds only
  convex cones and conical limits).

### 3.4 Chevalley–Warning: EXISTS
`M/FieldTheory/ChevalleyWarning.lean`, variables `{K σ ι : Type*} [Fintype K] [Field K] [Fintype σ] [DecidableEq σ]`
(52), `q = Fintype.card K`, then `[DecidableEq K] (p : ℕ) [CharP K p]` (103):
- `MvPolynomial.sum_eval_eq_zero (f : MvPolynomial σ K) (h : f.totalDegree < (q - 1) * Fintype.card σ) : ∑ x, eval x f = 0` (57)
- ```
  theorem char_dvd_card_solutions_of_sum_lt {s : Finset ι} {f : ι → MvPolynomial σ K}
      (h : (∑ i ∈ s, (f i).totalDegree) < Fintype.card σ) :
      p ∣ Fintype.card { x : σ → K // ∀ i ∈ s, eval x (f i) = 0 }        -- line 110
  ```
- `char_dvd_card_solutions_of_fintype_sum_lt` (168),
  `char_dvd_card_solutions {f : MvPolynomial σ K} (h : f.totalDegree < Fintype.card σ) : p ∣ Fintype.card { x : σ → K // eval x f = 0 }` (179),
  `char_dvd_card_solutions_of_add_lt` (191; two polynomials).
- Use: a ternary quadratic form over 𝔽_p (degree 2 < 3 variables) has a nontrivial zero, because the zero vector is
  one solution and the count is divisible by p. This gives local solubility of the quartic 2-coverings at good odd
  primes once a smooth point can be lifted with Hensel.

---------------------------------------------------------------------------------------------------

## 4. Weierstrass curves

### 4.1 Curves, invariants, ellipticity: EXISTS
`M/AlgebraicGeometry/EllipticCurve/Weierstrass.lean`: `structure WeierstrassCurve (R)` (76; fields a₁ a₂ a₃ a₄ a₆),
`b₂…b₈` (100–112), `c₄ c₆` (120,124), `Δ` (131), `map` (230), `baseChange [Algebra R A]` (235), notation `W⁄A` (239),
`map_Δ` (272), `twoTorsionPolynomial : Cubic R` (304), `eval_toPoly_twoTorsionPolynomial` (307),
`twoTorsionPolynomial_discr : … = 16 * W.Δ` (311),
`protected class IsElliptic : Prop where isUnit : IsUnit W.Δ` (366), `Δ'` (376), `j` (388),
`instance : (W.map f).IsElliptic` (455).

### 4.2 Affine model, equations, formulas: EXISTS
- `abbrev Affine` (`Affine/Basic.lean:74`), `toAffine` (78), `polynomial` (96), `Equation` (149), `equation_iff` (156),
  `Nonsingular` (211), `nonsingular_iff` (218),
  `equation_iff_nonsingular [Nontrivial R] [W.IsElliptic] {x y : R} : W.Equation x y ↔ W.Nonsingular x y` (249),
  `equation_iff_nonsingular_of_Δ_ne_zero` (243), `map_equation` (279), `map_nonsingular` (292),
  `baseChange_equation` (312), `baseChange_nonsingular (hf : Function.Injective f) (x y)` (323).
- `Affine/Formula.lean`: `negY` (120), `negY_negY` (123), `Y_eq_of_X_eq` (131), `nonsingular_neg` (146), `linePolynomial` (158),
  `slope [DecidableEq F] (x₁ x₂ y₁ y₂ : F)` (175), `slope_of_X_ne` (197), `slope_of_Y_ne` (191), `addPolynomial` (219),
  `addX` (245), `negAddY` (254), `addY` (262), `equation_add` (333), `nonsingular_add` (355), `addX_of_X_ne` (389),
  `addX_self_of_Y_ne` (444), `map_*` / `baseChange_*` versions (467–531).

### 4.3 Points and the group law: EXISTS
`Affine/Point.lean`, with variables `[CommRing R] … [Field F] {W' : Affine R} {W : Affine F}` (79–81):
- `inductive Point | zero | some (x y : R) (h : W'.Nonsingular x y)` (477, `deriving DecidableEq`), over any `CommRing`.
- `Point.mk {x y} (h : W'.Equation x y)` (545, needs `[Nontrivial R] [W'.IsElliptic]`),
  `pointEquiv : W'.Point ≃ WithZero {xy : R × R // W'.Equation xy.1 xy.2}` (579), `nonsingularPointEquiv` (518).
- `neg` (622, any CommRing), `neg_some` (637).
- `add` (658) and `AddCommGroup W.Point` (805) need **`[Field F] [DecidableEq F]`** (line 653). No `IsElliptic` is
  needed: associativity is proved through the ideal class group, using
  `toClass : W.Point →+ Additive (ClassGroup W.CoordinateRing)` (750), `toClass_injective` (795).
  Case lemmas: `add_some` (674), `add_of_Y_eq` (680), `add_self_of_Y_eq` (685), `add_of_Y_ne` (690), `add_self_of_Y_ne` (701),
  `add_of_X_ne` (710).
- 2-torsion: `isRoot_twoTorsionPolynomial_of_add_self` (722),
  `isRoot_twoTorsionPolynomial_iff (h2 : NeZero (2 : F)) (hΔ : W.Δ ≠ 0) (x : F) : W.twoTorsionPolynomial.toPoly.IsRoot x ↔ ∃ y, ∃ h : W.Nonsingular x y, some x y h + some x y h = 0` (734).
- Maps along field homs:
  `Point.map (f : F →ₐ[S] K) : (W'⁄F).Point →+ (W'⁄K).Point` (822; W' over a ring R, with `[Algebra R S] [Algebra S F] [IsScalarTower R S F]` etc., line 816),
  `map_some` (839), `map_map` (846), `map_injective` (849),
  `Point.baseChange (F K) [Algebra F K] [IsScalarTower R F K] : (W'⁄F).Point →+ (W'⁄K).Point` (858), `map_baseChange` (862).
  This is exactly E(ℚ) → E(ℚ_p) and E(ℚ) → E(ℝ) (both are injective).
- `xRep` (886), `xRep_eq_xRep_iff` (916), `finite_preimage_xRep` (955).
- Projective and Jacobian models with `toAffineAddEquiv` (`Projective/Point.lean:555`, AddCommGroup 572; Jacobian similar).

### 4.4 Descent and isogenies: MISSING in Mathlib (EXISTS in the repo, see 6)
No Kummer/descent map E(K)/2E(K) → (Kˣ/Kˣ²)², no isogenies (`grep -i isogeny` is empty), no `[n]` written via division
polynomials. `DivisionPolynomial/Basic.lean`/`Degree.lean` define `ψ₂, Ψ₂Sq, Ψ₃, preΨ', ΨSq, Φ, ψ, φ` (113ff.), with
`Ψ₂Sq_eq : W.Ψ₂Sq = W.twoTorsionPolynomial.toPoly` (132), but nothing links them to `n • P`.

### 4.5 Reduction: PARTIAL
`Reduction.lean` (`R` a DVR, `K` its fraction field): `class IsIntegral` (58), `integralModel` (62), `exists_isIntegral` (159),
`class IsMinimal` (275), `exists_isMinimal` (286), `minimal` (300),
`reduction (W) [IsMinimal R W] : WeierstrassCurve (ResidueField R)` (317), `class HasGoodReduction` (324),
`hasGoodReduction_iff_isElliptic_reduction` (327), multiplicative/additive/split classes (341–360), trichotomy (368).
There is no reduction map on points, no E₀/E₁ filtration, no formal group, and no "kernel of reduction is torsion-free
prime to p". (The repo has a hand-made version over ℤ[√2], see 6.4.)

### 4.6 Point counts over finite fields, Hasse: MISSING
- There is no `Finite`/`Fintype` instance for `W.Point` over a finite field (grep finds none). `pointEquiv` reduces the
  question to a subtype of `F × F`, which is how the repo does it (6.5).
- No Hasse bound (`grep -i hasse` finds only Hasse derivatives).
- `LFunction.lean`: `localPolynomial` (43) uses `Nat.card (W'.reduction R).toAffine.Point` only as a definition;
  `localPowerSeries` (53), `localEulerFactor` (57), `LFunction` (79). No theorems.
- `M/NumberTheory/Height/EllipticCurve.lean`: `Point.naiveHeight` (37), `approx_parallelogram_law` (80),
  `finite_naiveHeight_le` (116), `finite_torsion : Finite (AddCommGroup.torsion W.Point)` (123, needs Northcott).

---------------------------------------------------------------------------------------------------

## 5. Groups: |G/2G| = |G[2]| and related card formulas: EXISTS

`M/GroupTheory/Index.lean` (all `@[to_additive]`, so the `AddSubgroup.*` names exist too):
- `Subgroup.index_ker (f : G →* G') : f.ker.index = Nat.card f.range` (285)
- `Subgroup.card_mul_index : Nat.card H * H.index = Nat.card G` (293)
- `Subgroup.card_ker_mul_card_range (f : G →* G') : Nat.card f.ker * Nat.card f.range = Nat.card G` (298)
- `Subgroup.index_eq_card : H.index = Nat.card (G ⧸ H)` (356), `index_eq_card_div` (369)
- **`Subgroup.index_range {f : G →* G} [hf : f.ker.FiniteIndex] : f.range.index = Nat.card f.ker`** (902). With
  `f = nsmulAddMonoidHom 2` (the additive version of `powMonoidHom`, `M/Algebra/Group/Hom/Basic.lean:38`) and
  `AddSubgroup.index_range`, this is `[G : 2G] = #G[2]` for any group where the 2-torsion has finite index, in
  particular any finite G (instance `finiteIndex_of_finite`, 764; also `finiteIndex_ker` when the range is finite, 885).
- `QuotientGroup.quotientKerEquivRange : G ⧸ ker φ ≃* range φ` (`M/GroupTheory/QuotientGroup/Basic.lean:134`; additive
  version `QuotientAddGroup.quotientKerEquivRange`).
- `Subgroup.card_eq_card_quotient_mul_card_subgroup` (`M/GroupTheory/Coset/Card.lean:53`).
- `AddSubgroup.index_range_nsmul [Free ℤ M] [Module.Finite ℤ M] (n) : (nsmulAddMonoidHom n).range.index = n ^ finrank ℤ M`
  (`M/GroupTheory/IndexNSmul.lean:36`).
- `IsCyclic.card_powMonoidHom_range/ker` (`M/GroupTheory/SpecificGroups/Cyclic.lean:~729–750`).
- Descent theorem: `Group.fg_of_descent` (67), `CommGroup.fg_of_descent` (110),
  `CommGroup.fg_of_descent' (H₁ : (powMonoidHom 2).range.FiniteIndex) (H₂ : ∀ x, 0 ≤ h x) (H₃ : parallelogram ≤ C) [Northcott h] : Group.FG G`
  (147), `finite_torsion_of_descent'` (210), all in `M/GroupTheory/Descent.lean`, with `AddCommGroup.*` versions.
- The repo has `index_nsmul_range_congr`, `nsmul_range_prod`, `index_nsmul_range_pi_int` (`ZQ/Model/Descent/RankOne.lean:35–50`)
  for `[ℤⁿ × D : 2(ℤⁿ × D)]`.

---------------------------------------------------------------------------------------------------

## 6. The repo (ZInQKernel)

### 6.1 Curves and the group law
- Uses Mathlib's `WeierstrassCurve.Affine.Point` and its `AddCommGroup`; no separate group law is defined.
- `shortCurve (A : F) : WeierstrassCurve F` (y² = x³ + A x), `ZQ/Model/Field/ShortWeierstrass.lean:22`;
  `shortCurve_equation_iff` (35), `shortCurve_Δ = -64 * A^3` (39), `shortCurve_isElliptic [NeZero (2:F)] (hA : A ≠ 0)` (44),
  `shortCurve_negY = -y` (53), `two_nsmul_some_eq_zero_iff` (61),
  `shortCurve_two_nsmul_some_eq_zero_iff [NeZero (2 : F)] (h) : 2 • Point.some x y h = 0 ↔ y = 0` (74),
  scaling isomorphism `scaleEquiv (hu : u ≠ 0) (hB : B = u^4 * A)` (181), `scalePoint_add` (155).
- `genCurve` over `K0 = QuadraticAlgebra ℚ 2 0` (ℚ(√2)), with `d = genD = 75 - 53√2`
  (`ZQ/Hypotheses/MordellWeil.lean:28–42`); `MordellWeilE := AddGroup.FG genCurve.toAffine.Point`.
- Coordinate chord/tangent lemmas for E: `ZQ/Model/Generator/GroupLaw.lean`.

### 6.2 2-isogeny descent (over any field K, for y² = x³ + b x): EXISTS
`ZQ/Model/Descent/Kummer.lean`:
- `SqClass K := Kˣ ⧸ (powMonoidHom 2 : Kˣ →* Kˣ).range` (38), `SqClass.mk` (43), `sqc (x : K) : SqClass K`
  (59; `sqc 0 = 1`), `sqc_mul` (74), `sqc_eq_one_iff (hx : x ≠ 0) : sqc x = 1 ↔ IsSquare x` (115), `sqc_eq_sqc_iff` (135),
  `SqClass.mul_self` (80). `SqClass.lift` (`FirstImage.lean:28`).
- `kummer (b) : (shortCurve b).toAffine.Point → SqClass K`, `O ↦ 1`, `(0,y) ↦ sqc b`, `(x,y) ↦ sqc x` (192).
- `kummer_add (P Q) : kummer b (P + Q) = kummer b P * kummer b Q` (315), `kummerHom : … →+ Additive (SqClass K)` (357),
  `kummer_two_nsmul` (375), `kummer_neg` (209).
- `phi (hb' : b' = -4 * b)`, the 2-isogeny `(x,y) ↦ (y²/x², y(b - x²)/x²)` (400).
  **`phi` is not proved to be a homomorphism** (no `phi_add`).
- `kummer_eq_one_iff (Q : (shortCurve b').toAffine.Point) : kummer b' Q = 1 ↔ Q ∈ Set.range (phi hb')` (419; the image of φ is the kernel of the Kummer map).
- `rescale (hb'' : b'' = 16 * b) : (shortCurve b'').toAffine.Point ≃+ (shortCurve b).toAffine.Point` (501), `kummer_rescale` (520),
  `rescale_phi_phi : rescale _ (phi hb'' (phi hb' P)) = 2 • P` (541; λ ∘ φ̂ ∘ φ = [2]), `kummer_scaleEquiv` (593).
- For y² = x³ − d²x this is b = −d², b' = 4d². It is the 2-isogeny descent, not the full 2-descent: there is no pair map
  `(x, x − d)` into `(Kˣ/Kˣ²)²` and no 2-covering.

### 6.3 Descent over K₀ = ℚ(√2) (rank computation)
- `ZQ/Model/Descent/Index.lean`: `two_smul_range_eq_ker : (nsmulAddMonoidHom 2).range = (kummerHom (b := -genD^2)).ker` (70),
  `index_two_E : (nsmulAddMonoidHom 2).range.index = 8` (78, proved with `AddSubgroup.index_eq_card` and
  `QuotientAddGroup.quotientKerEquivRange`), `phiE_surjective` (42), `finiteIndex_two_E` (99).
- `FirstImage.lean`: `kummer_range_E : Set.range (kummer (-genD^2)) = descentGroup` (235), `card_kummer_range_E = 8` (259);
  the image is detected by `sqcInvariant : SqClass K0 →* Multiplicative (ZMod 2) × (SignType × SignType)` (64).
- `SecondImage.lean`: `kummer_E'_trivial` (103; the second image is trivial).
- `Factor.lean`: `eq_unit_mul_genD_pow_mul_sq` (85), `even_vp_or_of_curve` (150: on y² = x³ + Bx, v(x) is even or 2v(x) = v(B)),
  `descentGroup` (107), `sqc_mem_closure_of_even` (139).
- Valuations: `vp π : K0 → ℤ`, built from Mathlib's `IsDedekindDomain.HeightOneSpectrum.valuation`
  (`ZQ/Model/Field/Valuation.lean`); dyadic computations in `Field/Dyadic.lean`; units and square classes of ℤ[√2]ˣ in `Field/Units.lean`.
- **Mordell–Weil**: `mordellWeilE : MordellWeilE` (`ZQ/Model/Descent/MordellWeil.lean:24`) is
  `AddCommGroup.fg_of_descent' finiteIndex_two_E (naiveHeight ≥ 0) hC`, where `hC` comes from Mathlib's
  `approx_parallelogram_law` (`M/NumberTheory/Height/EllipticCurve.lean:80`) and Northcott comes from
  `Height/NumberField.lean`. The Mathlib theorem used is `AddCommGroup.fg_of_descent'` (`M/GroupTheory/Descent.lean:147`, additive form).
- `RankOne.lean`: `exists_generator_C/E` (106/202), `card_torsion_C/E = 4` (91/98). `Torsion.lean`: `mem_torsion_E_iff` (110).
  `OddIndex.lean`: `odd_free_index` (48).

### 6.4 Reduction mod a degree-one prime (hand-made, over K₀): EXISTS
- `ZQ/Model/Descent/Residue.lean`: `VGe π k x` (24), `res π ρ : K0 → ZMod p` (193), `res_add/mul/div` (220/231/271).
- `KernelReduction.lean`: formal-group style estimates (`kernel_add` 297, `tCoord` 368,
  `nsmul_ne_zero_of_not_vge` 374: the kernel of reduction has no torsion prime to p).
- `Reduction.lean`: `red` (63), `red_add` (421), `redHom : … →+ (shortCurve Ab).toAffine.Point` (452),
  `eq_zero_of_red_eq_zero` (463), `red_injOn_of_coprime` (495), `card_dvd_of_coprime` (509).
  These are specific to K₀/ℤ[√2] and to y² = x³ + Ax, but the proofs are generic in spirit.

### 6.5 Point counts over 𝔽_p: EXISTS (by `decide`)
`ZQ/Model/Descent/PointCounts.lean`: `card_point_shortCurve (p) [Fact p.Prime] (a : ZMod p) [(shortCurve a).IsElliptic] : Nat.card (shortCurve a).toAffine.Point = pointCount p a`
(50, through `pointEquiv`), `card_point_17 = 20` (71), `card_point_23 = 24` (75). `pointCount` is defined in `ZQ/Hypotheses/PrimePattern.lean:69`.

### 6.6 p-adic / Hensel use
- The repo does not use `ℚ_[p]`, `ℤ_[p]`, `hensels_lemma`, `HenselianRing`, Chevalley–Warning or `selmerGroup` anywhere.
- Elementary Hensel over ℤ, `ZQ/Progressions/RealChar/Hensel.lean`: `realChar_sq_lift_step_odd` (15),
  `realChar_exists_sq_mod_pow_odd` (39: a square mod odd p is a square mod every pⁿ),
  `realChar_exists_sq_mod_two_pow (hn : 8 ∣ n - 1) (k)` (53: n ≡ 1 mod 8 is a square mod every 2ᵏ).
  These are statements about integer congruences, not about squares in ℤ_[p].
- Legendre symbols are used in `ZQ/RouteK/Slots/{Dirichlet,Theta}.lean` and `ZQ/Progressions/...`.

### 6.7 The Selmer system and CR₃ (context for the planned work)
- `ZQ/RouteK/System/Selmer.lean`: `Unknowns` (24), `twoAdicRows` (60), `monsky` (85), `E1/E2/D` (89–97), `IsSol` (101), `sols` (108).
  This is the explicit 𝔽₂-linear system Σ(𝒞) written in Monsky's coordinates. `Config` is in `System/Config.lean:70`.
- `ZQ/Hypotheses/CertifiedRank.lean`: `def CertifiedRank : Prop` (the only hypothesis left unproved). Its docstring says
  "Proposition 0: Σ(𝒞_d) is Sel₂(C_d) written in coordinates". This identification is what the planned 2-descent would
  formalize. Proposition 0 itself is not in Lean.

---------------------------------------------------------------------------------------------------

## Summary of gaps (what has to be built for an explicit 2-Selmer group of y² = x³ − d²x over ℚ)

1. Squares in ℤ_[p]/ℚ_[p]: the unit criterion for odd p, the mod-8 criterion at p = 2, square classes of ℚ_p (4 or 8 of them),
   `IsSquare x ↔ even v(x) ∧ unit part is a square`. Building blocks that exist: `hensels_lemma`, `IsAdicComplete.henselianRing`,
   `unitCoeff_spec`, `toZMod`, `toZModPow`, `Padic.valuation_ratCast`.
2. The full 2-descent map `E(K) → (Kˣ/Kˣ²)²`, `P ↦ (x, x − d)` (or `(x + d, x − d)`) with the 2-torsion conventions, its
   homomorphism property and kernel `= 2E(K)`. The repo's `kummer` (2-isogeny) and `SqClass` are the natural base to
   extend, and the repo's `kummer_add` proof is a template.
3. 2-coverings (the quartic or intersection-of-quadrics curves `d₁u² − d₂v² = d`, …), and the equivalence
   "class (d₁,d₂) is in the image of E(K) ⟺ the covering has a K-point".
4. Local solubility at every place: ℝ (easy, `Real.isSquare_iff`), odd p ∤ 2d (Chevalley–Warning for the quadric
   plus Hensel, or χ-sums), odd p ∣ d, and p = 2 (finite case analysis mod 8/16 plus Hensel).
5. `ℚ(S,2)` with S = {∞, 2, p ∣ d}: Mathlib has `IsDedekindDomain.selmerGroup` but not its explicit description over ℚ
   (generated by −1, 2 and the p ∣ d). `Rat.isSquare_iff_even_factorization` is the main tool.
6. No Hilbert symbol, no isotropy of quadratic forms over 𝔽_q or ℚ_p, no conics, no χ-sum of a quadratic polynomial, no
   `Fintype (W.Point)` instance, no Hasse bound, no reduction on points over ℚ_p, no isogenies in Mathlib.
7. `[G : 2G] = #G[2]` for finite G exists (`AddSubgroup.index_range`), and so does the first isomorphism theorem.

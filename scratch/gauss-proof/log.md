# gauss-proof results log

- ZInQKernel/Contrib/GaussFE/HeckeFE.lean: verbatim copy of scratch/bp-hecke-fe/HeckeFE.lean,
  namespace BpHeckeFE renamed to ZInQ.Contrib.GaussFE (only change). VERIFIED: `lake build
  ZInQKernel.Contrib.GaussFE.HeckeFE` succeeds (22:15 PST), no errors.
- ZInQKernel/Contrib/GaussFE/Gauss.lean (imports Mathlib only). VERIFIED compiled (22:25 PST,
  `lake env lean` and `lake build ZInQKernel.Contrib.GaussFE.Gauss`, no errors, no sorry).
  `#print axioms ZInQ.Contrib.GaussFE.gauss_jacobi` = [propext, Classical.choice, Quot.sound].
  Statement: for prime p ≡ 1 (mod 4), ∃ A B : ℤ, A²+B² = p ∧ (A+1) % 2 = 0 ∧ (B−A−1) % 4 = 0 ∧
  #{(x,y) ∈ 𝔽_p² : y² = x³ − x} = p + 2A.
  Pieces: `exists_quartic` (χ : MulChar (ZMod p) ℤ[i] of order 4, Mathlib exists_mulChar_orderOf),
  `quadraticChar_eq_chi_sq` (χ² = quadratic character, via a generator of (ZMod p)ˣ),
  `sum_sq_comp` (Σ_x F(x²) = Σ_t (1+χ(t)²)F(t)), `sum_chi_sq_cubic` (Σ_x χ(x³−x)² = J(χ,χ²) + J(χ³,χ²)),
  `jacobi_conj` (J(χ³,χ²) = conj J), `jacobi_mul_star` (J·conj J = p, Mathlib
  jacobiSum_mul_jacobiSum_inv through ℤ[i] ↪ ℂ), `chi_neg_one_mul_chi_two_sq` (χ(−1)χ(2)² = 1),
  `two_add_two_i_dvd_jacobi_add_one` ((2+2i) ∣ J + 1; involution t ↦ t⁻¹ in ℤ[i]/(2+2i)),
  `card_cubic_eq` (count = p + Σ quadraticChar(x³ − x)).
- ZInQKernel/Contrib/GaussFE/FunctionalEquation5.lean. VERIFIED compiled (22:35 PST; `lake env lean`
  and `lake build ZInQKernel.Contrib.GaussFE.FunctionalEquation5`, no errors, no sorry).
  `psiPair`, `psiPair_neg`, `psiPair_conj`, `unitOf_primary`, `psiPair_primary`,
  `gaussPointCount : GaussPointCount` (bp-hecke-fe's Prop, definition unchanged in HeckeFE.lean),
  `literature_hecke_fe : HeckeContinuation5 ∧ ZInQ.Literature.FunctionalEquation5`,
  `theorem ZInQ.Contrib.functionalEquation5 : ZInQ.Literature.FunctionalEquation5`.
  scratch/gauss-proof/axioms.lean → out_axioms.txt: all three depend on
  [propext, Classical.choice, Quot.sound]; `example : ZInQ.Literature.FunctionalEquation5 :=
  ZInQ.Contrib.functionalEquation5` elaborates (type is exactly the hypothesis).
- Built ZInQKernel.MainLiterature (lake build, 5 min, success) for the headline file.
- ZInQKernel/Contrib/GaussFE/Headline.lean. VERIFIED compiled (`lake env lean`, `lake build`):
  `certifiedRankTYZClRk_of_readingA_grossZagier : TYZThm35ReadingA → GrossZagier →
   RouteK.Rank.CertifiedRankTYZClRk`,
  `frozenTarget_of_sixContactMin_tyzThm35ReadingA_grossZagier : SixContactMin → TYZThm35ReadingA →
   GrossZagier → FrozenTarget`,
  `frozenTarget_of_sixContactMin_tyzInputs_grossZagier : SixContactMin → PropN.TYZInputs →
   GrossZagier → FrozenTarget`.
  out_axioms_headline.txt: all three [propext, Classical.choice, Quot.sound].

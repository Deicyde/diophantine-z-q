# The five headline statements

For each of [M]'s Theorem 1.1, Lemma 1.2, Theorem 4.1, Theorem 5.2 and Theorem 5.3: what each
repository states, whether it proves or assumes it, and how its statement differs from [M]'s.
[F] is `Deicyde/diophantine-z-q` at `f81ade8b`; [N] is `nasqret/z-in-q-lean` at `de33a32d`, with
its kernel dependency `elliotglazer/diophantine-z-q` at `2358394` ("ndep"). Statuses and standing
are those of `docs/taxonomy.md`; the verdicts are in `data/mapping.json`. No repository was built:
everything below is read from the source. Two skeptics checked every claim here against the
sources; their corrections, and those of a later independent review, are applied.

## Theorem 1.1 (a polynomial definition of ℤ, with bounds)

- **[F]: `exact`, conditional.** `ZInQ.FrozenTarget` states the theorem: one integer polynomial
  in 292,890,231,905 variables, total degree below `2↑↑7`, every coefficient below `2↑↑8` in
  absolute value, whose rational zeros projected to the first variable are exactly ℤ. The
  headline `ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_poleCompleteness`
  proves it from `ZInQ.SixContactMin` and `ZInQ.PoleCompleteness`. `ZInQ.OneProof.frozenTarget`
  proves it from seven Lean hypotheses: three H bundles (one of them an empty structure) and hRC,
  hCT, hB, hK, whose fields are the 33 open rows of `docs/one-proof/OPEN.md`. The unconditional copy
  `ZInQ.exists_bounded_integer_polynomial_defining_integers` (`lean/Frozen/`) is `sorry`.
- **[N]: `exact`, conditional.** `ZOverQ.Bounded.bounded_from_height_tian_gross_zagier` concludes
  ndep's `ZInQ.FrozenTarget`, the same statement, from ndep's `ZInQ.SixContactMin`, [N]'s
  `PublishedTian47` and [N]'s `SimpleZeroRank` (an abbreviation of ndep's `ZInQ.Literature.GrossZagier`).
  Its route does not pass through [M]'s Theorem 5.2: the dependency replaces the pole input by a
  rank hypothesis on other curves. [N]'s second headline,
  `ZOverQ.Qualitative.PicardConclusion.integer_polynomial_of_arithmetic_geometry`, proves only
  `ZOverQ.Qualitative.IntegerPolynomial` (some polynomial, no variable count, no bounds) from twelve
  hypotheses. [N] also proves `ZInQ.FrozenTarget` from other sets of unproved Props, outside its
  headlines: `ZOverQ.Bounded.bounded_from_height_and_literature`,
  `ZInQBlueprint.OriginalRank.frozen_of_height_and_five_rank_inputs`, `…_four_rank_inputs`,
  `…frozen_of_height_printed_modular_simple_zero` and
  `ZInQBlueprint.PublicRankJoin.frozen_of_geometry_and_class_rank`.

## Lemma 1.2 (assembly: the six inputs make P_* satisfy Theorem 1.1)

- **[F]: `close`, conditional.** `ZInQ.Assembly.Pstar_spec` and `ZInQ.Assembly.assembly` prove that
  the specified polynomial satisfies Theorem 1.1 from `SixContactMin`, `PoleCompleteness`, the slope
  representation `ZInQ.Mult.SlopeRepresentation` and the halting-circuit node bound
  `ZInQ.Compiler.NodeCheck.HaltingAddMulBound`. The node bound is a proved theorem
  (`haltingAddMulBound`) that the main theorems supply; the rest of [M]'s inputs G, M, C and B are
  proved inside instead of assumed. The slope representation, a consequence of [M]'s prime pattern,
  is a hypothesis that [M]'s list of inputs does not name. `ZInQ.Assembly.assembly_AP` takes its
  route-AP form, which the headline derives from proved density results.
- **[N]: `differs`, conditional.** [N]'s assembly theorems
  (`ZOverQ.Qualitative.integer_polynomial_of_height_and_rank`, `bounded_from_height_tian_gross_zagier`)
  take hypotheses outside [M]'s list: `UniformHeight C` for some C, and `CertifiedRankTYZClRk` or
  `PublishedTian47` with `SimpleZeroRank` in place of PC. They give a polynomial defining ℤ, but
  none states that [M]'s specified P_* satisfies Theorem 1.1, so neither statement implies the
  other. ndep's `ZInQ.Assembly.Pstar_spec` concerns ndep's own specified polynomial, built on the
  curves `y² = x(x − ℓ)(x + ℓ)`, from `HaltingAddMulBound`, `SixContactMin`, `PoleCompleteness`
  and `SlopeRepresentation`; no [N] declaration names it.

## Theorem 4.1 (the six-contact height estimate)

- **[F]: `exact`, stated and neither proved nor assumed.** `ZInQ.SixContactEstimate` states the
  theorem for every admissible S and R with [M]'s constant H₆(S; R). No theorem proves it and no
  headline takes it. The headline `..._of_sixContactMin_poleCompleteness` assumes its instance
  `ZInQ.SixContactMin` (S = S_mul, R = D), which `ZInQ.sixContactMin_of_sixContactEstimate` derives
  from the estimate. `ZInQ.OneProof.frozenTarget` instead obtains that instance from the open bundles
  of OPEN.md through `HDec.HSyn.sixContactMin_of_open85`.
- **[N]: `stronger`, conditional.** `ZInQBlueprint.PublicText.HeightInstance` fixes R = D and puts no
  condition on S: not primality, not the primes at most 324, not a range. For admissible S whose
  primes are all at most D it is Theorem 4.1 at (S, D). For S with a prime above D it claims the
  smaller constant H₆(S; D), which [M] does not assert. For general S, [N] proves it only from the
  unproved Prop `ZInQBlueprint.PublicText.GeometricComparisons` (`height_of_comparisons`). At
  S = S_mul, where it is ndep's `ZInQ.SixContactMin`, [N] also proves it from other unproved Props
  (for example `sixContactMin_of_twistBound`, `sixContactMin_of_surfaces`). [N]'s bounded headline
  assumes ndep's `ZInQ.SixContactMin`; its qualitative headline assumes no form of Theorem 4.1.

## Theorem 5.2 (pole completeness, PC)

- **[F]: `exact`, assumed by the headline and proved only conditionally.** `ZInQ.PoleCompleteness`
  states the theorem for [M]'s pole polynomial (curves `y² = x(x − ℓ)(x + 3ℓ)`), with [M]'s
  conditions on B. The headline takes it as a hypothesis.
  `ZInQ.Manuscript.PoleS12.poleCompleteness_of_restrictedConverseGenuine_casselsTatePairing` proves
  it from Theorem 5.3 (`RestrictedConverseGenuine`), the Cassels–Tate pairing on the curves E_ℓ,
  BCDT's Theorem A, and a consequence of Kolyvagin's Theorem 1 (the case r = 1 for modular curves),
  all four assumed. Other routes prove it from other unproved Props:
  `ZInQ.Manuscript.PoleRC.poleCompleteness_of_crm` from `CRM` (its second hypothesis is proved,
  `Contrib/OneProof/PoleCompletenessFromRCGenuine.lean:49`), and
  `ZInQ.Manuscript.PoleS12.poleCompleteness_of_restrictedConverseGenuine` from Theorem 5.3 with
  `Lemma54`, `BCDTThmA`, `KolyvaginThm1` and `MordellWeil`.
- **[N]: `exact`, stated and neither proved nor assumed.** `ManuscriptV15.Arithmetic.PoleCompleteness`
  states the theorem for [M]'s pole polynomial. No [N] theorem proves or assumes it. What [N] uses
  is ndep's `ZInQ.PoleCompleteness`, the same shape for a different pole polynomial (curves
  `y² = x(x − ℓ)(x + ℓ)`), which [N]'s `ZOverQ.Qualitative.pole_of_class_sum` proves from a rank
  hypothesis.

## Theorem 5.3 (restricted converse, RC)

- **[F]: `exact`, assumed.** `ZInQ.Manuscript.SelmerTwoPower.RestrictedConverseGenuine` states the
  theorem for E_ℓ: y² = x(x − ℓ)(x + 3ℓ), ℓ positive squarefree with ℓ ≡ 11 (mod 12), with the
  ℤ₂-corank of the 2-primary Selmer group and the analytic order at s = 1. It is a hypothesis of
  `ZInQ.OneProof.frozenTarget` (row hRC of OPEN.md) and is not proved. Of Sections 7–9 and
  Appendices E–G, where [M] proves it, [F] states only the display (RC) (this theorem again) and
  three displays of Appendix E ((K5)–(K7)).
- **[N]: `close`, stated and neither proved nor assumed.** `ManuscriptV15.Arithmetic.RestrictedConverse`
  has [M]'s curves and range of ℓ, but takes the Selmer corank and the order at s = 1 as arbitrary
  function arguments; its own docstring calls it a typed interface awaiting their identification
  with the genuine objects. No [N] theorem uses it.

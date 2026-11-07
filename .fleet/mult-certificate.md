# mult-certificate: report

All leaves are formalized in `ZInQKernel/Multiplication/Certificate/` (root module
`ZInQKernel/Multiplication/Certificate.lean`, imported from `ZInQKernel.lean`), namespace
`ZInQ.Mult`. There is no `sorry`, `axiom` or `native_decide`. `#print axioms` on the main
theorems shows only `propext`, `Classical.choice` and `Quot.sound`. `lake build ZInQKernel`
succeeds.

## Leaves

| Article | Lean name | Status |
| --- | --- | --- |
| multiplication/abscissa-parity.md | `ZInQ.Mult.abscissa_val_even` (Parity.lean) | proved |
| multiplication/pole-obstruction.md | `ZInQ.Mult.pole_obstruction` (Parity.lean) | proved |
| certificate/constants.md | `S_ht`, `catalogue`, `S_b`, `S_mul`, `Bp`, `Cp`, `Dp`, `Ep`, `contactPoly`, `IsOddContactPrime`, `prec` (Constants.lean); `M_S` is the hypothesis file's `contactSupport` | done (definitions) |
| certificate/constants-properties.md | `one_le_M0`, `four_le_cstar`, `one_le_ell`, `S_mul_admissible`, `Aht_eq_heightH6`, `sixContact_at_Smul`, `two_mul_ten_pow_thirteen_le_Aht`, `four_lt_T`, `prime_of_mem_catalogue`, `catalogue_injective`, `Hcat_squarefree`, `padicValNat_ell`, `not_mem_S_mul` (ConstantsProperties.lean) | proved (items 1 and 5 under `M₀ ≥ 1`, see below) |
| certificate/clearing-arithmetic.md | `clearing_arithmetic`, `clearing_identities` (ClearingArithmetic.lean) | proved (`decide`) |
| certificate/twelve-tests.md | `invX`, `zOf`, `Lam`, `testValues`, `testValues_eq` (Tests.lean) | done (definitions) |
| certificate/slope-predicate.md | `SlopePred`, with `slopeR0`, `slopeA`, `slopeR`, `normTests`, `groupW`, `traceTheta`, `certShifts` (SlopePredicate.lean) | done (definitions) |
| certificate/local-templates.md | `rawZ_rel_iff_of`, `rawZ_not_rel`, `rawInverseX_rel_iff_of`, `rawInverseX_not_rel`, `log25_rel_iff`, `rawZ_rel_iota`, `rawInverseX_rel_iota` (LocalTemplates.lean) | proved |
| certificate/test-group-semantics.md | `testGroup_rel_iff`, `testGroup_rel_iff_codes` (TestGroup.lean) | proved |
| certificate/slope-semantics.md | `slope_rel_iff` (Slope.lean) | proved |
| certificate/height-certificate-semantics.md | `heightCertificate_rel_iff`, with `HeightCert`, `nineQ` (HeightCertificate.lean) | proved |
| certificate/guard-true-triples.md | `guard_true_triple`, `guard_false_triple`, `guard_rel_iff`, `guardPoly_zero_set` (Guard.lean) | proved, under the hypothesis that the guard constructor is `guardPoly` |
| certificate/multiply-unfolding.md | `multiply_rel_iff_unguarded`, `multiply_rel_iff`, `multiply_rel_iff_cert` (Multiply.lean) | proved, assuming fixed-scalar semantics (`hS`) |

## How the statements differ from the articles

- **constants.** `S_mul := S_ht ∪ 𝓗 ∪ c_*.primeFactors` (Mathlib's `primeFactors 0 = ∅`).
  `S_ht` is the precision chapter's `heightPrimes`. `catalogue` is
  `Syntax.catalogueFinset catalogueModulus 22 324`, with `coe_catalogue : ↑catalogue = catalogueSet`.
  `catalogue`, `S_b` and `S_mul` are `@[irreducible]`: elaborating a term `p ∈ catalogue`
  otherwise unfolds it down to `range (4·324#)`. Use `mem_catalogue`, `catalogue_eq`, `mem_S_b`
  and `mem_S_mul` instead. `B_p` is defined for every `p` (`4` on `S_ht`, else `1`).
  `prec`, `testValues` and the test groups are indexed from `0`.
- **constants-properties.**
  - Item 1 ($M_0\ge1$) depends on the size chapter's successful formal multiple. `one_le_M0`
    therefore takes `∃ m, 1 ≤ m ∧ Syntax.FormalCondition Syntax.Ns m` as a hypothesis (what
    `Size.exists_formal_multiple` should provide). `four_le_cstar` and `not_mem_S_mul` take
    `1 ≤ Syntax.M0`. Item 5 genuinely needs it: if $M_0=0$ then $c_*=0$ and every prime divides
    $c_*$.
  - Item 2 needs no hypothesis.
  - As requested, the height constants are bridged through their equation lemmas only:
    `D_eq_heightD`, `E0_eq_heightE0`, `Bcm_eq_heightBcm`, `Ccm_eq_heightCcm`, `heightQ_R`,
    `Aht_eq_heightH6 : (Syntax.Aht : ℝ) = heightH6 (Syntax.R : ℝ)` and
    `sixContact_at_Smul : ratHeight u ≤ Aht · M_{S_mul}(u)²⁴`.
- **local-templates.** "Q = O or y(Q) ≠ 0" is written `∀ x y h, Q = .some x y h → y ≠ 0`.
  Both-branch forms (`rawZ_rel_iff`, `rawInverseX_rel_iff`) are added. The ι(n) forms need no
  generator certificate: `log25_z_ne_zero` (torsion theorem) gives x, y ≠ 0.
- **test-group-semantics.** `testGroup_rel_iff` is stated for any parameter vector whose first
  20 coordinates are ι(c₀), …, ι(c₃); this is the form the slope proof uses. The article's form
  is `testGroup_rel_iff_codes` with `testGroupVec c D`. No Mordell–Weil hypothesis is needed.
- **slope-semantics.** Stated for any vector `a` with `a 0 = t`, `a 1 = ℓ` and the codes
  ι(c_i) at `2 + (5i + k)`.
- **height-certificate-semantics.** Stated for any vector with `a 15 = ℓ` and the codes at
  `16 + (5i + k)`. The article's item 2 is `HeightCert`: `b i * (Y i) 1 = A i 0`. Since
  `(ι(n))₁, (ι(n))₂` are the coordinates of `x([n]P₀)` (zero for n = 0), this is the article's
  `b_i x_{ij} = a_{ij}`. Also added: `heightTemplate_rel_members`, which reads the membership
  conjuncts without any hypothesis on the shift points (the unfolding needs this).
- **guard-true-triples.** The template is `guardTemplate I T` for a constructor record `I`,
  which is not yet instantiated anywhere. The statements therefore assume
  `hI : I.guard T = Syntax.guardPoly T`. With that assumption, the zero-set hypothesis of the
  guard semantics (`syntax/templates/guard-semantics.md`) is discharged (`guardPoly_zero_set`,
  `guard_rel_iff`).
- **multiply-unfolding.** The fixed-scalar semantics (`syntax/fixed-scalar-semantics.md`) is not
  formalized, so it enters as
  `hS : ∀ m r, (scalarTemplate I cs).Rel (Fin.append (iota m) r) ↔ r = iota (cs * m)`.
  The article's "$c_*\ge1$" is inside `hS`. The article form is `multiply_rel_iff_unguarded`;
  its height-certificate argument is `heightVec P Q R ℓ ![ι(cs), ι(cs n₁), ι(cs n₂), ι(cs n₃)]`.
  `multiply_rel_iff` unfolds the certificate into `HeightCert`. `multiply_rel_iff_cert`
  specializes to `cs = ↑Syntax.cstar`, `ℓ = ↑Syntax.ell` with `certShifts n`.

## Lemmas added beyond the leaves

- Parity.lean: `not_dvd_2730_of_not_mem_poleS0`, `poleSystem_of_polePoly_eq_zero`.
- ClearingArithmetic.lean: `padicValNat_two_twelve`, `padicValNat_three_twelve`,
  `padicValNat_twelve_of_five_le`, `padicValNat_twelve_le_two`.
- Constants.lean: `contactPoly_eq_prod`, `contactPoly_eq_zero_iff`,
  `prime_dvd_contactSupport_iff'`.
- ConstantsProperties.lean: `padicValNat_prod_primes`, `Ps_eq_prod`, `Hcat_eq_prod`,
  `padicValNat_Ps`, `padicValNat_Hcat`, `padicValNat_ell_formula`, `le_R_of_mem_S_mul`.
- SlopePredicate.lean: `traceTheta_eq`, `slopeR0_ne_zero`, `SlopePred.poleInput_ne_zero`.
- LiftLemmas.lean: generic readers for `Formula.Lift`: `lift_and_append`, `lift_feq`,
  `lift_nzFormula`, `lift_fin`, `ev_comp_*`, `pr`/`pt`/`prv`, `member_rawAdd_iff`,
  `iota_zero_coord_eq_zero_iff`, `negCode_iota`.
- TestGroup.lean: `lift_root(_iota)`, `lift_local(_iota/_pt)`, `Lam_ne_zero` and the explicit
  witnesses `tgY`.
- Slope.lean: `val_slopeW`, `lift_slopeGroup`, `normPairs_eq`, `normTests_spec`,
  `C_eq_ratCast` and the witnesses `slY`.
- HeightCertificate.lean: `height_slope_call`, `height_member_call` and the witnesses `hcY`.
- Multiply.lean: `heightVec` with `heightVec_ell/_input/_shift`, `ev_genPoint` and the
  witnesses `mulY`.

## Problems met (Lean pitfalls)

- `pow_ne_zero _ (h : Ps ≠ 0)` produces `Ps ^ n` through a different `Monoid` instance path.
  The kernel then evaluates `Ps` and times out. Facts about powers of the constants must be
  stated for variables first (`padicValNat_ell_formula`, `rpow_mul_self_natCast`,
  `cast_aht_formula`).
- `Formula.lift_call` cannot be used by `simp`, or by `rw` with a metavariable parameter list:
  the parameters have type `Fin τ.params → Poly`. Pass the parameter list explicitly. Move
  between `fun k => ev y (g k)` and a value vector with `iff_of_eq (congrArg τ.Rel e)`, not `rw`.
- Variables introduced with `set` can block defeq checks once a `by` proof is still pending
  (`P ⟨0, ?m⟩`). Introduce witnesses with `obtain ⟨y, hy⟩ : ∃ y, y = …` and index lemmas by
  `j : Fin n`.
- A `by` block inside an anonymous constructor must not wrap onto a less-indented line.

## Suggestions for the next agent

- Discharge `hS` by proving `syntax/fixed-scalar-semantics.md` for the concrete constructor
  record. Discharge `hI` by instantiating `Constructors` with `guard := Syntax.guardPoly`.
- Discharge `one_le_M0`'s hypothesis with the size chapter's `exists_formal_multiple`
  (`N_s ≥ 1` is `Syntax.Ns_pos`).
- The soundness and completeness tasks should use `multiply_rel_iff_cert`; they already use
  `SlopePred`, `certShifts`, `sixContact_at_Smul`, `not_mem_S_mul` and `pole_obstruction`.

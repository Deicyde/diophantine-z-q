# Residual non-vacuity verification


## Scope after independent review (2026-11-18)

This is a **degenerate-case** non-vacuity witness: full local conditions, S' = S, no derivative labels. At this instance the following inputs hold vacuously or degenerately: `hUm` and `hLm` (only as `0 ≤ _`, because the local parts of the model are zero); `hD`, `hDodd`, `hcondD` and `ψ`/`hψ` (quantified over empty sets); the premise of `hfull` never fires (its conclusion is proved separately). The change of condition is the identity, the quotient is zero, and the transfer is not exercised (`L = P₀`; the Nekovář input is used only with S' = S), so `genericRank = rankTot` for every witness. Genuinely witnessed: `eG`/`eGact` in degrees 0–2, `pP`, `L`/`hLmin`/`pL`, the bounds and finiteness. The witness must not be cited for the old-Kummer or active-support cases.

The bounds say `6 ≤ h⁰ + h¹ + h² ≤ 238` for the continuous cohomology of G_{Q(i),S} with coefficients F₂²: h⁰ = 2 holds unconditionally, h¹ ≥ 4 uses Milne, ADT I.5.1, and 238 = 56·3 + 70 is the consumers' general constant (the classical value is 22, not formalized here). Of the printed Milne inputs, only I.4.10 and I.5.1 carry an unverified-locator flag; the I.2.8 and I.2.3 statements record checked locators. The checking file cited below (`Audit.lean`) is not shipped.

## Result and scope

Both RC53 residual-count constructors compile on one genuine nonzero
full-condition instance, conditional on their existing printed propositions.
Their generic model rank is between 6 and 238.

The instance is E₁₁: y² = x(x − 11)(x + 33), over K = Q(i), at coefficient
index j = 0, with the trivial character into A₁ units. The actual residual
module is F₂ tensor over A₁ of the actual M₁. It has four elements, dimension
two, and the genuine trivial Galois action. The same integral equation is
used at every finite place, and its local generic fiber is the base change
of the global curve. Every local curve has exactly four rational points
killed by 2.

The support parameter is N = 66; the moving prime is 5; there are no derivative
labels. The charged rational primes are {2,3,5,11}. S₀ = Sloc = S = S', the
finite places above this set. The set of counted degrees is all of {0,1,2},
not an empty set or a singleton chosen to hide other terms.

The full local condition is the actual continuous local cochain complex with
the identity condition map. Its local identity cone is acyclic. The residual
diagram therefore keeps genuine global cohomology, with zero differential,
after cancellation of the two local pieces. Its degree-zero rank is two,
and the existing global Euler characteristic forces degree-one rank at least
four. An actual map from a complex's field-valued cohomology is proved to be
a quasi-isomorphism. K-projective lifting along the genuine full-condition
projection produces pP, and the genuine support map produces pL. These are
maps into the genuine complexes, not only equalities of dimensions.

## Verification performed

- The supplied base revision is 6ea158a404343c90a445c129cd0d1f3a0d4b8ddc.
- Single-file compilation started only after the supplied prerequisite log
  reported successful completion of 10643 jobs.
- The final witness and the standalone audit both compiled successfully,
  without warnings or errors.
- Compilation used six Lean worker threads, CPU affinity 64–79, and niceness 10.
- The only heartbeat bound introduced is 600000.
- The source guard found no placeholders, extra axioms, prohibited evaluation
  commands, compiler-backed decision procedures, or new parsing declarations.
- The public-text guard found no private working locations or private execution
  identifiers in the source, inventory, or audit output.
- The audit replays exactly the final proof source before adding its checks.
  A byte comparison of that source prefix passed.
- All 62 theorems, including the 49 private helpers, have their types and axiom
  dependencies printed. Seven key definitions are also audited: 69 axiom
  reports total. Every report uses a subset of propext, Classical.choice and
  Quot.sound. Every public theorem uses exactly those three standard axioms.
- No existing source, dependency pin, branch, or commit was changed. No
  prerequisite module was built, no repository operation was performed, and
  no human was contacted.
- The unavailable compiled NatHomology helper was not built. Its needed
  zero-degree and all-degree comparisons were proved in the new source.

The proof source is in Witness.lean. Audit.lean is a standalone replay;
Axioms.txt is its complete, untruncated output. Hypotheses.md lists every
input of the two target constructors in plain mathematics.

## The target declarations

- ZInQ.Contrib.CloudB3RC53.Mattuck.residualRankCounts_genuine
- ZInQ.Contrib.CloudB3RC53.GenuineInst.residualRankCounts_actual

## Exactly which inputs are witnessed

- eG and eGact: genuine global continuous cohomology, respectively with F₂²
  and with the actual residual module; both identifications cover degrees 0,1,2.
- hUm and hLm: the two local model pieces have zero remaining rank after the
  genuine full-condition identity-cone cancellation. Both zero bounds are
  bounded by the corresponding genuine local dimension sums, at the same support.
- pP: an actual quasi-isomorphism from the bounded residual cone to the genuine
  smaller-support full-condition Selmer complex, obtained by K-projective lifting.
- L, hLmin and pL: L is that finite model, supported in degrees 0,1,2, with zero
  differential; pL is an actual quasi-isomorphism into the genuine larger-support
  complex, obtained by composition with the supplied support comparison.
- All model terms are finite-dimensional. The supports agree. The actual
  coefficient hypotheses, the local ellipticity and rational torsion, the
  quadratic-radicand data, the complex place, the finite Nekovář setting, and
  the exact change-of-condition sequence are supplied as well.
- hW is genuinely true here: the change-of-condition map is the identity and
  its quotient is the zero complex.

No residual-model hypothesis remains un-witnessed for this chosen full-condition
case once the existing printed arguments are supplied.

## What is not established

This is interface non-vacuity, not the manuscript's complete intended instance.

1. K = Q(i) satisfies the target types but is explicitly excluded from the
   manuscript's final-companion selection. No analytic companion is certified.
2. N = 66 is a support parameter. It is not asserted to equal the conductor
   of E₁₁, and no conductor equality is proved.
3. Full local conditions are used, not old-Kummer conditions. The actual local
   torsion prerequisite is proved, but pP, the finite model and pL for the
   old-Kummer Selmer complex are not constructed by this contribution. Their
   existence does not follow from the identity-cone cancellation used here.
4. There are no new active places. A nonempty active-support case still needs
   the genuine local factorizations and the quotient acyclicity hW after the
   stated limit and inversion of t. The plain F₂ full/unramified comparison
   does not acquire that acyclicity just because the residual action is trivial.
5. The existing printed propositions remain explicit assumptions, not new axioms
   and not theorems proved here. The Milne source-verification flags are not cleared.

The printed arguments are the manuscript-cited Milne ADT, second edition (2006),
I.4.10(c), pages 56–57; I.5.1, page 67; I.2.8, page 31; I.Corollary 2.3,
page 28; and Nekovář, Selmer complexes, Astérisque 310 (2006), 7.8.8(ii),
pages 186–187. These locators are supplied by the RC53 interfaces and their
counting statements; no independent scan verification is claimed.

## Public theorem statements

The common namespace is ZInQ.Contrib.RC53Assist.ResidualWitness. The notation
and open namespaces are exactly those in the proof source. The axiom output
for each theorem below is [propext, Classical.choice, Quot.sound]. The types
and axiom reports for every private helper are preserved in Axioms.txt.

```lean
homologyModelTo_quasiIso {k : Type} [Field k]
    (C : CochainComplex (ModuleCat.{0} k) ℤ) :
    QuasiIso (homologyModelTo C)

eleven_admissible :
    0 < (11 : ℕ) ∧ Squarefree (11 : ℕ) ∧ 11 % 12 = 11 ∧
      ∀ ℓ : ℕ, ℓ % 12 = 11 → 11 ≤ ℓ

smallE_residual_hypotheses
    (S : Set (HeightOneSpectrum (𝓞 SmallK))) :
    FullTorsion SmallK S SmallE (2 ^ (0 + 1)) ∧
      FullTorsion SmallK S SmallE (2 ^ 0) ∧
      FullTorsion SmallK S SmallE 2 ∧
      ∀ (σ : GKS SmallK S)
        (P : TorsS SmallK S SmallE ((2 : ℕ) : ℤ)), σ • P = P

smallM_facts :
    Nat.card SmallM = 4 ∧ Module.finrank (ZMod 2) SmallM = 2 ∧
      ∀ (σ : GKS SmallK SmallS) (x : SmallM), σ • x = x

smallCurve_discriminant (R : Type*) [CommRing R] :
    (smallCurve R).Δ = 2304 * 11 ^ 6

local_models_are_baseChanges
    (w : HeightOneSpectrum (𝓞 SmallK)) :
    (smallLocalModels w).baseChange (w.adicCompletion SmallK) =
      SmallE.baseChange (w.adicCompletion SmallK)

smallCurve_two_torsion (F : Type*) [Field F] [CharZero F] :
    Nat.card (Submodule.torsionBy ℤ (smallCurve F).toAffine.Point 2) = 4

local_models_have_full_two_torsion
    (w : HeightOneSpectrum (𝓞 SmallK)) :
    Nat.card (Submodule.torsionBy ℤ
      ((smallLocalModels w).baseChange (w.adicCompletion SmallK)).toAffine.Point 2) = 4

jointWitness_nonempty
    (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex)
    (h788 : NekovarProp788ii SmallK) :
    Nonempty JointWitness

smallSupport_facts :
    Nat.Prime 5 ∧ ¬ 5 ∣ 2304 * 11 ^ 6 ∧
      chargedPrimes 66 5 ∅ = {2, 3, 5, 11}

residualRankCounts_genuine_nonvacuous
    (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex)
    (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial)
    (h788 : NekovarProp788ii SmallK) :
    ∃ J : JointWitness,
      6 ≤ (genuineCounts h410 h51 h28 h23 h788 J).genericRank ∧
      (genuineCounts h410 h51 h28 h23 h788 J).genericRank ≤ 238

residualRankCounts_actual_nonvacuous
    (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex)
    (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial)
    (h788 : NekovarProp788ii SmallK) :
    ∃ J : JointWitness,
      6 ≤ (actualCounts h410 h51 h28 h23 h788 J).genericRank ∧
      (actualCounts h410 h51 h28 h23 h788 J).genericRank ≤ 238

smallBound :
    residualBoundConstant (2 * 66).primeFactors.card 0
      (∅ : Finset ℕ).card = 238
```

## File identities

- Witness.lean: 42001 bytes; SHA256 6668faf062429a0c1876777bb7e86f33b7c9616bb7b0df113d62e908d7922a7c.
- Audit.lean: 45788 bytes; SHA256 74021660c0a37afdf21210a73aac54340f5c58c7a97c2bc8acfdd59cfe105fa2.
- Axioms.txt: 25900 bytes; SHA256 27009a6d16199ad3476bdf6864af3afd2c22de5260381d58ed18ac29060d2484.
- Hypotheses.md: 9366 bytes; SHA256 de29c67b2f6b80eae7390a5c115e30fc33c82b9b68a08cfdb222aef2f373659e.

The two read-only target sources used in the audit have these identities:
ResidualGenuine.lean, 6952 bytes, SHA256
41da1457b6701d6a8b150223a7e9afe23bc4f838d50f3fea01027345477d33dd;
CoefResidualCounts.lean, 16216 bytes, SHA256
e40818f9ec3bb06b69a37af56e9c71eaa23fb0764dd5e12b2660ddc7b3e9a657.

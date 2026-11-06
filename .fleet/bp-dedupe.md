# bp-dedupe: blueprint consolidation report

Branch `wip/bp-dedupe`, based on `5b8d054`. The blueprint went from 392 articles to 353 (39
articles deleted; one moved, one trimmed and renamed). `autoform check` and `autoform audit`
are clean after every commit. No Lean file was touched. "Frozen" below means one of the
directories formalizers are working in now (syntax/templates, syntax/constants,
multiplication/local, assembly/approximation/real-*.md, compiler/natural, top-level model/*.md)
or an article with `statement: formalized`. In those articles I changed only dependency links
and, where a link pointed at a deleted article, the sentence carrying it. Each change is listed
below.

## Cluster 1: compiler/translation/machine/ against compiler/natural/

Canonical: compiler/natural/ (programs/, universal/, precision/). None of the machine/ articles
proved anything compiler/natural lacks (checked item by item), so the whole subchapter went.

Deleted (path, article id):
- compiler/translation/machine/register-programs.md af_d5ce94cef1e9aab84e6a994e
- compiler/translation/machine/program-numbering.md af_78597754145c35c23b6e471c
- compiler/translation/machine/program-numbering-decode.md af_baffc1518498e1c1e1c81649
- compiler/translation/machine/structured-programs.md af_baf48f90ae4938958835028b
- compiler/translation/machine/lowering.md af_ea8693e192956863703c6806
- compiler/translation/machine/lowering-correctness.md af_e7cad9833f61fcbb5996e607
- compiler/translation/machine/list-codes.md af_89b843dffed2f563c786d16b
- compiler/translation/machine/universal-interpreter.md af_c4ce10ea32ac26d1c470d7bf
- compiler/translation/machine/interpreter-step.md af_8eff9af34f8715b871d4c584
- compiler/translation/machine/interpreter-correctness.md af_e22821da89135f1eed147ccf
- compiler/translation/machine/precision-predicate.md af_34dc554711ec767ad0b6bf8a
- compiler/translation/machine/nondegenerate-multiples.md af_13158e82bc20414894926e9b (cluster 12)
- compiler/translation/machine/quadratic-norm-zero.md af_21c478969889e662f347eaad
- compiler/translation/machine/jacobian-formulas.md af_32b090fd87327c45949fffc4
- compiler/translation/machine/projective-generator.md af_9224e7100caa646cdb5a15d2
- compiler/translation/machine/capped-arithmetic.md af_550250f71b3e965cff620c96
- compiler/translation/machine/precision-ir.md af_30bb31bcffb71755576076b3
- compiler/translation/machine/ir-correctness.md af_eb6a0733e131b143b2e19f9f
- compiler/translation/machine/cantor-unpairing.md af_dda6bb3dae964f27f7d15d17
- compiler/translation/machine/wrapper.md af_64bc68a739cbd9e7360dcc40
- compiler/translation/machine/wrapper-correctness.md af_7ed9789bc99c3c2b91251ccd
- compiler/translation/machine/precision-machine-semantics.md af_0d182f0bee3b5fdaeaf60c2a
- compiler/translation/machine/five-input-specialization.md af_9475ebe08a0ae5387320b869
- compiler/translation/machine/specialization-semantics.md af_25a5543b3412621ee91b6258
- compiler/translation/machine/README.md (container)
- compiler/translation/program-literal-size.md af_4a8e044aefac1d6ca7c31346 (the m ≤ 2^20,
  c_3 < 2^(2^27) variant). The canonical bound is compiler/natural/universal/wrapper-code-size.md
  (1399 < c_3 < 2^(2^24)).

Relinked: compiler/translation/precision-circuit-scope.md (now depends on
natural/universal/precision-circuit.md; c_3 ≥ 2 comes from wrapper-code-size's c_3 > 1399
instead of "c_3 + 1 = 2^w(2D+1)"). precision-decision.md was relinked here and then deleted in
cluster 3. compiler/README.md and compiler/translation/README.md no longer mention a machine
subchapter; the translation README points to the natural chapter for Section 10.3 and cites
wrapper-code-size for c_3.

Content moved (into the implementation notes of the canonical natural articles):
- manuscript correction: the saturation lemma is stated in the manuscript for cap L ≥ 1 only,
  but the precision test can reach L = 0. The canonical decision-program-correct.md already
  handles L = 0 in its statement and proof, so no new article was needed; the remark and the
  upstream lemma `checkedCappedPower_zero_cap` are in its note;
- the Mathlib `StateTransition` design for runs and simulations (register-machine,
  lowering-correct, wrapper-correct notes), the reproduction issue for the interpreter's
  lowering (lowering note), digit-lemma pointers (program-numbering, program-numbering-encode
  notes), the generic form of the five-input specialization (precision-circuit-specialization
  note), the integer-pair form of the Jacobian check (jacobian-generator note), the
  `QuadraticAlgebra.norm_eq_zero_iff_eq_zero` instance (norm-zero note), the `@[irreducible]`
  advice for c_3 and the `CantorDecoder.loop` pointer (wrapper-program note), and the checking
  methods for the wrapper size (wrapper-size-check note).

## Cluster 2: the natural-code lemma

Canonical: compiler/translation/natural-code-semantics.md (id kept).
Deleted: assembly/value-templates/natural-codes.md af_733a993b598b73f751803fd0.
Relinked: assembly/value-templates/signed-encoding-semantics.md (now natural-code-semantics plus
the multiplication template for M); value-templates README.
For the lead: a third copy exists, syntax/templates/natural-semantics.md (frozen). After MW was
dropped (cluster 11) its statement ("assume M; Rel_natural(A) iff A = ι(n), n ∈ ℕ") is identical to
the canonical one. I could neither delete it nor change it. The natural-code-semantics note says
that one Lean proof should serve both. Once syntax/templates is unfrozen, delete one of them.
The syntax copy is the better proof, since it avoids injectivity of ι.

## Cluster 3: the precision predicate

Canonical: compiler/natural/precision/ (precision-relation, precision-guards, z-coordinate,
signed-encoding, signed-encoding-bijection, precision-height-constant,
precision-height-constant-value).
Deleted:
- assembly/approximation/precision-predicate.md af_429f9b160ce7eb19cb6edb13
- assembly/approximation/precision-acceptance.md af_be2811faba7749bf8b907409 (nothing needs it
  any more: admissibility comes from the nonzero-multiples lemma, and the constants agree by
  precision-height-constant-value)
- compiler/translation/precision-decision.md af_4214350c476f1cec6240dc05 (no article linked it;
  close-relation's proof does the same composition)
Relinked: close-relation, close-soundness, close-completeness, main-branch-exactness,
close-coordinates-semantics, signed-encoding-semantics, six-local-tests, pole-input-real,
nonzero-multiples, and the frozen real-accumulation.md and real-derivative.md (links only:
σ± and Tr come from model/field/quadratic-field.md, z from z-coordinate.md).
Statement edits (not frozen):
- close-relation now writes Prec(n,κ,a,l,j) as an abbreviation for accepts(enc n, …, enc j);
- six-local-tests defines z and w inline;
- close-coordinates-semantics states the convention z_0 = 0 (the template accepts j = 0);
- main-branch-exactness applies H at R = D, using A^{(0)}_ht.
The approximation and translation READMEs were rewritten to match.
Content moved: the upstream pointers `HeightConstantAlgorithm.heightConstant` and
`h6_for_max_317_eq_height_constant`, and the `10^12 < 15!` route, went into the note of
precision-height-constant-value. The coordination point between the compiler and assembly
chapters (`precision_rel_iff`) went into the close-relation note.

## Clusters 4–7: formal neighbourhoods, primes of ℤ[√2], reduction, P0 at the bad places

All four clusters are in one commit (cd38e7f), because deep-multiples, pole-input-local and
formal-multiple-existence needed edits from several of them at once.

Canonical:
- multiplication/local/formal-group.md for W_k, z, w and the subgroup property;
- multiplication/local/primes-above-p.md for odd primes;
- model/field/special-primes.md for (s) and (d);
- multiplication/local/dyadic-generator.md (with generator-dyadic-numerals.md) for
  v_s(x(P0)) = −6 and P0 ∈ E_3(s);
- model/descent/reduction-torsion.md for the homomorphism at degree-one primes of good reduction.
Kept, now depending on the canonical articles, because each states something different:
- assembly/local-tests/formal-multiplication.md (af_fdd11da248e86a22d5f24b93), rewritten as the
  one article on multiplication in a formal neighbourhood. It is stated over any discretely
  valued field, like the canonical article, and contains: additivity v(z(P+Q)−z(P)−z(Q)) ≥ 5k
  (from both deleted duplicates); v(z([n]Q)−n z(Q)) ≥ 5k; [p]W_k ⊆ W_{k+1}, and
  [n]W_k ⊆ W_{k+v(n)} when v(p) ≤ 4 (from size's filtration); and at odd unramified p,
  z([m]Q) = m z(Q) u_m with u_m ≡ 1. It also fixes the notation E_k(π) and ν_π used by the
  assembly chapter, and keeps the size chapter's remark that the manuscript uses the logarithm
  isometry at (s) where the inequality suffices;
- assembly/local-tests/k0-valuations.md, trimmed and renamed to dyadic-trace.md (id
  af_c0d526f1f4209b800feaa168 kept). It keeps only what the canonical articles lack:
  v_s∘σ = v_s, and v_s(x) ≥ 2k ⇒ v_2(Tr x) ≥ k+1, which pole-input-local uses;
- size/formal-multiple/reduction-homomorphism.md: all residue degrees and the nonsingular part
  at the cusp (d), strictly more general than reduction-torsion. Also kept: trivial-point-count,
  reduction-orders, bad-place-reduction, bad-place-congruences and odd-coefficient-extraction.
Deleted:
- assembly/local-tests/formal-group.md af_6c4778df56f0b27cf759ca28
- size/formal-multiple/filtration.md af_573c53f86fa85fe33fa0205f
- size/formal-multiple/odd-primes.md af_d48ab6071f79b1fd166dfdfa
- assembly/local-tests/good-reduction-multiples.md af_ae379070ab5b68f56ffcaa61 (the same fact as
  reduction-homomorphism + trivial-point-count, with a weaker bound)
- size/formal-multiple/dyadic-start.md af_a99666b6573a75b87d245b1d (= dyadic-generator)
- assembly/local-tests/bad-place-check.md af_2aee439afbca4d4c51eb7b86 (item 1 = dyadic-generator;
  item 2, [7]P0 ∈ E_1(d) by a 165-digit computation, is replaced by bad-place-reduction plus
  reduction orders)
Relinked: deep-multiples (whose proof now takes m_1 from reduction-orders with N = p, and from
dyadic-generator at s), pole-input-local, test-divisibility, formal-multiple-existence,
odd-coefficient-extraction, reduction-homomorphism and reduction-orders. The local-tests and
formal-multiple READMEs were rewritten.
Content moved (notes):
- the Lean route through the existing `ZInQ.kernel_add`, `vieta_shortCurve` and
  `sum_t_identity` (KernelReduction.lean) went into the formal-multiplication note;
- the Mathlib route for the primes above p went into the primes-above-p note;
- the padicValRat route went into the dyadic-generator note;
- the [7]P0 certificate method went into the bad-place-reduction note, as an alternative;
- in the reduction-homomorphism note: generalize the already proved `ZInQ.red`/`redHom`.
For the lead: model/descent/torsion.md (formalized) still says "in particular P0 has infinite
order", which overlaps cluster 12. I left it, since its main claim is the torsion subgroup.

## Cluster 8: division polynomials

No Lean declaration states either open article exactly.
- division-polynomial-jacobian.md is equivalent, but not identical, to
  `ZInQ.DivisionPolynomials.jac_identities_generic` (in the coordinate ring) and `jac_identities`
  (at a point), both in ZInQKernel/Model/DivisionPolynomials/Generic.lean. Lean uses the triple
  `jac n = (4φ_n, 4c_n, 2ψ_n) = 2•(φ_n, ω_n, ψ_n)` with Mathlib's `dblXYZ`/`addXYZ`, and proves
  `dblXYZ (jac n) = 8 • jac (2n)` and `addXYZ (jac (n+1)) (jac n) = (-8) • jac (2n+1)`. After
  cancelling the weighted factor 16, these are the article's dbl(J_k) = J_{2k} and
  add(J_{k+1}, J_k) = (−1)•J_{2k+1}.
- division-polynomial-elliptic-sequence.md (the law for normEDS) is not proved in Lean and is
  not used: NonTorsion.lean computes abscissas at the generic point from the recurrences.
Nothing depended on either article once division-polynomial-multiples.md (proved) stopped
citing them, so both were deleted:
- model/field/division-polynomial-elliptic-sequence.md af_121313091a3fb9c2242a4d65
- model/field/division-polynomial-jacobian.md af_a03a7b607a14bb792f6ba8d4
I rewrote the proof sketch of division-polynomial-multiples.md (statement unchanged) to describe
the Lean route, and updated the model/field README. A completed article may not carry a note, so
the Lean names above are recorded only here.

## Cluster 9: the shape of the natural precision circuit

Canonical: compiler/natural/universal/circuit-node-counts.md, with halting-node-check.md for the
power template's counts and constants.
Deleted: syntax/recipes/natural-circuit-statistics.md af_6a2e2d89347f6b92cbd08fca (it added
nothing).
Relinked: witness-accounting, recipe-heights, admissible-cutoff and the frozen
template-library.md (its Informally-uses link was replaced and halting-node-check added).
In the frozen circuit-node-counts.md, the sentence that linked the deleted syntax statement now
reads "The specification chapter's witness accounting uses items 2 to 4 …". The mathematics is
unchanged.
Content moved: the kernel-certificate routes and the reason c_3 ≠ 3 went into the
circuit-node-counts note.

## Cluster 10: |c_3| < 2^(2^24) in the size chapter

- size/majorants/admissible-cutoff.md now cites compiler/natural/universal/wrapper-code-size.md
  instead of the saved literal's 3,181,317 digits.
- size/constants/closed-comparisons.md lost item 8 (4·3181317 < 2^24). Both notes were updated.
For the lead: the frozen syntax/constants/fixed-constants.md still describes c_3 as "of
3,181,317 decimal digits". This is descriptive and not used by any proof, but it describes the
saved literal, not the Lean one.

## Cluster 11: Mordell–Weil is proved

- Removed the Mordell–Weil assumption and the main/mordell-weil.md link from 31 non-frozen
  articles, the assembly lemma included:
  - assembly: close-*, main-branch-exactness, ordinary-value-relation, value-templates/*;
  - compiler/translation: model-evaluation-semantics, natural-code-semantics,
    power-value-semantics, rational-translation, translation-soundness,
    translation-completeness;
  - multiplication: certificate/*, completeness/*, soundness/*, multiplication-template.
- Where the proof uses an article that still assumes MW (model/generator.md,
  model/membership-indices.md, multiplication/local/logarithm-*), the article now lists
  model/descent/mordell-weil-from-descent.md under Proof depends on.
- assembly/assembly-lemma.md is Lemma 1.2 over H, PC, 22P and CAT.
- Updated the READMEs: assembly, compiler/translation, model, model/descent, multiplication.
- In 23 notes, the shared assembly convention now takes the triple of hypotheses and points to
  `ZInQ.mordellWeilE`.
main/mordell-weil.md is unchanged.
For the lead: these frozen articles still assume MW in their statements:
- model/generator.md (also the generator certificate);
- model/membership-indices.md;
- multiplication/local/logarithm-nonvanishing.md;
- multiplication/local/logarithm-ratio.md;
- model/descent/rank-one.md (formalized; its hypothesis is "E(K0) finitely generated").
Lean drafts in some notes still take `hMW : MordellWeilE`; instantiate it with
`ZInQ.mordellWeilE`.

## Cluster 12: P0 has infinite order

Canonical: model/descent/nonzero-multiples.md (id af_27935f7d660df017638fbd70), moved from
assembly/value-templates/. It states that P0 has infinite order, that nonzero multiples are
affine with x, y ≠ 0 (so z and w are defined and nonzero), that ι is injective, and when the first
code coordinate vanishes. Its proof depends on model/descent/torsion.md.
Relinked:
- every assembly consumer, by path;
- compiler/translation/precision-decision.md (since deleted), which had used the deleted machine
  copy;
- model/field/fixed-point-codes.md (proof now via the lemma);
- size/norms/coordinate-heights.md, which now cites fixed-point-codes instead of re-deriving the
  division-polynomial formula from torsion.
The natural precision README says that precision-guards' hypothesis is discharged by the lemma.
The note names the Lean code waiting for it: `ZInQ.iota_eq_psi (hP0 : ¬ IsOfFinAddOrder genP0)`
and `ZInQ.iota_injective_of_addOrderOf_eq_zero`.
For the lead: the frozen precision-guards.md keeps its hypothesis "assume P0 has infinite order".
The frozen z-coordinate.md, point-codes.md and multiplication/local/logarithm-* keep their
remarks.

## Cluster 13: other duplicates

Fixed:
- compiler/translation/natural-circuit-values.md defined the polynomial of a natural circuit
  again. It now cites compiler/natural/formulas/natural-circuit-semantics.md and keeps only the
  values and admissible assignments.
- multiplication/local/logarithm-coefficients.md and syntax/templates/log25-coefficients.md
  (both frozen) state the same seven identities. I only added a Proof-depends-on link from the
  multiplication copy to the syntax copy, so the identities are proved once.
  For the lead: merge the two when the directories are unfrozen.
- multiplication/certificate/constants-properties.md item 1 (M0 ≥ 1) now cites
  size/formal-multiple/formal-multiple-existence.md instead of the cutoff.
- compiler/translation/precision-circuit-scope.md listed again the counts and constants of
  circuit-node-counts, halting-node-check and the specialization statement. It now states
  well-formedness and derives it from those articles.
- compiler/translation/rational-translation.md item 2 repeated
  power-value-semantics.md word for word. The item is gone, and the proof cites the
  power-value article.
Reported, not changed. A canonical choice is not obvious for these, or a frozen article is
involved, or the overlap is only partial. Most need a mathematical decision from the lead:
- the definition of a "good" pattern prime appears three times, inconsistently:
  - main/prime-pattern.md (formalized): splits, good reduction at both places,
    gcd(d1,d2) = 4 and p ∤ d1d2;
  - multiplication/completeness/pattern-slopes.md item 3: the same without p ∤ d1d2;
  - multiplication/completeness/selected-prime-precision.md: "good pattern prime" means
    r² ≡ 2 and 75 ∓ 53r ≢ 0 (mod p), with no gcd condition.
  The two multiplication articles should cite main/prime-pattern.md or rename their weaker
  notion. I did not change them, because each article's proof relies on its own wording.
- compiler/translation/natural-circuit-well-formed.md ("well-formed with bound V") overlaps
  compiler/natural/formulas/natural-circuit-semantics.md item 3 ("well scoped", frozen). They
  are different predicates: well-formed adds node order and constants ≥ 2, well-scoped adds
  that the blocks tile [0, V). The precision circuit gets both. One predicate could be derived
  from the other.
- assembly/local-tests/pole-input-real.md re-proves, for one product of six factors, the
  positivity and smallness that multiplication/completeness/pole-input-positivity.md and
  weak-approximation.md prove for the slope certificate (six groups of twelve factors). The
  multiplication pair essentially implies it, but not verbatim. Making pole-input-real a
  corollary means restating the multiplication lemmas generally.
- assembly/local-tests/formal-multiplication.md items 3–4 overlap
  multiplication/local/logarithm-isometry.md item 2 (v(z([m]Q)) = v(z(Q)) + v(m) at odd
  unramified p). The elementary version needs no completion, and the frozen one is the
  manuscript's route; keep both or pick one when multiplication/local is unfrozen.
- multiplication/soundness/generator-height.md restates model/heights results (quadratic
  property, the basic comparison, the height of 2R) transported to E by θ. It already
  proof-depends on them.
- multiplication/soundness/rational-height-bounds.md defines the rational height again, and
  restates h ≥ 0, already in the formalized model/heights/x-height-formula.md. It has no
  dependency on that article.
- multiplication/certificate/local-templates.md items 1–2 are template-level wrappers of
  syntax/field-pair-arithmetic.md item 5 (formalized), on which they already depend.
- syntax/field-pair-arithmetic.md item 3 and syntax/nonzero-gadgets.md item 2 (both formalized)
  both say NZ_K(u) is satisfiable iff [u] ≠ 0.
- compiler/translation/model-recipe-relation.md's last sentence restates
  syntax/language/generator-references.md (formalized).
- size/formal-multiple/formal-multiple-existence.md re-transcribes the ξ convention and the
  three divisibility conditions of syntax/constants/least-formal-multiple.md.
- size/cutoff.md restates r-equals-d, t-identity, t-bound and formal-multiple-existence as a
  summary (Proposition 12.1). It proof-depends on all four.
- Definitions re-transcribed inside statements:
  - model/membership.md and model/raw-addition-points.md (frozen) re-transcribe the member
    and raw_add formulas;
  - syntax/templates/template-pole.md writes Q_pole out again;
  - M_S(u) is defined in main/six-contact-estimate.md and again in
    multiplication/certificate/constants.md and assembly/local-tests/test-divisibility.md.
Checked and left as legitimate corollaries:
- guard-true-triples vs guard-semantics;
- small-constant-bounds item 1 vs primorial-literal;
- pole-input-local vs pole-input-valuations;
- deep-multiples vs reduction-orders and formal-multiple-existence;
- odd-coefficient-extraction, which is stronger than primes-above-p item 4.

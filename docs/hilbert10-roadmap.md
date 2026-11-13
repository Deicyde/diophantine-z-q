# Hilbert10: end-to-end proof roadmap and contribution guide

## Finish line

**The work is not done until the intended Hilbert’s tenth problem result over ℚ is fully proved.** Green PRs, compiled adapters, reviewed suppliers and a combined source tree are intermediate milestones.

The intended chain is:

1. Construct the actual arithmetic/geometric objects and supply the hypotheses of the selected proof route.
2. Prove a polynomial defines **ℤ inside ℚ**, not just an equality of two finite computations or a conditional implication.
3. Connect that definition to an explicit effective reduction of integer Diophantine solvability to rational Diophantine solvability, and the resulting Hilbert10 undecidability theorem.
4. Verify the complete source-to-consumer chain at one coherent revision, with all remaining mathematical premises discharged.

The current formal target is `ZInQ.FrozenTarget`, in [`ZInQKernel/Target.lean`](../ZInQKernel/Target.lean). It asserts an integer-coefficient polynomial in **292,890,231,905 variables**, with the frozen degree/coefficient bounds, such that a rational q has rational witnesses exactly when q is an integer. The separate Version 17 **214-variable quartic manuscript** and its numerical certificates are not silently substituted for that formal statement. A source/formalization gap is not by itself a verdict that a manuscript is false.

## Read the statuses correctly

- **Proved supplier:** a theorem has its stated full type and proof. Its hypotheses still matter.
- **Conditional consumer:** it proves the desired output only after its explicit inputs are supplied.
- **Actual wiring:** those inputs are constructed from the same objects/maps/prime families used downstream; a desired `Fact` or an unrelated model is not wiring.
- **Validated revision:** the combined source/types/bodies and exact-head CI have actually passed. Another PR’s CI does not validate the union.
- **Integrated:** the result is on the intended main revision. An open proposal or local tree is not integrated.
- **Finished:** the complete intended Hilbert10 result is proved, not merely an individual leaf or artifact.

Historical records retain their original scope and source revisions. A result on another mirror or a changed statement needs its own exact comparison; neither “five open everywhere” nor “all folded everywhere” is justified by a PR title.

## Current formal routes

### Canonical five-input contract

[`ZInQKernel/Contract.lean`](../ZInQKernel/Contract.lean) deliberately checks the original conditional headline:

```text
SixContactMin
  → TYZThm35ReadingA
  → HeckeContinuation
  → FunctionalEquation5
  → GrossZagier
  → FrozenTarget
```

This file itself does not discharge those five inputs.

### Proposed analytic reduction to three inputs

The source contributed by #64 proves the `heckeContinuation` and `functionalEquation5` suppliers. Its [`GaussFE/Headline.lean`](../ZInQKernel/Contrib/GaussFE/Headline.lean) also provides:

```text
SixContactMin → TYZThm35ReadingA → GrossZagier → FrozenTarget
```

via `frozenTarget_of_sixContactMin_tyzThm35ReadingA_grossZagier`. This is real progress in the analytic branch, but **still a three-input conditional theorem**, not a completed integer-definition/Hilbert10 proof. The original canonical contract is preserved; the combined tree and exact provider types must be validated rather than inferring a result from the source names.

### Height/H branch

[`Hypotheses/JHeight.lean`](../ZInQKernel/Hypotheses/JHeight.lean) proves the return from `JHeightBound Mult.S_mul` to `SixContactMin`. Its own source explicitly distinguishes that implication from constructing `JHeightBound`. Thus a height-bound constructor for the actual QM/surface/representation/modular/conductor objects remains a critical join.

The proposed #62 H-decomposition/glue route is useful source material, but changes Objects/root/contracts and has a different proposal history. In particular, it replaces the broad protected QM dichotomy with a Yu/indefiniteness-based statement and specialization; that is not automatically a proof of the canonical universally quantified package. It is **not** imported into this proof-only consolidation by choosing whichever target definition was written last. Its exact compatibility with current main and actual-object instantiations must be reviewed separately. Existing `RhoCont`, `TateBC`, C9 and other generic glue in that proposal should be read before claiming an infrastructure theorem is missing; generic glue does not automatically construct the required objects.

The final formal integer-definition-to-Hilbert10 reduction also needs an identified, checked consumer. Do not mark the task finished merely because a theorem ending in `FrozenTarget` is available with hypotheses.

## Consolidated supplier work

The [source-preserving consolidation](issue37-consolidation/README.md) combines **21 proof PRs**, retaining all 510 distinct source/note files and eliminating 151 repeated file occurrences. The [exact source map](issue37-consolidation/SOURCE-MAP.json) binds every file to its PR, source commit, Git blob and SHA-256. No theorem body or original target is changed for deduplication.

| Area | Original PRs | What the contribution supplies | What it does not automatically supply |
|---|---|---|---|
| Coefficients, finite-field counts, convergence and TYZ-input interfaces | #38, #39, #40, #43, #45 | Exact coefficient/point-count APIs, Hasse/convergence and input-equivalence work | A proof of every actual TYZ or rank hypothesis |
| Analytic continuation and functional equation | #64 | Exact providers and the folded three-input headline | `SixContactMin`, TYZ reading A or Gross–Zagier |
| Algebra and representation comparison | #42, #47, #50 | Skolem–Noether, Brauer–Nesbitt and Frobenius-density/C10 glue suppliers | The actual r₃/r₅ and modular representations, shared traces or semisimplicity data |
| General tame ramification | #52 | The exact general `PkgI2.AbhyankarDVR.{0}` proof, every original prime | A construction of the particular extension/prime/tame data needed by H |
| Herbrand, different and conductor infrastructure | #48, #55, #56, #58, #59 | Local/global suppliers and a genuine D1 numerical consumer | The actual global objects and residual ramification/factorial inputs |
| Adelic/cohomological/local-square-root work | #46, #49, #57, #60 | The stated quotient/cochain/cocycle and conditional local-square-root interfaces | Unrestricted LocalKW or the remaining actual H construction |
| Actual completed fields and prime/scalar maps | #61 | Native completion/Galois/decomposition/Qp/Zp/index bridges | Arbitrary embedding integral preservation or a full conductor/KW theorem |
| Global inertia and conductor assembly | #67 | Closed global inertia/degree/coverage reductions; conditional same-compositum assembly | Exponents and the actual arithmetic bounds required for unrestricted T17 |

This table is a source-to-consumer map, not an assertion that every original PR has been merged or that the new combined tree has already passed. The proposal’s separately bound validation/CI records state the actual result at its final head.

## Highest-value contribution targets

Before taking a target, check [Issue 37](https://github.com/elliotglazer/diophantine-z-q/issues/37) and existing claims. Claim **one named source-to-consumer edge**, with a file and intended full type, rather than “work on H” or “formalize all of KW”. The current point/Tate/Frobenius lanes are already allocated; coordinate before duplicating them.

### H10-QM: construct one actual fibre/descent witness, not an abstract substitute

**Boundary:** the proposed #62 `QM/Structures.lean` and `QM/Leaves.lean` route. Its `QMStr` is an injective unital order action on the actual abelian variety, and `R1R2fp` ties the moduli, forgetful, fibre and reciprocity properties to **one** witness. The proposed `fibre_conjugates_isomorphic` and `leaves_on_one_witness` reductions should be reused, not reproved.

**Needed construction:** the genuine surface/fibre over the canonical `Jmap u`, with the same number field, conjugates, isogenies, order action, reduction and theta/height objects used next. A zero-variety example, an existential model with the desired numerical output assumed, or different witnesses for each downstream use does not close this edge.

### H10-H: construct the actual height-bound input

**Needed output:** the actual `JHeightBound` assertion consumed by `sixContactMin_of_jHeightBound`, on the same `Mult.S_mul`/Hauptmodul/rational-point route.

**Work:** build the actual surface/QM, descent, modular and height comparison objects; connect conductor/level bounds and the Faltings/Hodge/polarization/height data through their exact maps. The existing `GlueOutputs → JHeightBound → SixContactMin` numerical joins are proved reductions, but the source warns that a numerical output payload alone is not a faithful abelian-variety literature theorem. Supply its real object-backed inputs rather than hiding the desired height bound in a payload. Preserve all actual source hypotheses and normalization constants.

### H10-C10: supply the genuine 3/5 Frobenius-comparison data

**Boundary:** `GlueC10Link.c10_of_squares` and `FrobSquares` in the [exact proposed #62 `HDecomp/C10/Link.lean`](https://github.com/elliotglazer/diophantine-z-q/blob/e303a42543e9adf89aa70075372b622f4870a770/ZInQKernel/HDecomp/C10/Link.lean), which is held apart from this consolidation’s current-main source.

For every relevant Frobenius g outside S, construct **the same** L, residue field k, A/Aσ, μ, reduced varieties, F, μ̄ and N≠0 for both ℓ=3 and ℓ=5, with actual Tate-module transport/reduction maps and these three squares:

1. `red' ∘ σs = Vmap F ∘ red`;
2. `red ∘ Vmap μ = Vmap μ̄ ∘ red'`;
3. `Ψ.conj (N • Tσ) = (Vmap μ ∘ σs).baseChange E`.

The existing square-to-comparison and trace-link glue is already proved; do not reprove it. The actual coefficient maps C→k₃ and C→k₅, common modular Frobenius coefficients, C9 comparison, bases, continuity and semisimplicity of the **same k₃** representations remain genuine inputs. Do not assume these in a new payload or embed ℚ₃ and ℚ₅ in an invented common Hausdorff model.

**Allocated prerequisites:** actual point/base-change group isomorphism and Hom naturality; the distinct same-M PkgI3/Stacks Tate linear/naturality/rank consumer; and the relative-Frobenius group-map adapter with prime-field and finite-field packaging. The separately bound unpublished point/Tate component now reports the **full original `PkgI3.TateModuleFree` predicate**, ordinary compilation/boundary cases, fresh trust-zero import, actual own-body/type checks, and hypothesis/universe/corruption controls using only standard axioms. Its external dependency bodies were not all freshly replayed. Final non-author as-built reconciliation, public/full-normal validation and main/provider integration remain separate; the optional-dependency result is not included in this source union. Do not reimplement it as if no source existed. The Frobenius lane separately reports finite-field q-power packaging with `#k=p^f`; that is not an unrestricted p-power k-linear map or a Galois/Tate/reduction comparison. These generic prerequisites still need the actual reduction/Galois/isogeny application. Over a general characteristic-p k, relative Frobenius targets A^(p); a finite/prime-field specialization does not justify A^(p)=A for arbitrary k.

### H10-REP: actual semisimplicity and modular/C9 suppliers

**Needed output:** the representation and coefficient/trace/continuity/semisimplicity inputs at the native C10 consumer, with the exact fields, subrepresentations, matrix units and finite-dimensional structures.

Read the proposed generic `RhoCont`/`TateBC` and C9 glue before implementing another adapter. In that proposal, `I3Linalg/C2.lean` already proves `SemisimpleBaseChange`; `RhoCont` proves continuity from free finite actual Tate modules, and `TateBC` proves the required bijectivity reduction from an injective same-group map and equal ranks. Reuse these reductions rather than advertising them as missing everywhere. The remaining work is the actual Faltings/Tate inputs, point/dimension maps and representation data. Faltings’ semisimplicity on the actual `PkgI3.AbVar.galRep` is not supplied by an isomorphic vector-space model. The modular ρ₃/ρ₅/newform/C9 trace data must refer to the same arithmetic construction. A finite/free Tate-module result or a basis by itself does not supply this package.

### H10-KW: actual completed inertia bounds and conductor witness

**Boundary:** `nonempty_embedding_at_primePowerConductor_of_arithmetic` in [`GlobalPrimePowerAssembly.lean`](../ZInQKernel/Contrib/KroneckerWeber/GlobalPrimePowerAssembly.lean).

The frozen theorem constructs a positive n and the original-L cyclotomic compositum `E_n`, proves coverage/totient arithmetic, and keeps two inputs on this **same E_n**:

- `hU`: unramified over ℤ at actual integer primes outside S;
- `hB`: actual inertia cardinality above p∈S is at most `(p ^ r p).totient`.

The theorem allows arbitrary finite S. The intended original ramification-set application needs actual suitable exponents and these bounds; an unrelated completion, a cyclotomic-relative unramifiedness statement, or a different conductor-dependent embedding is not enough. Later canonical-image/restriction/unramifiedness source is separate from the frozen 22-module review; its failed fresh-prefix timeout is not a pass.

**Verification blocker:** the later unpublished 494-module LocalKW/T30 source/type packet has compiled provider types, but the unmodified full raw check has no pass. The two-hour I/O-only diagnostic timed out without a report; it is not a substitute. Verification needs suitable isolated large compute, with headroom above the observed roughly 140 GiB footprint, or a separately reviewed scalable verification method—never a scope/kernel-option shortcut. The public #46 source in this consolidation is the earlier conditional route, not those unpublished ports.

### H10-D1: instantiate the genuine numerical conductor consumer

**Boundary:** [`ConductorBounds/D1.lean`](../ZInQKernel/Contrib/ConductorBounds/D1.lean), `D1_closed`.

The Hilbert/Serre literature leaves are discharged, but its original 14 binders/data remain: L/Galois/number-field, p/prime, P/prime/lying-over, a with `1≤a` and `e(P/ℤ)≤a!`, and b with a nontrivial actual ramification group. Supply them from the actual H construction. The result `phi(ramCard L P) b ≤ 4*a²` is not by itself a constructed conductor or height bound.

### H10-TYZ and H10-GZ: close the remaining analytic/rank inputs

**Needed outputs:** the precise `TYZThm35ReadingA` (or the separately justified TYZ-input route) and `GrossZagier` assertions consumed by the selected headline.

The exact canonical `TYZThm35ReadingA` input says the relevant analytic order ≥2 forces **both** row values `T5aCl d` and `T5bCl d` to vanish. The exact canonical `GrossZagier` input returns an actual rational affine point of nonfinite additive order from analytic order exactly one for the stated elliptic curve/continuation. Match those full source statements, not a nearby rank slogan. An equivalence of input packages is not a proof of one package. The proved continuation/functional equation removes those particular leaves; the full Hecke provider covers every natural d≠0, while FE5 and the folded rank route use the squarefree d≡5 mod8 domain and the completed-L strip `0<Re(s)<2`. Do not extend the latter through invalid Gamma values.

Match actual paper versions, curve objects, coefficient conventions, nonvanishing and exceptional cases. A changed source reading or downstream application needs a new explicit comparison rather than a favorable old citation. The chosen rank/Green–Tao/density route already has its stated source reductions; do not open another supplier campaign for those simply because the final H/rank inputs remain unsupplied.

### H10-END: explicit final integer-definition/undecidability consumer

**Needed output:** an end-to-end theorem with the intended Hilbert10 conclusion and no remaining unproved mathematical premise.

Identify or implement the exact conversion from the chosen polynomial definition of ℤ in ℚ to an effective encoding of integer Diophantine systems over ℚ, and connect the integer undecidability result. Record the original polynomial/domain and quantify over all intended inputs; a finite example, degree bound or numerical certificate is not an undecidability theorem.

## How to submit a useful contribution

1. **Claim:** exact file/declaration, required input, intended output and next consumer in Issue 37; identify any existing owner before starting.
2. **Lock the statement:** quote the full type, including universes, implicit/typeclass arguments, prime/index coverage, scalar towers, continuity, nonzero/unit and finite-dimensional hypotheses.
3. **Read the supplier:** compare the actual source theorem and proof with the constructed objects. Record available result → needed assertion → connecting derivation; names alone are not evidence.
4. **Prove the bridge:** no custom axiom, `sorry`, hidden desired `Fact`, weakened quantifier or substitute model. Standard Lean axioms are not extra mathematical leaves.
5. **Validate:** fresh source/type checks, owned-body kernel checks, meaningful positive/negative boundary cases, then the unchanged full gate and exact-head public CI for the combined candidate. Keep compile, scoped replay and full validation distinct.
6. **Preserve history:** old snapshots and failures remain; a timeout/cancellation is not a pass. If a source/consumer changes, give new source/type/replay bindings rather than silently refreshing a favorable old report.
7. **Contribute one edge:** put the result against the consolidation’s agreed dependency layer. Do not copy its already-shared 9/27-module transport closure into another standalone PR or open another equivalent point/Tate adapter.

Use the repository’s actual Lean 4.35.0/dependency pins. Optional Axiom/cache, target/registration and checker tooling proposals remain separate; do not upgrade or alter the admission policy to make a proof compile. The current contributor guide and actual main ruleset govern review; retired historical checks are not automatically current, and retiring a check does not prove the mathematics.

## Remaining completion checklist

- [ ] Actual height/H input supplied for the selected native route.
- [ ] TYZ reading/input statement and Gross–Zagier joins fully supplied with exact source-to-consumer checks.
- [ ] Original integer-definition theorem proved without remaining mathematical assumptions.
- [ ] Explicit effective Hilbert10 consequence checked.
- [ ] One coherent combined revision validated and independently reviewed at the actual intended source scope.

**Until all required joins are proved and the intended Hilbert10 result follows end to end, the work is not done.**

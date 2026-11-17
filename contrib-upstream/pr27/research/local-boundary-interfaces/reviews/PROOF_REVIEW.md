# Proof and assembled-interface review of the four local-boundary modules

Date: 2026-11-10. Reviewer: Codex model agent
`/root/normalization_claim_review`. The reviewer did not author these four
modules, native runner or finite-control script and has made no source edits.
This is a fresh bounded nonauthor model review, not external human acceptance
or an independent kernel implementation. An initial source-only review on
this date left assembly checks pending; this revision records their completion
on the exact bytes bound by `PROOF_REVIEW_INPUTS.json`.

### 1) Verification target

The target is the four-module submission selected by `PR_SCOPE.md` and its
41 named roots in `TARGETS.json`: 19 in `ConjugateLocalTransport`, eight in
`ConjugateLocalH1`, seven in `ActualBoundaryCup`, and seven in
`OrthogonalComparison`. The exact source files are byte-identical to research
commit `33483f751e6dcd3f91fb303969838aca33ad0458`; I verified their hashes and
direct import lists against that Git object and `ORIGIN.json`.

The candidate base is V13 commit
`9c0b3aba60d90fdcac82115f0582a6f52f1054f7`. The four imports close over Mathlib
and the local transport module; none imports the frozen 39-target packet.
The inspected Mathlib checkout is
`56a005855ea17e0b0958f73ec801ae140b0a1679`. Its actual H1 quotient and homotopy
definitions were read, rather than inferring their meanings from theorem names.

The mathematical claim is conditional local transport, cochain correction,
and preservation of homology by a supplied comparison inverse. It does not
construct all actual arithmetic input objects or prove the determinant switch.
The final README and application note, all printed definitions and elaborated
statements, the submitted native build/axiom evidence and the adverse controls
have now been inspected. The reviewer reproduced the finite controls, but did
not repeat the integrator's Lean build or run an external proof checker.

### 2) Independent re-derivation (outline)

#### Local representation and cocycle transport

Write rho=alpha*T restricted to H. Its action is a representation because the
scalar action commutes with the R-linear endomorphisms. No faithfulness,
finite freeness, division by two, or field assumption is used.

Let phi=t*tau be the displayed Frobenius/transporter factorization. The source
equality `T(phi)=T(tau)` implies T(t)=1 by multiplying on the right by
T(tau)^-1. Thus rho(t)=alpha(t) and rho(t^-1)=u, where
`u=alpha(t)^-1` is one specified integral unit for every cocycle on these data.
The argument derives scalarity of the transport from the representation
equality; scalar transport or the target coordinate identity is not a field
of `LocalData`.

For a crossed cocycle p, expand p(x*a) and p(a*(a^-1*x*a)) and cancel p(a).
Applying rho(a^-1) gives

```math
p(a^{-1}xa)=\rho(a^{-1})\bigl(p(x)+(\rho(x)-1)p(a)\bigr).
```

If rho(x)=1 this reduces to rho(a^-1)p(x). The finite generator is phi².
Since T(phi)=T(tau), tau²=1 and alpha(finiteGenerator)=1, it acts trivially.
The inertia element also acts trivially by its two displayed hypotheses.
Moreover tau=t^-1*phi gives the conjugation identities

```math
\tau\,\mathrm{fin}\,\tau^{-1}=t^{-1}\mathrm{fin}\,t,
\qquad
\tau\,\iota\,\tau^{-1}=t^{-1}\iota^\ell t.
```

The crossed-cocycle power formula then gives the exact coordinate transform
`(f,s) -> (u*f,u*(ell*s))`. The `(u*f,-u*s)` specialization uses the explicit
premise `(ell:R)=-1`. It does not follow merely from ell being an inert prime.

Raw conjugation is pullback along the subgroup conjugation homomorphism. Its
coefficient representation is rho composed with that homomorphism. The code
keeps this carrier distinct from rho and inserts no second coefficient J.
No global quadraticity hypothesis on alpha is introduced or used.

#### Descent to genuine H1

Mathlib's `H1` is the degree-one cohomology of its inhomogeneous cochain
complex; `H1pi` has kernel the actual one-coboundaries. At an element x with
rho(x)=1, every coboundary rho(x)v-v evaluates to zero. Hence evaluation
factors through that quotient. Pullback by gamma sends the coboundary of v
to the coboundary of the same v for rho composed with gamma, so pullback also
descends. Surjectivity of `H1pi` proves the formulas on all H1 classes from
their cocycle formulas. These arguments match the use of
`liftOfSurjective`, `H1pi_eq_zero_iff` and `H1_induction_on` in the code.

The result is actual algebraic group cohomology, rather than a fresh abstract
class carrier defined to satisfy the conclusion. Continuous Galois cohomology
and a common finite arithmetic quotient are not supplied by these definitions.

#### Boundary-cup correction

The only cup identities assumed are the displayed degree-(1,0) and (0,1)
Leibniz rules. For closed l, the former reads
`dt(cup10(l,q))=-cup11(l,d0(q))`. Bilinearity and
`localCondition=localGlobal+d0(q)` therefore give

```math
\operatorname{cup}_{11}(l,\mathrm{localCondition})
 =\operatorname{cup}_{11}(l,\mathrm{localGlobal})
  -d_t\operatorname{cup}_{10}(l,q).
```

A linear trace annihilating dt removes that correction. The second Leibniz
rule gives the left-boundary statement with positive differential sign;
the first gives the right-boundary statement with negative sign. After trace,
both vanish. The representative-change roots then follow by bilinearity.

The premises are degreewise cup/differential laws, a closed direction, a
cone-cycle equation and a boundary-annihilating trace. They do not assume a
boundary-duality adjunction or the desired normalizer equality. Nevertheless,
`LocalCupData` is not an implementation of a whole differential graded
algebra or Selmer complex: even d1*d0=0 is not needed by these particular
identities and is not a structure field. Actual cup maps and the common
compact-support trace must still be identified in an application.

#### Cone comparison and the homotopy inverse

For the H22 differential
`d(g,u,q)=(dG g,dU u,loc g-inc u-dL q)`, use
`j(g,u,q)=(g,a u,q+h u)`. The middle component commutes by the chain-map
identity for a. Comparing the third components reduces exactly to
`inc-inc' a=dL h+h dU`; the plus sign in j is required. The first component
is preserved literally. On replacing q by minus the other cone coordinate,
the comparison's third component becomes `l-hu`, as the sign-change root
states.

For actual homological complexes and chain maps, suppose `j >> q=p` and
`k >> j` is homotopic to the identity on D. Postcomposition of that homotopy
with q gives `k >> p` homotopic to q. Postcompose further with loc for the
localized assertion; Mathlib's homotopy-invariance theorem gives equality
of genuine homology maps. A right homotopy inverse is enough for this
conclusion; existence of that inverse is not proved or silently inferred.

The degreewise construction and the categorical consequence are separate
interfaces. This module does not build a specific arithmetic Selmer complex,
package the degreewise map into its arithmetic chain-map instance, or produce
the inverse at a localization. Its global-projection premise is a legitimate
lower-level comparison identity, not the conclusion that an inverse preserves
the projection.

### 3) Checks

Source identities and direct imports were checked against the exact extraction
commit. All 573 source lines in the four modules were read. I checked the
critical signs, composition directions, coefficient carriers, zero cases and
the origin of every substantive premise of the selected roots. No `sorry`,
new mathematical axiom or assumption of the target determinant normalization
appears in these source proofs. This observation does not replace a transitive
axiom audit of compiled roots.

Boundary analysis identifies the following application guards:

- The negative inertia specialization requires `(ell:R)=-1`. For one fixed
  natural ell this cannot hold in a characteristic-zero ring. Its arithmetic
  use is at finite coefficient stages; transporting the identity through a
  retained limit is separate work. The pre-specialization formula with ell
  is valid over the full advertised commutative-ring domain.
- ActualBoundaryCup uses the cone coordinate with third differential
  `-loc+inc-dq`. OrthogonalComparison uses H22's `loc-inc-dq`. Their q
  coordinates differ by a sign. The application must perform that conversion;
  the selected sign-change root records it.
- Evaluation on H1 requires trivial action at the evaluated element. Without
  it, a nonzero coboundary can have a nonzero evaluation although its H1 class
  is zero. The conjugate evaluation hypotheses are derived for the conjugate
  representation, not copied by identifying it with the original one.
- Zero cup maps or a zero trace are permitted by the abstract laws. These
  theorems therefore prove compatibility, not nonvanishing or perfect duality.
- Removing closedness, the Leibniz sign, the trace condition, the inclusion
  homotopy or the right-inverse hypothesis invalidates the corresponding
  deduction. Submitted adverse controls should exercise these guards.

#### Assembled statements and native evidence

I read all 993 lines of `evidence/native/axioms-and-statements.stdout.txt`,
including all 16 selected definitions and all 41 elaborated proof-root types.
The types preserve the advertised domains, hypotheses and composition
directions. There is no elision marker in the statement portion. The printed
definition bodies omit proof fields in Lean's usual way; this is not a dump
of every expanded proof term, and source reading supplies the corresponding
definition-level inspection. The two homotopy-valued definitions are honestly
counted as proof roots rather than 41 proposition-valued theorems.

I read `verify_native.py` completely and independently compared its recorded
inputs, target list, generated audit, per-root axiom lists, exit codes and
artifact hashes with current files. All 17 published native evidence files
are byte-identical to the completed reviewed run. The seven native commands
returned zero; the four module compilations and audit command each explicitly
set `debug.skipKernelTC=false`. All native stderr files and all four module
stdout files are empty. The recorded before/after input hashes agree and match
the reviewed source, README, APPLICATION, origin, target and runner bytes.
The four fresh local `.olean` artifact hashes also match the run receipt.

The run is Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
Its explicit `LEAN_PATH` places a new selected-module output directory before
the pinned dependency caches and omits stale project build paths;
`LEAN_SRC_PATH` is unset. The audit traverses dependencies of each selected
root with `collectAxioms`; all reported axioms lie in `propext`, `Quot.sound`
and `Classical.choice`. The declaration and axiom multisets contain precisely
the 41 selected roots, once each.

This establishes fresh selected-project compilation and a transitive axiom
audit with kernel checking enabled. Imported dependency caches and the Lean
standard library remain trusted: clean tracked dependency sources and matching
Git revisions do not authenticate those binary caches. No protected theorem
comparison, full dependency rebuild, paranoid run, proof export replay or
independent checker run was performed for this packet. The README states
these limits correctly.

#### Independently reproduced finite controls

I read all 292 lines of `check_controls.py` and its design before rerunning
it with Python 3.13.12, `-B` and optimization flag zero. Its exact results
match the author's Python 3.12.3 output in every JSON field except interpreter
version. Optimized execution refuses to run with exit code 1. Inputs were
unchanged across the reproduction. See `CONTROLS_REVIEW.md` and
`CONTROLS_REPRODUCTION.json` for details, scope and portable command provenance.

The results comprise 64 cochain trials with nonzero correction, 640 degreewise
cone cases (218 reject the wrong sign), 4,680 two-term homotopy cases, 128
crossed-equation checks, 256 coboundary-pullback checks and 16 rejected
nilpotent-parameter inverse candidates. Eleven explicit adverse witness
families cover the stated sign, closedness, trace, coefficient-carrier,
evaluation, projection and independent-rescaling shortcuts. These are finite
diagnostics, not exhaustive arithmetic coverage or a proof of actual Selmer
data. In particular the torus pairing is nonzero but not claimed unimodular;
the degreewise cone samples are not claimed to be complete chain complexes.

### 4) Discrepancy report (if any)

No false statement, proof defect or incorrect diagnostic conclusion was found
in the four source modules or reviewed supporting code. The final README and
APPLICATION explicitly retain the finite-stage minus-one guard, the cone-sign
conversion, distinct conjugate coefficient carrier, supplied-inverse premise
and arithmetic instantiation boundary. Historical source-application references
are mapped to immutable source links and the current application note.

The application note correctly distinguishes the source class-functional
coordinate from an assumed stored-row matrix realization. It does not promote
these local deductions to the missing actual normalization identity. This
review accepts the formal-to-application scope and displayed algebra, not a
new certification of every cited arithmetic construction or published source
section. The source-application specialist review remains a separate record.

I also read the bound pre-clean-reproduction versions of VERIFICATION,
FINDINGS and PR_DESCRIPTION. Their counts, mathematical claim ceilings,
cache-trust description, adverse-control interpretation and explicit pending
clean-checkout gate agree with the inspected evidence. They do not claim
publication, hosted checks or external acceptance. A later status update after
clean reproduction must be covered by its own supplement rather than silently
substituted for these reviewed document bytes.

### 5) Certification result

**PASS within the displayed conditional algebraic scope.** No premise merely
restates the advertised local transport, coboundary correction or
inverse-preservation conclusion. The bound four-module source, README,
APPLICATION, native runner/evidence and finite controls are accepted by this
internal nonauthor model review for the scoped additive submission.

This does not establish the full arithmetic boundary-cup adjunction,
determinant comparison, localization coverage, continuous-cohomology
realization or main Diophantine theorem. It does not transfer the frozen
39-target packet's cloud evidence to these 41 roots. Shared model, source
and toolchain dependencies remain. The current proposed PR prose is reviewed;
any later clean-worktree reproduction, revised completion-status prose and
eventual hosted checks are separate assembly evidence, not claims made by
this binding.

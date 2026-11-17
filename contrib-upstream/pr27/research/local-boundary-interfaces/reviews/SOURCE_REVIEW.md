# Source and application review

Date: 2026-11-10. Reviewer: Codex agent
`/root/normalization_source_review`, an internal model reviewer distinct from
the author/integrator `/root`. The exact model identifier is not exposed in
this review's tool metadata. This is a separate-agent, same-model-environment
review, with shared source material and possible correlated errors; it is not
external human or specialist acceptance.

**Decision: accepted within the stated conditional-interface source and claim
scope.** The four selected modules and final `README.md` / `APPLICATION.md`
make useful, correctly bounded deductions from their explicit premises. No
proof-source change is requested. This decision does not accept the complete
arithmetic instantiation, determinant switch, restricted converse, or main
Diophantine theorem. It does not certify the native runner, its caches, or a
build outcome. The execution and code-review lanes are separate.

The exact reviewed input hashes and this report's hash are in
[SOURCE_REVIEW_INPUTS.json](SOURCE_REVIEW_INPUTS.json). Changes to a bound
source or claim require a new reviewer decision. At review time these additions
were local and uncommitted; this is not a publication or merge authorization.

## Material read and checked

- All four selected Lean modules, their declared imports, `TARGETS.json`,
  `ORIGIN.json`, and the final package README/application note.
- The canonical V13 passages bound by ORIGIN: conjugate coefficients, H12,
  H20–H22, derivative local pairings, the actual paired functional and coordinate,
  retained inner diagrams, the switch, and its lower-bound consumer. The
  manuscript SHA-256 is
  `9db71bbfcefb37db56eabcf40a5f9dd85de9ed58294635da3dbf6d4f5caa8fcd`.
- The historical local-transport derivation/application, actual-boundary-cup
  derivation, and orthogonal-comparison derivation at research source
  `33483f751e6dcd3f91fb303969838aca33ad0458`. Their substantive arguments were
  read, rather than relying on earlier PASS labels. Their broader status prose
  is not adopted as current whole-arithmetic acceptance.
- Mathlib's actual `H1`, `H1π`, kernel theorem and induction principle in
  `LowDegree.lean`, and the right-composition and homology consequences of
  `Homotopy` at the pinned Mathlib revision. This checked the meaning of the
  imported interfaces, not every transitive proof or binary artifact.
- Jan Nekovář, *Selmer complexes*, Astérisque 310 (2006), published edition:
  §§1.3.1–1.3.2 (mapping-fibre product), §6.3.1 (compact-support target and
  local-invariant trace square), and §§7.1.1/7.2.1 (tame/Frobenius convention),
  using the retained published source. PDF SHA-256:
  `61c84e5ad3252a2e520747215ac57a282addc2b58c824a3637bcd77bbe02153f`.
  This is a targeted primary-source comparison, not a new review of the full
  global duality theorem, all its applications, or an exhaustive errata search.
- The repository contribution and audit/research-review protocols, and the
  selected submission scope. The latter fixes a four-module, non-release PR
  and excludes the wider determinant/limit/descent programme.

Read-only hash checks confirmed all four source SHA-256 and Git-blob identities
against ORIGIN, the whole manuscript and all 11 bound manuscript excerpts,
and the declared pin/protocol hashes. The source-bound support file hashes
also match. The target inventory has 41 explicit proof roots, including two
homotopy-valued definitions, and 16 definitions to print. Inventory agreement
is not a successful Lean execution claim.

## Independent check of the deductions

**Conjugation and H¹.** From φ=dτ and T(φ)=T(τ), cancellation in the
representation gives T(d)=1. Hence the twisted action of d⁻¹ is the scalar
u=α(d)⁻¹. Expanding the crossed-cocycle equation gives

```math
p(a^{-1}xa)=\rho(a^{-1})\bigl(p(x)+\rho(x)p(a)-p(a)\bigr).
```

The extra term vanishes only at trivially acting elements. Conjugation fixes
φ² up to d-conjugation and sends tame inertia to its ℓth power up to that
same d-conjugation. Therefore the finite/singular coordinates are
(u f,u ℓ s), with a single unit for every cocycle. The stated minus-one
formula additionally requires (ℓ:R)=−1. There is no primitivity, field, or
division-by-two requirement.

A coboundary evaluates to zero at a trivially acting element. This supplies
the kernel inclusion needed for descent through Mathlib's genuine H¹
projection. Pullback takes values in the pulled-back representation, and
pulls a coboundary to a coboundary there. The code and application correctly
keep those two coefficient carriers distinct. This proves an abstract-group
H¹ identity; continuity and a common arithmetic finite quotient are not
constructed by these Lean files.

**Boundary cup.** With dl=0, the degree-(1,0) Leibniz identity gives
d(l cup q)=−l cup dq. Substituting the cycle equation
inc u=loc g+dq gives the stated correction, and applying the supplied trace
kills it. The degree-(0,1) identity gives the other-slot boundary invariance.
No boundary-duality adjunction is assumed under another name. The formal
interface is degreewise and uses supplied cup/differential maps; it does not
construct Selmer cohomology, the actual coefficient-valued cup, or its trace.

**Comparison.** In H22's convention the third components of D'j and jD
differ by inc u−inc'a u−dh u−hdu, which vanishes by the displayed homotopy
equation. Thus the degreewise map preserves the global projection literally.
The separate genuine-complex result follows by postcomposing
k≫j homotopic to id with the target global projection q and using j≫q=p.
Postcomposition by localization preserves that homotopy and its equality on
homology. This requires a supplied right homotopy inverse; it does not
construct one or assert equality of individual local-condition coordinates.

The H22 coordinate q_H and boundary-cup coordinate q_N satisfy q_N=−q_H.
Transforming both the input and output local coordinate gives the two
displayed differentials and changes q_H+h u to q_N−h u. The final docs retain
this sign conversion. No finite/singular triangle isomorphism is needed.

## Exact consumers and arithmetic boundary

All line references below are to the bound canonical V13 source.

| Selected module | Relevant source construction and consumer | What remains an arithmetic application input |
| --- | --- | --- |
| `ConjugateLocalTransport.lean` | `ex:arith-conjugate-duality`, 2898–2967; H12, 3225–3233; same-coefficient H20–H21, 3339–3417; derivative local model, 3431–3508. These supply local conjugate coordinates for the paired-functional and switch consumers. | The actual twisted representation, normal subgroup, compatible generators, good odd derivative prime, character triviality, and common quotient preserving both classes and the exact tame relation. J belongs once in the coefficient pairing; raw pullback does not insert it again. |
| `ConjugateLocalH1.lean` | H22, 3509–3542, supplies actual finite continuous representatives. `ex:limits-inner-limit`, 4577–4636, is the separate retained-diagram route. The output is used when computing the conjugate partner in `ex:arith-paired-functional`, especially 3873–3891. | Identify the arithmetic classes and coordinate maps with the formal H¹ objects. For later use, retain the same unit and inverse with the same diagram. The fixed-prime premise ℓ=−1 cannot be instantiated directly in characteristic zero; no nonflat H¹ base-change theorem is proved here. |
| `ActualBoundaryCup.lean` | H22 fixes the cycle relation; `ex:arith-paired-functional`, 3873–3891 and 3979–3999, defines the actual duality row. The common strict boundary directions and their consumer occur in `ex:limits-derivative-switch`, 5021–5093. | Identify actual local cup maps, the closed orthogonal partner, pure connecting representative, one compact-support product/trace and the local-invariant square. An ordinary global H³ trace or an independently rescaled row cannot replace these objects. |
| `OrthogonalComparison.lean` | `ex:arith-paired-functional`, 3842–4012, gives the source comparison and its integral regimes; 3979–3999 defines j⁻¹c(z). The added singular condition is compared at 5351–5373 in `ex:limits-uniform-lower-bound`. | Supply local maps/homotopies in all degrees and the actual integral or localized right inverse. The generic inverse alone does not prove integral preservation. The preserved object is the localization of the global cohomology class, with the local-condition component related to it by the cone cycle equation. |

The final application correctly distinguishes the actual functional loci from
`ex:arith-coordinate`, 4014–4029: the latter defines the class-functional
determinant coordinate, not an explicit stored-row matrix construction.

The manuscript already states and argues the relevant source constructions.
For example, 3893–3911 separates completed dyadic group-ring representatives
from primitive height-one representatives, and 3974–3999 constructs the
integral comparison/closed lift over the stated completed group ring. The
singular comparison is separately argued at 5351–5373. These are not newly
identified omissions. This review checks how the selected formal deductions
relate to those passages; it does not certify that all required arithmetic
data across all supports, limits and localizations have now been completely
constructed and externally verified.

## Nine obligations and claim limits

The nine entries in APPLICATION are appropriate for this conditional-interface
record. In particular:

1. The formal premises, rather than a renamed target normalization, are explicit.
2. Constructed units/H¹ maps, degreewise cup equalities, and genuine homotopies
   are distinguished from arithmetic Galois/Selmer constructions.
3. Universal quantification on fixed formal data is not silently enlarged to
   every arithmetic support or localization.
4. Pullback direction, the two cone signs and the right-inverse direction are
   accounted for. Localized homology is distinguished from literal cochains.
5. The intended downstream partner is the source's j⁻¹c(z), not an arbitrary
   functional with a convenient scalar. Its matrix/row realization is outside
   this selection's asserted conclusion.
6. Finite-stage hEll, the integral unit, coefficient twist and single J are
   kept visible. There is no characteristic-zero specialization shortcut.
7. Good odd derivative conditions and the various other local comparisons
   remain explicit source inputs, not consequences of abstract group theory.
8. Zero/divisible vectors and characteristic two are allowed by these identities.
   Their validity does not create an inverse at a forbidden localization.
9. The exact determinant and lower-bound consumers are identified, while
   completed arithmetic normalization, lattice/torsion comparison, exceptional
   cases and universal descent are not accepted by this packet.

The completed dyadic and primitive height-one regimes are genuinely different
source applications. In particular, integrality of the paired cochain over
the completed dyadic ring does not by itself make every determinant coordinate
integral: the terminal minor divisor at 5144–5157 gives the separate lower
bound. This package does not assert otherwise, and proving a universal
derivative theorem over all coefficient regimes is not a merge requirement
silently added by this review.

Two presentation findings were resolved before this binding: the functional
and coordinate locators are now distinguished, and obligation 9 preserves
the separate status of existing ordinary/source-relative arguments instead
of implying that they do not exist. These were attribution/scope clarifications,
not new mathematical repairs to the four selected modules.

## Non-release and evidence scope

The non-release classification is appropriate: this is an additive extraction
of exact helper-module bytes with a bounded application map, not a new
manuscript edition, mathematical repair promoted into V13, or research release.
The observed working-tree changes were new `lean/Research/` and
`research/local-boundary-interfaces/` files, with no tracked-file modification.
Accordingly, manuscript/PDF regeneration, mirror synchronization and a new
global release handoff are not required by this change. They remain duties of
any later release that incorporates a larger mathematical claim. The frozen
39-target foundation's evidence does not certify these 41 selected roots.

This reviewer did not run Lean, paranoid/external checkers, the finite controls,
or the native runner, and did not inspect final execution receipts. Pending
`VERIFICATION.md`, findings integration, PR text, code review and hosted check
outcomes are not approved by this source review. No additional arithmetic
formalization, manuscript acceptance, novelty, or external-referee confidence
should be inferred from the decision above.

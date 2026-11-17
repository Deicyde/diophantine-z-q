# Arithmetic instantiation contract — not discharged by this packet

Consumer: the derivative-switch lemma and the rank-one inner-instance
coordinate preservation used in the uniform-bound/height-one arguments.
Source snapshot: `40d01c53b3545a62949b14669c4906d3e978110e` in the owner's fork.

## What the algebra supplies

Given a common-strict two-term presentation and its actual cycles/closed rows,
the ordinary theorem derives the determinant coordinate discrepancy. Candidate
Lean modules implement that inference without taking the discrepancy formula
or the desired unit comparison as a hypothesis. Formal compilation is pending.

## What must come from the arithmetic source

| Obligation | Exact required content | Status here |
|---|---|---|
| Integral source | The two actual integral cone triangles, their retained determinant bases and a compatible common-strict two-term presentation, or a proved determinant-functor bridge to it | Not instantiated |
| Generic scope | Each inner constituent has rank-one H1/H2 and nonzero actual finite localization; do not substitute the rank-dropping outer object | Explicit applicability restriction |
| Old/new classes | zF is the actual old class; zS is the actual H19--H22 derivative with local component Jv and the same fixed multiplier | Not instantiated |
| Functionals | lambdaF/lambdaS are the actual rows produced by the retained conjugate/orthogonal/global-duality constructions | Not instantiated |
| Closedness | The two rows annihilate their own actual differentials; no independent primitive rescaling | Required by CommonStrictData |
| Boundary independence | The common strict quotient and the self-annihilator image yield the nonzero target determinant theta | Ordinary source bridge identified; not formalized here |
| Local J | The integral isomorphism is transported in the actual bases, det(J) is an R-unit, and J^2=1 for the stated beta convention | Local algebra input, no new arithmetic proof |
| Boundary--cup naturality | For ALL local s,f, the actual rows satisfy the two identities in BoundaryCupIdentity, with compatible cone/cup signs | Core arithmetic obligation |
| Normalization | The constants cF,cS in these identities coincide, or differ by an actual integral unit. They need not be individually units | Core arithmetic obligation |
| Localizations | The above hold at the completed 2-adic DVR and every required height-one localization, including the exceptional (t)/(t+2) tests | Not established by generic-field algebra |
| Limits | Actual classes, rows, bases and identities are retained through the specific inner constructions; no generic isomorphism is silently promoted to an integral/outer one | Not checked here |

## Typed adapter

The adapter consumes the SAME rows in CommonStrictData and requires

    lambdaF(AS s) = cF * beta(v,s)       for every s,
    lambdaS(AF f) = -cS * beta(f,Jv)     for every f,
    beta(f,s) = epsilon * area(f,J s),
    J*J = 1.

It derives qF=cF*epsilon*eta and qS=cS*epsilon*eta. It then derives the
coordinate ratio -cF/cS, when defined, or the division-free common-normalization
comparison. It does not accept qF=qS or determinant preservation as an input.

In source-level cohomology, AS and AF here mean the actual boundary directions
followed into the other degree-two cohomology group and evaluated by its closed
functional. A model must identify these with the matrix representatives; an
abstract pairing with similar dimensions is not enough.

## Prohibited substitutions

- A quasi-isomorphism CF ~= CS fixing the strict complex is not a premise.
- The local determinant det J=-1 does not fix the boundary--cup normalization.
- IsUnit in the generic field does not mean an integral unit.
- Equal generic dimensions do not prove the actual functionals are compatible.
- A common nonunit clearing factor may cancel; two unrelated clearing factors
  may not be discarded.
- A proof of the six earlier boundary/volume lemmas does not prove this adapter's
  arithmetic hypotheses.
- This source-level verification gap is not, by itself, a finding that the
  manuscript has no such justification or that its conclusion is false.

## What would close this contribution's arithmetic application

A source-pinned proof identifying the actual matrices/classes/rows, deriving the
two boundary--cup identities with their same normalization and checking the
required rings supplies the remaining application. Until then this is an
explicit conditional connecting theorem, not an accepted determinant-switch
proof or a proof of the restricted converse.

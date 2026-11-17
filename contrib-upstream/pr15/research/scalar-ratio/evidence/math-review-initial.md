### 1) Verification target

**Initial mathematical decision: CERTIFIED under the explicit raw common-strict hypotheses.** The raw-frame formula, adjugate-based uniqueness including zero tensors, integral-unit equivalence and same-row conditional boundary-cup consequences are correct. **Formal acceptance remains pending:** compilation, elaborated definitions/types, repaired candidate interfaces and the final combined challenge have not been checked by this reviewer in this round.

Date: 2026-11-08. Reviewer: non-author Codex model agent
`/root/boundary_scalar_math_review` (GPT-6-family host identity; exact
serving-model identifier unavailable). This is the same reviewer agent as
the preceding boundary-scalar review, so reuse of that earlier review is
a repeat/source-identity check, not another independent review of the old
21 declarations. This agent did not author the supplied milestone or its
Lean proofs. The integrator and proof authors supplied intended targets
and implementation updates. Shared models, context and source material
can create correlated errors; no human or blind review is claimed.

Tools used: shell/file inspection, Git read-only inspection, SHA-256 of
raw bytes, exact standard-library Python, and this report write. No Lean
build, axiom audit, export replay, protected comparison, cloud/paranoid
run, repository source edit, manifest change, commit or push was performed
by this reviewer. The math-verifier skill was applied. The repository
research-review and audit-integration protocols were read; their bytes
remain the same as in the preceding review.

Repository: `/Users/chey/Coding_Projects/diophantinezq/derivative-switch-review`.
Base commit: `bc2f21120c1b090a279c7b56675caa0e502584e1`. The four new
working modules and new packet are untracked additions at this stage;
the commit does not identify their evolving bytes. All hashes in this
report are SHA-256 of the original raw bytes, without normalization.

Received root:
`/Users/chey/Coding_Projects/diophantinezq/audit-output/2026-11-08-scalar-ratio-milestone-intake/received/scalar_ratio_milestone`.
Its four source candidates were read and compared with the working
copies. The preserved input notes match their received originals byte
for byte.

| Received source under `lean/Research/DerivativeSwitch/` | Original SHA-256 |
| --- | --- |
| `Coordinate.lean` | `e0cfbefd5d95f0673730735bb2b241dc70db0225b9c13c715c9d580e455f27ab` |
| `CommonStrict.lean` | `53d581522547747a974d8ee656df017b1c31c73433c090a4b6b301869e11ec2a` |
| `UnitCriterion.lean` | `6221cbbf16b0af8f3a69205d2a8fa24cb60dd593f60605643224707d257d10e6` |
| `BoundaryCup.lean` | `4059d2ed9013233c0b5a655ae2a29b9d27d0ed6b111d8d8bbc3035d55818727a` |

| Working source most recently inspected | SHA-256 |
| --- | --- |
| `lean/Research/DerivativeSwitch/Coordinate.lean` | `229e66269880b9970b15ca36fab290d2572fdfac7396383d3327e652128ade90` |
| `lean/Research/DerivativeSwitch/CommonStrict.lean` | `32ad10991351015134939247f57f200f684e267fe05ecf233cc2a1d38c82d3f8` |
| `lean/Research/DerivativeSwitch/UnitCriterion.lean` | `efd9f4404b9760f9d7ebc2cb0874f21f517ed3868e9e23f78fd0465a2c03e45a` |
| `lean/Research/DerivativeSwitch/BoundaryCup.lean` | `bad8020f783cd2e7dd52f0b48ec951af65e6fe1a9a4f11c6c9aa432ef9057ab5` |

The initial read preceded compiler-author repairs. Its working hashes
were respectively `5120df26ab20ee90931c036162f98bf4bfdbbe82b4c120bc6d3319e79aa88453`,
`0c19da89ddb2e2aa30426679ee12b711081b7aa6aa8619f5a1fd4da2989f49d3`,
`d7f23ca5c934ab53e90e5ea9ae3e75ae0790603910cd04f10e9cb5456bd5ff47`,
and `bad8020f783cd2e7dd52f0b48ec951af65e6fe1a9a4f11c6c9aa432ef9057ab5`.
These are recoverable from the originals by replacing the one
`SOURCE-COMPLETE CANDIDATE...` header line with the two lines
`Received as an uncompiled candidate. Current verification is recorded in`
and `` `research/scalar-ratio/VERIFICATION.md`. ``. I verified that this
byte transformation reproduces all four initial hashes. Subsequent
working-source differences were inspected, including the split structure
fields described in Section 4. These changing snapshots are not a final
compiled-source binding or approval of future edited bytes.

| Other reviewed input or proposal | SHA-256 |
| --- | --- |
| `research/scalar-ratio/inputs/MATHEMATICS.md` | `605cc706a743774fab96b85ff218a0e9113b91a39dd10b3b2981a73057ac4ce2` |
| `research/scalar-ratio/inputs/ARITHMETIC_CONTRACT.md` | `99e5dbbc3e1c5eb71e98350ca0955cd045d4cdeaab800b20c1023588144a3f9a` |
| `research/scalar-ratio/inputs/HANDOFF.md` | `4bf00c2958489d5198b5faccaf387838ffdb4e934ec48df9b6b4fe55f4ab7f10` |
| `research/scalar-ratio/CONTRACT.md` | `7d7d69aa9fb2cae043ba29c93a0de5099ad552d387e1f53b09f9f58909cc4aca` |
| `research/scalar-ratio/DERIVATION.md` | `02fbb34ccd76ff3d3894b812416b722cf6f044322d16d35b4d0f11e39561e733` |
| `research/scalar-ratio/PLAN.md` | `fdfdcb6bac5480d41a68882ec4dc4bea7a967d16e992887ebe462264ce8b4de8` |
| `research/scalar-ratio/README.md` | `15d21ed9fd9f3a5c42fa802a71a427221da704fc22048b2b62d468e3ef54b302` |
| `research/scalar-ratio/verification/comparator.json` | `ae8b3b382cfc69d3aceb281c188548923855345a71f3775b813530ca059f00c8` |
| `research/scalar-ratio/tests/check_milestone.py` | `7bf9326d4ba799a561fdeefcdb1d9dd5b887511fa61ed56b12c9ebd9369de59a` |
| `research/scalar-ratio/tests/exact_matrix.py` | `fac50661ebbd4e57e93db2dbf8bb01ba10c6fd3cd93eb5cedfd8ee8a476f87a1` |

**Lookup and relation to earlier coverage.** I read the actual relevant
definitions/proofs in `lean/Research/BoundaryScalar.lean` (raw hash
`fd1ea9ca11a417072c7be08ef477901427c57a74962559d753d62db95883f3ef`)
and `lean/Research/BoundaryCupAdapter.lean`
(`330699edaab6812ed68ed09a5fb682ad1d6b3af5a030a252691723066beffd7b`),
rather than using their favorable verdicts. Those source bytes are
unchanged. The old matrix theorem accepted normal-frame equations and
basis determinants; the new CommonStrict construction derives them from
raw matrices, cycles and a complement. The old uniqueness consumer used
a nonzero tensor; the new one uses a nonzero adjugate and covers zero
rows. The old ring-homomorphism unit result was sufficient and required
a nonzero denominator; the new `Subring K` equivalence includes both-zero
and one-zero cases. The old abstract cup adapter worked over a commutative
ring, arbitrary modules and arbitrary equivalence using `J.symm`; the
new matrix-facing adapter specializes to a field, the fixed coordinate
plane, the area form and an involutive matrix J. It is more integrated,
not more general in every parameter.

The current owning manuscript passage `ex:limits-derivative-switch`,
lines 5020–5093 of `manuscripts/quartic_v13.tex`, was reread. The whole
source hash remains `9db71bbfcefb37db56eabcf40a5f9dd85de9ed58294635da3dbf6d4f5caa8fcd`;
Git confirms it is unchanged from the supplied source baseline
`40d01c53b3545a62949b14669c4906d3e978110e`. Earlier review in this same
task inspected the adjacent H12/H19–H22 and actual paired-functional
construction under those identical bytes. That bounded source/history
lookup remains applicable; it is not a fresh whole-paper or primary
Nekovar audit. Historical classification is **prior algebraic components
located; raw construction/zero-case extensions supplied here; arithmetic
source application unresolved in this review**. Manuscript incorporation
of this new milestone is **pending/not attempted**. No newly discovered
whole-manuscript refutation is claimed.

### 2) Independent re-derivation (outline)

Let `m=|I|`, `n=m+2`, `DF=[D0|AF]`, `DS=[D0|AS]`, with actual
cycles `zF=(hF,v)`, `zS=(hS,Jv)`, closed rows `lambdaF,lambdaS`,
`eta=det[v,x]!=0`, and `theta=det[D0,a,b]!=0`, where
`a=AF x`, `b=AS Jx`, `delta=det J!=0`.

**Direct cofactor derivation, deliberately independent of the candidate's
one-diagonal-normal-form decomposition.** Define target covectors

```text
rhoF(y)=det[D0,a,y],       rhoS(y)=det[D0,y,b].
```

The basis `T=[D0,a,b]` and closedness imply, including zero rows,

```text
lambdaF=(qF/theta)rhoF,       lambdaS=(qS/theta)rhoS,
qF=lambdaF(b),                qS=lambdaS(a).
```

For `BF=[I,zF,(0,x)]`, `det BF=eta` and `DF BF=[D0,0,a]`.
For any source row `r` and target vector `y`, multilinearity gives

```text
det(DF+t y r)=-(t/eta)r(zF)rhoF(y).
```

Only the zero class column can contribute its perturbation; any second
perturbed column repeats `y` and gives zero. Comparing the linear
coefficient with `r adj(DF)y` gives
`adj(DF)=-(1/eta)zF rhoF`. The singular calculation with
`BS=[I,zS,(0,Jx)]`, determinant `delta eta`, gives
`adj(DS)=(1/(delta eta))zS rhoS`. Therefore

```text
zF lambdaF=(-eta qF/theta)adj(DF),
zS lambdaS=(delta eta qS/theta)adj(DS).
```

No cancellation of qF or qS occurs. This proves both coordinates even
when either or both rows vanish. The invertible target includes independent
`D0,a,b`; with the nonzero cycles it forces each differential's rank to
be `n-1`. Thus each adjugate is nonzero. If two scalars describe any
fixed tensor, subtracting the two full identities and evaluating a
nonzero adjugate entry gives equality of scalars. This argument applies
to the zero tensor, whose unique coordinate is zero. It does not require
the tensor itself to be nonzero.

**Independent check of the new raw frame construction.** The candidate's
alternative presentation is also correct:

```text
TF=[D0,b,a],     TS=[D0,a,b],     N=diag(I_m,0,1),
DF BF=TF N,     DS BS=TS N,
det TF=-theta,  det TS=theta,
lambdaF TF=qF e_p^t,             lambdaS TS=qS e_p^t.
```

These equalities follow column by column: strict columns give D0, the
actual-cycle column gives zero, and the last source column gives AFx
or ASJx. The spare target column is killed by N; `raw_frame_identity`
correctly permits an arbitrary vector there. Closedness determines
the remaining row coordinate. Since `adj N=e_p e_p^t`, the frame
coordinate is q. Adjugate multiplicativity transforms it by
`det B/det T`, recovering the formulas and finite-side minus sign.
The strict factor is retained throughout; no integral invertibility of
the source frames or strict minors is assumed.

**Integral-unit equivalence without dividing by either cross evaluation.**
For a specified subring `R` of K, define
`a ~_R b` by `a=e b` for an actual `e` in `Rˣ`. Put
`c=delta eta/theta`, which is nonzero. Then

```text
delta uF=c(-qF),       uS=c qS.
```

Multiplication by any common nonzero field scalar preserves the witness
unit in both directions, even if that scalar is not a unit in R.
Multiplication by -1 also preserves the relation. Hence

```text
UnitRelated R (delta uF) uS ↔ UnitRelated R qF qS.
```

To remove delta from the left side one needs its explicit lift to `Rˣ`.
With that lift, `UnitRelated R uF uS ↔ UnitRelated R qF qS`. Both
arguments zero satisfy the relation using unit 1; exactly one zero
cannot satisfy it because images of R-units are nonzero. No statement
that a quotient `0/0` is an arithmetic ratio is needed or made.

For qS nonzero the ordinary quotient is defined and the formulas give
`delta uF/uS=-qF/qS`. The division-free relation
`qS(delta uF)+qF uS=0` holds without that premise. The formal
multiplicative-map consumer merely applies a homomorphism trivial on
R-unit images to a unit witness. This correctly covers ordinary
multiplicative valuations; it is not a formal additive-DVR equivalence.

**Same-row cup adapter.** In the fixed common coordinate plane, J acts
on both arguments and `J^2=1` is an explicit premise. For the exact
stored rows, the two universal identities give

```text
qF=lambdaF(AS Jx)=cF epsilon area(v,J(Jx))=cF epsilon eta,
qS=lambdaS(AF x)=-cS epsilon area(x,J(Jv))=cS epsilon eta.
```

Thus the normalization defect is `-cF/cS` when epsilon and cS are
nonzero; eta is already nonzero. cF may be zero. For cF=cS the
division-free calculation gives `delta uF=-uS`, including common
normalization zero. If delta=-1 it gives `uF=uS` in this cofactor
orientation. A unit ratio of normalizers, plus the R-unit lift of delta,
gives `UnitRelated R uF uS`, including zero rows. `BoundaryCupIdentity`
does not take qF=qS, coordinate equality, or valuation preservation as an
input. Its universal evaluations use the literal `d.lamF,d.lamS`,
`d.AS,d.AF`, rather than newly normalized functionals.

**Complement independence.** The actual cycle equations give
`AF v=-D0 hF` and `AS Jv=-D0 hS`; both closed rows kill D0. Thus the
cross maps vanish on v. For any other complement `x'=r x+s v`, `r!=0`,
multilinearity gives `eta'=r eta`, `qF'=r qF`, `qS'=r qS`,
`theta'=r^2 theta`. The formulas for both coordinates are unchanged.
This verifies the ordinary derivation's quotient/complement assertion;
the packet accurately does not advertise a separate Lean quotient or
complement-independence theorem.

### 3) Checks

**Plug-back and hypothesis checks.**

| Target | Check and result |
| --- | --- |
| Coordinate definition | `tensor z lam i j=z i*lam j`; `HasCoordinate` is the entire matrix identity with adj(D), independently defined before the desired formulas. |
| Frame direction | `D B=T N` gives old coordinate `(det B/det T)*q`; the inverse direction would be wrong. Both candidate transport proof and direct derivation use the correct direction. |
| Raw data | D0 has arbitrary finite column index I and row index `I⊕Fin 2`; AF and AS have the actual two local columns. The block frame includes the actual hF/hS and v/Jv, not primitive replacements. |
| Rank/uniqueness | Nonzero area and target determinant construct genuine field-unit frames. They force nonzero adjugates before `coordinate_unique` is used, independently of the rows and their tensors. |
| Unit ring | `R : Subring K`, `unitValue R e=R.subtype(e.val)`, `e:Rˣ`; this is an actual unit of the chosen coefficient ring, not generic-field `IsUnit`. |
| Actual coordinates | `CommonStrictData.coordinate_values` accepts separately supplied `HasCoordinate` witnesses and proves their values using uniqueness. It does not define them to be the output formulas. |
| Same rows | The cup structure refers to the rows of that same CommonStrictData. Changing only one row changes the input or invalidates its fixed adjunction constants. |

**Boundary cases and necessity controls.**

| Case | Result / scope |
| --- | --- |
| Empty I (`m=0,n=2`) | The strict source is zero, strict target remains K², and both normal-frame/adjugate arguments work. |
| One-dimensional auxiliary Coordinate lemma | A supplied index k forces nonempty index type; for a singleton, normal is the 1×1 zero matrix with adjugate one. Main CommonStrict uses size at least two. |
| Divisible v, fractional x, nonzero strict h | Frame determinants are eta and delta eta regardless of h; field invertibility is sufficient. No integral complement is introduced. |
| Common strict nonunits/torsion | D0 remains in theta. Common factors cancel only in the proved coordinate comparison; no cohomology torsion summand is discarded. |
| Zero rows | Formula and uniqueness yield coordinate zero. Both-zero UnitRelated is true; either one-zero case is false. |
| Rank-zero matrix outside hypotheses | For 2×2 D=0, adj(D)=0; a zero tensor then satisfies HasCoordinate for every scalar. This demonstrates why the nonzero adjugate/frame premise is essential. |
| Missing R-unit determinant lift | Over Z_(2), `delta=2`, `uF=-1,uS=2,qF=qS=1` gives transported unit-related coordinates but untransported coordinates of different valuations. One realization has `J=diag(2,1)`, DF=`[[0,1],[0,0]]`, DS=`[[0,0],[0,1]]`, `v=e1`, `x=e2` and `zS=2e1`. The integral-isomorphism/unit-lift guard is essential. |
| Characteristic two | Alternation and the column-swap sign still hold, with -1=1. No division by two or characteristic-zero restriction is used in these algebraic theorems. |
| c=0 or epsilon=0 | The full adjunctions force both cross values zero in the common-normalization case; exact equality uses no cancellation of that common factor. Defect quotient theorems explicitly exclude zero epsilon/cS. |
| v=0 or acyclic constituent | Excluded by eta!=0. The zero-functional extension does not prove these different branches of the arithmetic manuscript. |

**Supplied finite suite, inspected and replayed.** Python 3.13.12 commands
from the repository root:

```sh
python3 -B research/scalar-ratio/tests/check_milestone.py
python3 -B -O research/scalar-ratio/tests/check_milestone.py
```

Both exited zero, producing byte-identical 1,247-byte JSON, SHA-256
`e2d141099503d845ec240d1c85d7323a8d909c06b2a5540457acec92c48426e6`.
Observed new controls: 180 adapter cases in sizes 2–6, 720 basis-level
adjunction checks, 540 prime-specific unit-criterion checks, 180 complement
changes, 60 equal-normalization cases, 90 zero-functional cases, 121
common nonunit clearings, 90 wrong-functional rejections, and 179
non-eigenvector local cases. The old 300-case regression is also rerun.
All checks use explicit exceptions, so optimization does not disable them.
The arithmetic utilities are exactly the preceding checker, hash
`fac50661...`; these reruns are not independent checker implementations
and finite samples do not prove the universal theorem.

**Independent small exact control.** I separately used only the direct
2×2 adjugate formula and exact rationals, without importing either supplied
checker. Inputs were

```text
J=[[0,1],[1,0]], v=(2,4), x=(1/3,-1/5), eta=-26/15,
AF=[[-4,2],[0,0]], AS=[[0,0],[-2,4]],
lambdaF=(0,-cF epsilon), lambdaS=(cS epsilon,0),
cF in {0,1,2,-3}, cS in {0,1,2,3}, epsilon in {0,5}.
```

All 32 cases passed full outer-product identities, both adjunctions on
the two local basis vectors, unit equivalence at primes 2,3,5, and the
defined ratios. There were 23 cases with at least one zero evaluation,
12 defined-ratio cases, and a non-eigenvector actual v. Independent
controls also confirmed the determinant-unit and adjugate-nonzero
necessity examples above. The complete small reproduction is preserved
here; run without optimization. Its finite scope is supplementary to
the independent general derivation, not a theorem certificate.

```python
from fractions import Fraction as Q
from itertools import product

def need(b,s):
    if not b: raise RuntimeError(s)
def area(v,x): return v[0]*x[1]-v[1]*x[0]
def mv(A,v): return [sum((a*b for a,b in zip(row,v)),Q(0)) for row in A]
def adj(A): return [[A[1][1],-A[0][1]],[-A[1][0],A[0][0]]]
def tensor(v,l): return [[x*y for y in l] for x in v]
def coord(D,z,l,u): return tensor(z,l)==[[u*x for x in row] for row in adj(D)]
def vp(q,p):
    q=Q(q); need(q!=0,'vp zero')
    def count(a):
        c=0
        while a%p==0: a//=p; c+=1
        return c
    return count(abs(q.numerator))-count(q.denominator)
def related(a,b,p):
    return (a==0 and b==0) if (a==0 or b==0) else vp(Q(a)/b,p)==0

J=[[Q(0),Q(1)],[Q(1),Q(0)]]; v=[Q(2),Q(4)]; x=[Q(1,3),Q(-1,5)]
AF=[[Q(-4),Q(2)],[Q(0),Q(0)]]; AS=[[Q(0),Q(0)],[Q(-2),Q(4)]]
eta=area(v,x); need(eta==Q(-26,15),'area')
a=mv(AF,x); b=mv(AS,mv(J,x)); theta=area(a,b)
count=zero_cases=ratio_cases=0
for cF,cS,eps in product([Q(0),Q(1),Q(2),Q(-3)],
                         [Q(0),Q(1),Q(2),Q(3)],[Q(0),Q(5)]):
    lf=[Q(0),-cF*eps]; ls=[cS*eps,Q(0)]
    qF=sum(y*z for y,z in zip(lf,b)); qS=sum(y*z for y,z in zip(ls,a))
    uF=cF*eps; uS=cS*eps
    need(coord(AF,v,lf,uF) and coord(AS,mv(J,v),ls,uS),'full coordinates')
    need(uF==-eta*qF/theta and uS==-eta*qS/theta,'formula signs')
    need(qF==cF*eps*eta and qS==cS*eps*eta,'cross evaluations')
    for e in [[Q(1),Q(0)],[Q(0),Q(1)]]:
        need(sum(y*z for y,z in zip(lf,mv(AS,e)))==
             cF*eps*area(v,mv(J,e)),'finite adjunction')
        need(sum(y*z for y,z in zip(ls,mv(AF,e)))==
             -cS*eps*area(e,mv(J,mv(J,v))),'singular adjunction')
    for p in [2,3,5]:
        need(related(uF,uS,p)==related(qF,qS,p),'zero-aware unit iff')
    if qS:
        need(-uF/uS==-qF/qS==-cF/cS,'ratio'); ratio_cases+=1
    if not qF or not qS: zero_cases+=1
    count+=1
need(related(Q(-2),Q(2),2) and related(Q(1),Q(1),2),'transported relation')
need(not related(Q(-1),Q(2),2),'delta unit guard')
D=[[Q(0),Q(2)],[Q(0),Q(0)]]; z=[Q(1),Q(0)]; zero=[Q(0),Q(0)]
need(coord(D,z,zero,Q(0)) and not coord(D,z,zero,Q(1)),'zero coordinate unique')
Z=[[Q(0),Q(0)],[Q(0),Q(0)]]
need(coord(Z,z,zero,Q(0)) and coord(Z,z,zero,Q(1)),'nonzero-adjugate guard')
need((count,zero_cases,ratio_cases)==(32,23,12),'coverage counts')
print('PASS cases=32 zero_cases=23 defined_ratios=12; units_at=2,3,5')
```

**Source-facing obligations.** The new contract is an appropriate
conditional application inventory. The mathematical matches and limits
are:

| Obligation | Required / constructed / decision |
| --- | --- |
| Source hypotheses | Raw square common-strict matrices, actual cycles, closed rows, nonzero area and target determinant are explicitly assumed; the scalar formula is derived. Actual arithmetic hypotheses remain to be identified/proved. |
| Constructed objects | `join`, `cycle`, block `frame`, target columns, tensor and coordinate predicate are concrete. Split fields store the independent old/new objects. Actual Selmer complexes, cochain maps and determinant functors are not constructed. |
| Domain/index coverage | Every finite I, including empty I, yields size m+2. The field result has no characteristic exclusion. It does not cover v=0, acyclic constituents or substitute the rank-changing outer object for rank-one inner data. |
| Transition/comparison maps | Raw column multiplication, area covariance, actual target swap and frame transport give the correct signs/scalars. The determinant-line interpretation of delta remains ordinary algebra; arithmetic naturality is OPEN. |
| Consumed object identity | Cofactor witnesses refer to the exact stored cycles and rows; cup identities consume the same ones. Relating them to the manuscript's conjugate/orthogonal/Poitou–Tate functionals remains OPEN. |
| Coefficients/normalizations | Core matrices are over K; no R-integrality is encoded by CommonStrictData itself. UnitRelated uses the specified embedded subring, and removal of delta needs its actual R-unit lift. Both common nonunit clearings and zero rows remain visible. |
| Local conditions | Common strict columns are retained; source local D0/D^0 identifications, integral cone presentations, homotopies and all required localizations are still arithmetic application obligations. |
| Exceptional cases | Zero rows, one-zero cases, nonunit common scales, minimal size and nonprimitive/fractional complements are checked. Nonzero area/target and determinant-unit guards cannot be dropped. |
| Downstream consumers | The exact ratio and unit iff can supply the conditional switch consumer. This packet alone supplies neither the arithmetic common normalization nor the manuscript's uniform bound, height-one application, restricted converse or release acceptance. |

The proposed combined configuration has exactly 39 distinct target names,
with the old 21 as an exact prefix and 18 new principal declarations. Its
definition-hole list is empty and allowed axioms are the conventional
three. This is an inspected inventory/configuration fact only; the
actual split challenge definitions, final elaborated 39 types and
execution evidence are reserved for final review.

### 4) Discrepancy report (if any)

**No mathematical discrepancy found in the intended formulas or guards.**
The direct cofactor derivation, one-normal-form construction, unit-witness
cancellation, complement change and same-row adapter agree.

**E1 — grouped structure-field syntax required correction.** The incoming
and first-read CommonStrict source used `AF AS : ...`, `hF hS : ...`,
`v x : ...`, `lamF lamS : ...` in a structure body. The compiler author
reported that this parses as a field with a binder, rather than two
independently named data fields. The latest inspected source explicitly
splits every field. That is the intended independent data of the
mathematical specification and is not an added normalization premise.
It is a real elaboration/interface correction, so the original candidate
cannot be described as having passed formal statement review merely
because its intended mathematics was sound. The repaired source-level
structure is correct, but its actual compiled structure and theorem types
must still be inspected in the final round.

Other observed changes are header/status clarification and local proof
elaboration repairs: simplification lemmas, explicit matrix block
expansions, explicit K/I parameters, proof conversions and local
elaboration/heartbeat settings. No weakened mathematical premise,
coordinate redefinition, primitive replacement or new mathematical axiom
was identified in the inspected source diff. This is not an axiom audit
or claim that those changed proof terms have compiled.

The explicit delta-unit and nonzero-adjugate countercontrols demonstrate
essential premises; they are not counterexamples to the stated theorems.
The primitive `(-1/2,1/4,2)` example still refutes only the weaker local-data
inference, not the arithmetic manuscript with its required compatibility.
The current arithmetic source obligations remain unresolved in this
bounded review; no claim that an earlier justification never existed is
made.

### 5) Certification result

**CERTIFIED, under the stated raw common-strict assumptions, as ordinary
mathematics and source-level intended specification:** the two full
cofactor formulas; nonzero-adjugate uniqueness including zero tensors;
division-free comparison; transported and untransported integral-unit
equivalences with their exact guards; same-row boundary-cup evaluations,
normalization defect and common/unit-normalization consequences; and
the ordinary complement-independence calculation.

**Formal acceptance: NOT YET CERTIFIED in this initial report.** The
grouped-field correction and evolving proof elaboration require a final
exact-byte reread against actual compiled definitions/types, transitive
axiom output and the combined challenge. No native/profile completion
is inferred from finite Python passes. No future source hash is accepted
in advance.

Actual arithmetic realization, source duality/naturality with the precise
normalizations, all retained limits/localizations, manuscript incorporation,
protected/Linux/paranoid or external checking, human acceptance and
release acceptance remain OPEN or unperformed in this review. The four
new modules do not silently enlarge the earlier freezes or accepted
48-module snapshot.

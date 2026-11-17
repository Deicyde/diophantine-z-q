### 1) Verification target

**Decision at intake: CERTIFIED under the supplied common-strict matrix assumptions, in the declared adjugate convention. Arithmetic instantiation remains OPEN.** The typed conditional boundary-cup adapter described below is also correct. This report does not accept a whole manuscript, assert mathematical novelty, supply human approval, or extend the six existing formal lemmas into arithmetic coverage.

Date: 2026-11-08. Reviewer: separately instantiated Codex model agent `/root/boundary_scalar_math_review` (GPT-6-family host identity; exact serving-model identifier is not exposed to this agent). This agent did not author the supplied theorem or the six-lemma packet. Available tools included read-only shell inspection, exact Python computation, and local filesystem report writing. No Lean execution, cloud dispatch, protected comparator, paranoid run, repository source edit, manifest update, commit, or push was performed by this reviewer.

This is a non-author model review, not evidence of epistemic independence: the task supplied the intended identities, source locations, prior scope decisions, and author-review context. I read the supplied statement and derivation and then deliberately re-derived it by a rank-one determinant-update argument. Models and shared context may have correlated errors. The author of `REVIEW_40d01c5.md` explicitly helped originate the earlier candidate; that report is an adversarial author re-review, not a new non-author acceptance.

The repository was inspected at clean commit `083344e84a231d9127d57589ae5c0b355384579b`. The supplied note is external to that commit. Every hash below is SHA-256 of the original raw file bytes, without normalization. The acceptance in this report is bound to the supplied note's exact hash and assumptions; it does not automatically accept later edited statements, Lean declarations, or integration prose.

| Reviewed file, relative to the named root | SHA-256 |
| --- | --- |
| Bundle: `review/BOUNDARY_SCALAR_LEMMA.md` | `5c72a9d2169bee1d9f0077d422ed0cb06913c61bf762e0976e822ef1c95dedb6` |
| Bundle: `review/REVIEW_40d01c5.md` | `83aaad88febd68e4b1916858547d90224ac9e62c11ceb173dc443adccef9f357` |
| Bundle: `review/check_boundary_scalar.py` | `fac50661ebbd4e57e93db2dbf8bb01ba10c6fd3cd93eb5cedfd8ee8a476f87a1` |
| Repository: `manuscripts/quartic_v13.tex` | `9db71bbfcefb37db56eabcf40a5f9dd85de9ed58294635da3dbf6d4f5caa8fcd` |
| Repository: `research/determinant-switch/CONTRACT.md` | `01be1c4182cd5c7483ad2253b93b975ddced22396372e726aa808614d525516b` |
| Repository: `lean/Research/DerivativeSwitchBoundary.lean` | `63a9215fa55568069d2d1a7b2c3a7345ec21c7ad6a82203f42c5451ee4b8bbea` |
| Repository: `docs/audit-history/issue2/evidence/determinants.md` | `648a83cfec26f3032dc75aa04be03870c1864173c60daed3ff082935db703bd5` |
| Repository: `research/determinant-switch/evidence/freeze-20261108/math-review.md` | `2ef8fa012497e738a63115f849446373990007b6d2cb0ce040707244c81a97e1` |
| Repository: `research/determinant-switch/evidence/freeze-20261108/final-review.md` | `fd9716ccfe80e15f6797bc703fd7da84e2ef50a3e0b3b3e8697aa56c96362ced` |

Repository root: `/Users/chey/Coding_Projects/diophantinezq/derivative-switch-review`. Bundle root: `/Users/chey/Coding_Projects/diophantinezq/audit-output/2026-11-08-boundary-scalar-intake/bundle`.

The governing files were read: `AGENTS.md` (`8962f442f897f69d6f001a589eeae22881bda75b77f1b77e7f30f3b7d50e0bfb`), `docs/research-review/PROTOCOL.md` (`b5365b3d9cd9a782bf7fd0b6020403d5d400eac13dc7e60875484a8769d3d925`), and `docs/audit-history/PROTOCOL.md` (`c0b9834a75e64bfd66183b06d1e26019f957a38468ce41b10ce290f8c5c44816`). I applied `/Users/chey/.codex/skills/math-verifier/SKILL.md`.

**Statement assessed.** Let `R` be a DVR, `L=Frac(R)`, `n>=2`, `m=n-2`, and `DF=[D0|AF]`, `DS=[D0|AS]`. The matrices are integral; `D0` has rank `m`; `J:F_R≃S_R` is integral with `delta=det J` a unit. The actual cycles are `zF=(hF,v)`, `zS=(hS,Jv)` with `v!=0`; the nonzero closed functionals are `lambdaF DF=0`, `lambdaS DS=0` over `L`. Choose any `x` with `eta=det[v,x]!=0`, and assume `T=[D0,AF x,AS Jx]` invertible, with determinant `theta`. Put `a=AF x`, `b=AS Jx`, `qF=lambdaF(b)`, `qS=lambdaS(a)`. Then the unique adjugate coordinates satisfy

```text
zF lambdaF = uF adj(DF),       uF = -eta qF/theta,
zS lambdaS = uS adj(DS),       uS = delta eta qS/theta,
Phi_det(tauF)/tauS = delta uF/uS = -qF/qS.
```

The first two equalities are field-linear algebra; the DVR and integral-isomorphism assumptions are needed for the integral line comparison and valuation interpretation. No primitivity or integral complement is used.

**Supplied-source and historical lookup.** I read the complete supplied lemma and checker, the supplied contribution review's mathematical/scope discussion, the six existing Lean statements/proofs, the repository contract, and the exact adjacent manuscript passages listed below. I also read the earlier determinant argument preserved in `docs/audit-history/issue2/evidence/determinants.md` and the explicit three-by-three cofactor/strict-torsion derivations in the earlier packet review, rather than relying only on their verdicts. The earlier excerpt invokes “section 9” for switch preservation; the full original report behind that excerpt was not located in the bounded repository search. Its invocation is not a source-level verification of the new adapter. The earlier packet's three-by-three calculation is a genuine special-case justification and a reusable sign check, not an arithmetic boundary-cup proof.

Historical classification is **prior components located; complete arithmetic normalization status unresolved in this scoped review**. Manuscript incorporation of the newly supplied scalar calculation is **pending**. This is not a declaration of a newly discovered whole-paper gap, nor a finding that no earlier proof exists. I did not review the full manuscript dependency chain, Nekovar's primary source, or all earlier private research.

### 2) Independent re-derivation (outline)

**Rank and nonvanishing first.** The vectors `D0,a,b` are a basis of `L^n`. The image of `DF` contains the independent `m+1=n-1` columns `D0,a`, and the nonzero cycle `zF` puts its rank at most `n-1`; hence its rank is exactly `n-1`. The same holds for `DS`, using `D0,b`. The closed functional `lambdaF` annihilates `D0,a`. If it also annihilated `b`, it would vanish on the basis `T`, contradicting its nonzero assumption. Thus `qF!=0`; similarly `qS!=0`. A rank `n-1` matrix has nonzero rank-one adjugate, with column space its kernel and row space its left kernel. Since each kernel is generated by the actual nonzero cycle and each left kernel by the actual nonzero functional, the coordinates `uF,uS` exist uniquely and are nonzero.

**A determinant-update proof, deliberately different from the supplied normal-form proof.** Define covectors

```text
rhoF(y)=det[D0,a,y],       rhoS(y)=det[D0,y,b].
```

They vanish on `D0,a` and `D0,b`, respectively, and satisfy `rhoF(b)=rhoS(a)=theta`. Therefore

```text
lambdaF = (qF/theta) rhoF,
lambdaS = (qS/theta) rhoS.
```

Let `r` be any source row functional and `y` any target column. For
`BF=[e1,...,em,zF,(0,x)]`, `det BF=eta` and `DF BF=[D0,0,a]`. In
`(DF+t y r)BF`, the zero column must supply the factor `t y r(zF)`.
Every other term with two perturbation columns vanishes because those
columns are multiples of the same `y`. Consequently

```text
det(DF+t y r) = -(t/eta) r(zF) rhoF(y).
```

The coefficient of `t` on the left is `r adj(DF) y`. Since `r,y` are
arbitrary, `adj(DF)=-(1/eta) zF rhoF`, giving
`uF=-eta qF/theta`.

For `BS=[e1,...,em,zS,(0,Jx)]`, `det BS=delta eta` and
`DS BS=[D0,0,b]`. The analogous determinant expansion gives

```text
det(DS+t y r) = (t/(delta eta)) r(zS) rhoS(y),
adj(DS) = (1/(delta eta)) zS rhoS,
uS = delta eta qS/theta.
```

This verifies both signs without assuming the conclusion or discarding a
strict factor.

**Basis transport and the determinant-line map.** For `D'=T^-1 D B`,

```text
adj(D') = (det B/det T) B^-1 adj(D) T,
z'=B^-1 z,       lambda'=lambda T,
u' = u det T/det B.
```

Thus the old coordinate equals `u' det B/det T`; the supplied derivation
uses the right direction. In its normal forms, `NF=[[0,1],[0,0]]` has
`adj NF=[[0,-1],[0,0]]`, while `NS=[[0,0],[0,1]]` has
`adj NS=[[1,0],[0,0]]`. The transformed tensor coordinates are indeed
`-qF` and `qS`.

For cohomological degrees one and two, `det^-1 C=det(C^1) tensor
det(C^2)^*`. With the strict-first ordering used here, each short exact
sequence of complexes identifies it with the common inverse strict
determinant factor tensor the degree-one local plane determinant.
Applying `exterior^2 J` therefore multiplies the retained line basis by
`delta`, not `delta^-1`. This uses two exact sequences and determinant
additivity; it does not assert a commuting morphism of the two triangles
fixing the strict complex. Dividing the coordinates gives `-qF/qS`.

**Typed conditional boundary-cup adapter.** Take an alternating bilinear
form `omega:F x F -> L` and a linear equivalence `J:F≃S`. Define

```text
beta(f,s) = epsilon omega(f,J^-1(s)),
lambdaA(iF partialS(s)) = c beta(v,s),
lambdaB(iS partialF(f)) = -c beta(f,Jv),
```

with the same specified `c!=0` and `epsilon!=0`. Here `iF:H^2(K)->H^2(CF)`
and `iS:H^2(K)->H^2(CS)` are the maps from the two exact sequences;
`partialS` and `partialF` are their opposite local boundaries. Evaluation
at `s=Jx` and `f=x` gives

```text
qF=c epsilon omega(v,x),
qS=-c epsilon omega(x,v)=c epsilon omega(v,x)=qF.
```

Thus the conditional comparison is exactly `Phi_det(tauF)=-tauS` in the
declared convention. Nonzero `qF` is already supplied by the matrix
hypotheses; if nonvanishing is established solely through the adapter,
one must additionally retain `omega(v,x)!=0` (automatic for a nonzero
alternating area form on the two-dimensional plane and independent
`v,x`). An alternating form by itself need not be nonzero.

The supplied note writes `beta(f,s)=epsilon omega(f,Js)` and `J^2=1`.
That expression is correct after explicitly identifying both coordinate
planes with the same two-dimensional Tate space and using its involutive
matrix `J`. For an abstract map `J:F->S` the expression `J(s)` is not
typed. The inverse formulation above removes this ambiguity and does not
need an involution assumption. Its specialization to the manuscript's
chosen coordinates uses H12's actual `J^2=I`.

### 3) Checks

**Plug-back checks.** The proof uses the actual `hF,hS,v,Jv`; it never
replaces these cycles by primitive generators. The cycles eliminate their
normal-form column exactly: `DF zF=DS zS=0`. The rows
`lambdaF T` and `lambdaS T` have zero strict entries and final entries
`(0,qF)` and `(qS,0)`. All displayed denominators are nonzero. No converse
or extra solution is introduced by division.

**Boundary and exceptional cases.**

| Case | Check and conclusion |
| --- | --- |
| `n=2`, `m=0` | The strict source is zero; the retained strict complex is `R^2[-2]`. The empty strict block has determinant one. The determinant-update and two-by-two adjugate signs remain valid. |
| Divisible actual cycles/local vector | `v!=0` gives a field basis `(v,x)` without any primitive assumption. `det BF=eta` remains true for nonzero `hF`; source shears do not change it. |
| Fractional `x` | All complement and target-basis operations are over `L`. No integral splitting of `Rv` is assumed. Arbitrary nonzero `eta`, including nonunits, is allowed. |
| Common strict nonunit factors | `D0` is retained in `theta=det[D0,a,b]`. The same `theta` cancels only after both coordinate formulas have been derived. This is a determinant statement; it does not assert that the torsion of `H^2(K)` embeds unchanged in each plane cohomology. |
| Arbitrary integral `GL2` map | The formulas use the actual `delta`. It need not be `-1` or `+1`; only `v_R(delta)=0` is needed for the stated valuation identity. |
| Nonintegral functionals | Closed nonzero rows over `L` suffice. A common fixed clearing scalar multiplies both `q` values and both tensor coordinates, leaving the ratio unchanged. Independent rescalings can change its valuation. |
| Characteristic/sign | The field calculation is also valid in characteristic two, where the minus sign equals plus. The supplied numerical negative example specifically lives in characteristic zero over `Z_(2)` or `Z_2`. |
| Missing nonzero/invertibility hypotheses | `v=0`, zero functionals, `eta=0`, and singular `T` are excluded for real reasons: rank-one tensors or the divided expressions can then fail. No claim here covers these excluded cases. |

If the boundary space is actually identified with
`L^n/im(D0)` and has the supplied exact `AxesKernel`, it does imply the
invertibility of `T`: a relation between the classes of `a` and `b`
would put `(alpha x,beta Jx)` in the combined kernel. Because `x` is
outside `Lv`, both coefficients vanish, and independence of `D0`
finishes the argument. Identifying that quotient with the actual strict
cohomology is a construction obligation, not one of the six existing
Lean declarations.

**Independent primitive negative control.** For the supplied example,

```text
adj(DF)=[[0,-2],[0,0]],     adj(DS)=[[4,0],[0,0]],
zF lambdaF=[[0,1],[0,0]], zS lambdaS=[[1,0],[0,0]],
uF=-1/2, uS=1/4, delta=-1, delta uF/uS=2.
```

For `x=e2`, `a=2e1`, `b=-4e2`, `theta=-8`, `eta=1`, `qF=-4`,
`qS=2`, reproducing both formulas and the ratio. Both cycles and rows
are primitive integral. The combined boundary kernel consists exactly
of the two `e1` axes, so all six existing abstract lemmas apply with
their stated extra hypotheses. `H^2(K)=R^2` has no torsion, while the
two plane complexes have boundary-image torsion of orders two and four.
This disproves the weaker implication from axis kernels, integral `J`,
integrality, and even primitivity to valuation equality. It does not
satisfy the common boundary-cup normalization and is not a
counterexample to the arithmetic manuscript.

**Supplied computation replay.** After inspecting every function in
`review/check_boundary_scalar.py`, I ran Python 3.13.12:

```sh
python3 -B review/check_boundary_scalar.py
python3 -B -O review/check_boundary_scalar.py
```

Both exited zero and emitted identical 474-byte JSON, SHA-256
`661d088d9f4c62b5ded36ec80202fcdbab8260fe5f10376595a30ed08ccddfff`.
The observed counts were 300 common-strict cases, sizes 2 through 5,
152 equal cross-pairing cases, 129 unequal-scale negative controls,
and 255 divisible-vector cases. The code checks all outer-product
entries, not one selected cofactor, and explicit `need` exceptions
remain active under `-O`. It is finite exact regression evidence,
not a proof of a universal identity or arithmetic realization.

**Separately implemented supplementary computation.** I also ran 150
exact rational cases, 30 in each size 2 through 6, without importing
the supplied checker. Determinants/minors were calculated by Leibniz
permutation expansion rather than Gaussian elimination. Every tensor
entry and both scalar formulas passed. All 150 used integral
`GL2(Z_(2))` matrices with determinant `+/-3/5`, extending the supplied
checker's `+/-1` tests; 142 had nonunit `eta`, 133 fractional `x`,
150 nonintegral `L`-valued rows, 120 nonunit strict factors, and 110
divisible `v`. Seed: `1108202601`. This check is supplementary; the
certification rests on the universal derivation above. Its deterministic
construction and complete executable source are preserved below for
reproduction.

<details>
<summary>Supplementary exact-check source</summary>

```python
from fractions import Fraction as Q
from itertools import permutations
from random import Random
import json
rng=Random(1108202601)
def det(A):
 n=len(A)
 return sum(((-1)**sum(p[i]>p[j] for i in range(n) for j in range(i+1,n)))*prod(A[i][p[i]] for i in range(n)) for p in permutations(range(n)))
def prod(v):
 q=Q(1)
 for x in v:q*=x
 return q
def inv(A):
 d=det(A);n=len(A)
 assert d
 return [[Q((-1)**(i+j))*det([[A[r][c] for c in range(n) if c!=i] for r in range(n) if r!=j])/d for j in range(n)]for i in range(n)]
def adj(A):
 n=len(A)
 return [[Q((-1)**(i+j))*det([[A[r][c]for c in range(n)if c!=i]for r in range(n)if r!=j]) for j in range(n)]for i in range(n)]
def mm(A,B):return [[sum((x*y for x,y in zip(row,col)),Q(0))for col in zip(*B)]for row in A]
def ident(n):return [[Q(i==j)for j in range(n)]for i in range(n)]
def mv(A,v):return [row[0]for row in mm(A,[[x]for x in v])]
def dot(a,b):return sum((x*y for x,y in zip(a,b)),Q(0))
def block_cols(*bs):return [sum((b[i]for b in bs),[])for i in range(len(bs[0]))]
counts={'cases':0,'n2':0,'nonunit_eta':0,'non_pm1_delta':0,'fractional_x':0,'nonintegral_functionals':0,'strict_nonunit_cases':0,'divisible_local':0}
for n in range(2,7):
 m=n-2
 for k in range(30):
  P=ident(n)
  for _ in range(8):
   i,j=rng.sample(range(n),2);c=rng.randint(-3,3)
   P[i]=[x+c*y for x,y in zip(P[i],P[j])]
  P[0]=[x*Q(3,5)for x in P[0]]
  P_inv=inv(P)
  ds=[Q(2**(1+j%4))for j in range(m)]
  D0=[[P[i][j]*ds[j]for j in range(m)]for i in range(n)]
  a0=[P[i][m]*Q(2**(k%4))for i in range(n)]
  b0=[P[i][m+1]*Q(2**((k+2)%5))for i in range(n)]
  v=[Q(2**(k%4)),Q(2**(k%4)*rng.randint(-2,2))]
  J=[[Q(1),Q(rng.randint(-3,3))],[Q(0),Q(3,5)]]
  if k%2:J=[J[1],J[0]]
  jv=mv(J,v)
  rf=[-v[1],v[0]];rs=[-jv[1],jv[0]]
  Hf=[[Q(rng.randint(-2,2))for _ in range(2)]for _ in range(m)]
  Hs=[[Q(rng.randint(-2,2))for _ in range(2)]for _ in range(m)]
  AF=[[sum((D0[i][j]*Hf[j][c]for j in range(m)),Q(0))+a0[i]*rf[c] for c in range(2)]for i in range(n)]
  AS=[[sum((D0[i][j]*Hs[j][c]for j in range(m)),Q(0))+b0[i]*rs[c] for c in range(2)]for i in range(n)]
  DF=block_cols(D0,AF);DS=block_cols(D0,AS)
  zF=[-dot(row,v)for row in Hf]+v
  zS=[-dot(row,jv)for row in Hs]+jv
  x=[Q(rng.randint(-3,3),2**(k%3)),Q(1,2**((k+1)%4))]
  eta=det([[v[i],x[i]]for i in range(2)])
  if not eta:x[1]+=Q(1,16);eta=det([[v[i],x[i]]for i in range(2)])
  assert eta
  a=mv(AF,x);b=mv(AS,mv(J,x))
  T=[D0[i]+[a[i],b[i]]for i in range(n)];theta=det(T)
  assert theta
  lf=[Q(3,2**(k%4))*t for t in P_inv[-1]]
  ls=[Q(-5,2**((k+1)%4))*t for t in P_inv[-2]]
  qf=dot(lf,b);qs=dot(ls,a);delta=det(J)
  assert qf and qs and delta
  assert mv(DF,zF)==[0]*n and mv(DS,zS)==[0]*n
  assert mm([lf],DF)==[[0]*n]and mm([ls],DS)==[[0]*n]
  uf=-eta*qf/theta;us=delta*eta*qs/theta
  assert [[zF[i]*lf[j]for j in range(n)]for i in range(n)]==[[uf*q for q in row]for row in adj(DF)]
  assert [[zS[i]*ls[j]for j in range(n)]for i in range(n)]==[[us*q for q in row]for row in adj(DS)]
  assert delta*uf/us==-qf/qs
  counts['cases']+=1;counts['n2']+=n==2;counts['nonunit_eta']+=eta.numerator%2==0 or eta.denominator%2==0
  counts['non_pm1_delta']+=delta not in (-1,1);counts['fractional_x']+=any(t.denominator>1 for t in x)
  counts['nonintegral_functionals']+=any(t.denominator%2==0 for t in lf+ls)
  counts['strict_nonunit_cases']+=m>0;counts['divisible_local']+=k%4>0
DF=[[Q(0),Q(2)],[Q(0),Q(0)]];DS=[[Q(0),Q(0)],[Q(0),Q(4)]]
assert adj(DF)==[[0,-2],[0,0]]and adj(DS)==[[4,0],[0,0]]
assert Q(-1,2)*(-2)==1 and Q(1,4)*4==1 and -Q(-1,2)/Q(1,4)==2
print(json.dumps({'status':'PASS','seed':1108202601,'determinant_method':'Leibniz permutation expansion; no supplied checker import','counts':counts,'primitive_counterexample':['-1/2','1/4','2']},indent=2))
```

Run without `-O`: this separately authored test uses Python assertions and
does not claim optimized-mode rejection or enforcement. The supplied
checker above uses explicit exceptions and was separately checked under
`-O`.

</details>

**Source-facing application and nine obligations.** These are comparisons
for the proposed adapter, not fresh acceptance records for the manuscript.

| Obligation | Required / constructed / conclusion |
| --- | --- |
| Source hypotheses | The scalar theorem requires common-strict square two-term matrices and invertible `T`. The note supplies them as hypotheses. V13 gives two triangles, a rank-one actual class, nonzero `v`, local planes and exact-annihilator assertions at lines 5020–5084. Constructing simultaneous compatible presentations remains OPEN. |
| Constructed objects | Matrix cycles are the retained `zF,zS`, with common local relation `Jv`, and rows are the actual specified closed functionals. H19, (4.2), H22 and lines 3530–3542 supply the intended arithmetic cycle/witness objects; their identification with these matrix inputs remains an arithmetic construction obligation. |
| Domain/index coverage | The proof covers every `n>=2` and every instance satisfying its field hypotheses. It proves no inner-limit, outer-quotient, finite-stage, or height-one uniform assertion. V13 uses completed two-adic inner DVRs and all required height-one localizations; those applications remain OPEN. The rank-reducing outer fiber cannot replace a rank-one inner instance. |
| Transition/comparison maps | The explicit matrix map on determinant bases is `delta`, and the typed adapter's maps and minus sign are displayed above. V13 H20–H22 and lines 3434–3535 retain transfer/local homotopies and cup adjunctions. Checking their composite against the specific opposite-boundary evaluations with one common `c` remains OPEN. |
| Identity of consumed object | V13 lines 3873–3891 and 3980–3999 define `lambda_z=PD(-,j^-1 c(z))`; lines 4014–4028 use this same actual row in the tensor coordinate. The adapter must evaluate exactly these rows, rather than independently chosen primitive rows or arbitrary lifts. The theorem does not identify them automatically. |
| Coefficients/normalizations | The scalar proof retains `delta`, `eta`, `theta`, both `q` values, and all strict factors. The source pairing includes an actual Tate-coordinate `J`, H12's involution, the specified local factor and the common fixed class multiplier. They must be transported once in each occurrence; the `J` already in the transported pairing must not be inserted a second time. Proving equality, or unit ratio, of the actual boundary factors remains OPEN. |
| Local conditions | The source conditions retain `D^0`, and the strict/relaxed quotient planes are `F[-1]`,`S[-1]`, not zero/full at derivative primes. The note matches this abstract configuration. Integral orthogonal comparisons, conjugate places, isotropy homotopies and old-place torsion still require arithmetic instantiation; they are not generated by a determinant identity. |
| Exceptional cases | Divisible `v`, fractional `x`, strict nonunit factors, `n=2`, nonzero denominators and arbitrary unit `delta` are checked above. The source also uses quadratic specializations `(t)` and `(t+2)` and fixed clearing factors; the note's instancewise theorem does not establish their input hypotheses. |
| Downstream consumption | V13 lines 5134–5139 consume inner valuation preservation; lines 5323–5338 consume the actual derivative coordinate; lines 5374–5379 transport terminal integrality through switches. The ratio formula identifies the exact sufficient unit condition. It does not discharge the numerical lower bound, (5.5a), regularity, restricted converse, or other manuscript claims. |

The manuscript passages were inspected in their adjacent construction
context: conjugate coefficients and pairing at 2898–2957, H12 at
3225–3233, H19 at 3323–3337, H20–H22 and the local cup/homotopy discussion
through 3542, the paired-functional definition at 3842–3891 and 3980–4029,
the owning switch at 5020–5093, the inner valuation consumer at
5122–5142, height-one setup at 5162–5168, the pairing/sign computation
at 5212–5239, and the switched-functional consumers at 5323–5379.
The manuscript explicitly treats `J` as part of the transported duality
at 2953–2957. The adapter is therefore a sufficient interface to be
matched to that construction; its agreement with the source is not
proved just by writing the same pairing formula.

For reconstructing the exact relevant manuscript excerpts, the hash rule
is concatenate original raw lines `start..end` inclusive, retaining their
original line endings, with no added bytes:

| Lines | Excerpt SHA-256 |
| --- | --- |
| 2898–2957 | `5c412c4aa2be8c89b5776befa60f9b800634fde07a00a9c0067c52582cc18c56` |
| 3225–3233 | `d90f2091c3540337d81924175a51b5f1c999227980cc8f065e04f1d24fd6d5ae` |
| 3323–3337 | `22e3b16153043df891a6cf4f9e39a98318180a7fc67c56bfcbaa92dc1f7b4666` |
| 3434–3535 | `84ef6342cae2bdef270beb9a95c9880fb99d36f9b586b9265c103f36974c1ce3` |
| 3842–3891 | `518fa43e28552f0e8304f65663efb6841c8c4815cb242fa14a886eae6b79fcc7` |
| 3980–4029 | `3f7dcbd0e9b5c8da10825923d2f15236c0d4364f88f649f22e19a302256c1652` |
| 5020–5093 | `2f23916a10a7bf9724f702d575fd6cf620023d811730b77f4cbcc7a460d57680` |
| 5122–5142 | `4069bd66752c866c5a571e620df11fb73c4f636759830b7b5283f2094dfa6f4b` |
| 5162–5168 | `c45eb9e5f1c5709adefbe0b852608b25ccb55f687a6112946155a620fd17a769` |
| 5212–5239 | `7e218ca86371b5f42c0028309d5abaaa8b8bc78c0c84e96583c3b5321fcd9013` |
| 5323–5379 | `ea5abd0df4b176cf65c4a060923e19818d8891e524467d9525af8cf299595125` |

### 4) Discrepancy report (if any)

**No mathematical discrepancy in the general scalar theorem.** The
independent determinant-update derivation agrees with the supplied
normal-form proof on both signs, the determinant-basis direction, and
the primitive counterexample.

**Adapter notation clarification.** The supplied `J(s)` and `J^2=1`
require the coordinate identification described in Section 2. A typed
`J^-1(s)` formulation is a correct and slightly more general sufficient
adapter. This is a statement-precision issue, not an adverse example.
No acceptance is given here to a still-unseen implementation of that
typed statement.

**Nonvanishing precision.** The conditional equality `qF=qS` uses only
alternation, while deriving nonvanishing solely from `c,epsilon,eta`
also requires that `omega` be the nonzero area form in the chosen
two-dimensional coordinates. In the full matrix theorem nonvanishing is
already proved independently, so the note has no false scalar division.

**No historical or scope promotion.** The earlier no-go lemma excludes a
particular identity-on-strict square. The printed manuscript uses two
separate triangles. Their distinction is preserved. Earlier historical
special-case calculations and finite regression passes supply no
arithmetic normalization acceptance, and the source-level matching of
actual opposite-boundary evaluations remains unresolved within this
review's bounded search.

### 5) Certification result

**CERTIFIED under assumptions in `BOUNDARY_SCALAR_LEMMA.md`, SHA-256
`5c72a9d2169bee1d9f0077d422ed0cb06913c61bf762e0976e822ef1c95dedb6`,
for its common-strict matrix theorem, its stated adjugate convention,
its valuation equivalence, and its primitive negative control.** The
typed inverse-based adapter in Section 2 is correct as a conditional
ordinary-algebra implication. The supplied coordinate-based adapter is
correct with the explicit plane identification and involutive matrix
meaning stated above.

The existing six-lemma Lean source is byte-identical to the supplied
reviewed copy. No statement strengthening or new formal coverage is
inferred from this equality. Its arithmetic hypotheses are not proved
by this report.

Arithmetic common-strict realization, the actual functional identities,
the common normalization factor and signs after cochain/cone transport,
every retained-ring application, integration into consuming passages,
and manuscript/release acceptance remain **OPEN**. No relevant arithmetic
obligation is closed by the finite computation or by this local theorem.

This is a non-release review of an isolated research addition. No
publication source or release asset was changed, so PDF regeneration,
archive synchronization, publication readback and whole-proof closure
are not certified or required for this review's completed intake scope.
Any later mathematical/formal statement or adapter text must obtain its
own exact-byte review before carrying this decision forward.

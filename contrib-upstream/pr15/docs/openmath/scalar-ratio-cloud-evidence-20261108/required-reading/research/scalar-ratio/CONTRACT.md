# Scalar-ratio verification contract

This contribution extends the frozen 21-declaration algebraic packet. It starts
from raw common-strict matrices and derives the normal frames rather than
assuming them. The selected target is the original 21 plus 18 new declarations
in [comparator.json](verification/comparator.json). The original two freezes,
manuscript, accepted 48 modules and dependency pins are unchanged.

The intended algebra is fixed in [DERIVATION.md](DERIVATION.md). Original upload
bytes and the supplier's NOT_RUN formal status are retained in `inputs/`.
Native builds, local structure comparison, cloud replay and arithmetic
instantiation are separate claims. See [VERIFICATION.md](VERIFICATION.md).

| Application obligation | Required and constructed objects; evidence and consumer |
| --- | --- |
| Source hypotheses | A field K, finite I (including empty I), index I ⊕ Fin 2, actual D0/AF/AS, actual cycles and closed rows, area(v,x)≠0 and det[D0,AFx,ASJx]≠0. `CommonStrictData` stores these data; it stores neither a coordinate formula nor a desired unit equality. |
| Constructed objects | `join`, `cycle`, `frame` and `target` are explicit matrices/vectors. `HasCoordinate D z lam u` is the full identity tensor(z,lam)=u·adj(D), independent of the scalar formulas. `coordinate_values` applies uniqueness to separately supplied coordinates. |
| Domain and index coverage | Arbitrary finite I gives every size m+2 for m≥0; the minimal size is two. The matrix result is over any field and has no characteristic exclusion. area≠0 excludes zero local classes. No acyclic or rank-changing outer constituent is substituted. |
| Transition/comparison maps | Two separate source frames and target column orders yield DF BF=TF N and DS BS=TS N. The column swap gives det TF=−theta; det TS=theta. No map CF→CS, identity on the strict complex or strict automorphism eta is assumed. |
| Consumed object | Literal row evaluations qF=lamF(AS Jx), qS=lamS(AF x) give the cofactor coordinates of the same stored cycles and rows. UnitRelated and BoundaryCupIdentity consume these same objects. Normalizing different primitive rows would change the input. |
| Coefficients and normalization | `UnitRelated R a b` exhibits a unit of the specified Subring R⊂K. Field invertibility alone is insufficient. A common nonzero field factor may cancel even when it is not an R-unit. Removing delta additionally requires its explicit lift to R×. |
| Local conditions | The abstract matrix result makes no arithmetic localization claim. For use in the manuscript, actual integral cones, common-strict presentations, retained bases, local J and boundary–cup normalizations at every required localization must be established separately; see the preserved arithmetic contract. |
| Exceptional cases | Nonzero adjugate follows from the frames, so coordinate uniqueness includes lambda=0. Both zero coordinates/evaluations satisfy UnitRelated; exactly one zero does not. Only quotient theorems divide by qS (or cS and epsilon) with explicit nonvanishing. Common-normalization/unit adapters avoid this division. Neither eta nor theta is required to be an integral unit. |
| Downstream consumption | The formal valuation consumer is a multiplicative map K→*₀G trivial on R-unit images. It proves equal images from UnitRelated; the full additive-DVR iff, determinant-functor bridge, complement quotient construction and actual Selmer application remain ordinary or open as explicitly described below. |

## Boundary–cup adapter

Both local spaces are the explicit coordinate plane `Fin 2 → K`. The adapter
assumes J²=1 in these bases and beta(f,s)=epsilon·area(f,Js). For every s,f it
requires lamF(AS s)=cF beta(v,s) and lamS(AF f)=−cS beta(f,Jv). These are
lower-level identities on the actual rows, not the desired determinant equality.
It derives qF=cF epsilon eta and qS=cS epsilon eta, the exact ratio when defined,
and exact transported equality for a common normalization (including zero).
For det J=−1 the numerical coordinates agree in this orientation. An R-unit
ratio of normalizers and integral-unit determinant give UnitRelated(uF,uS).

## Explicit non-claims

The formalization constructs neither actual Galois/Selmer objects nor
Poitou–Tate duality. It does not prove occurrence of AxesKernel, identify the
actual arithmetic functionals, prove their compatible normalization, construct
derived determinant functors, or verify retained limits/exceptional height-one
localizations. No manuscript change, accepted determinant-switch proof,
restricted converse, upstream review/merge, or release acceptance follows.
The [received arithmetic contract](inputs/ARITHMETIC_CONTRACT.md) preserves
those obligations at source baseline 40d01c5; its historical compilation status
is superseded only by the separate current verification evidence.

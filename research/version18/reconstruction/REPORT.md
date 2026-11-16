# Independent finite reconstruction of Conant's frozen 198-variable package

Verdict: **PASS for the finite polynomial specification, both coefficient presentations, and the stated exact statistics, subject to the two wording distinctions below.** No package, manuscript, or polynomial was edited, and no optimization was attempted. This audit does not verify the inherited infinite arithmetic premises or any Busy Beaver theorem.

The selected archive is `C:/Users/glaze/Downloads/H10-quartic198.zip`, SHA-256 `33439f62ec243375b19f50c2801cad36500f21902285a82e5c08984a0c5568c4`. All 90 extracted files were freshly authenticated against `work/v18-198-dependency-inventory-20261114/PACKAGE-PINS.json`. The frozen package remained read only. Attribution to Gabriel Conant and the variable count 198 are retained.

## Exact result

Put

```
K0 = 31581660^28,
J0 = 5898050446009651968,
H0 = (J0*K0)^2.
```

H0 has 458 decimal digits.

| Property | Unbalanced table | Preferred balanced table |
| --- | --- | --- |
| Fixed coefficient | A=149^(2N+1) | C=149^N, with A=149*C^2 |
| Parameter range | Integer N >= 1 | Integer N >= 1 |
| Total rational coordinates | 198 | 198 |
| Input coordinates | 1 | 1 |
| Existential auxiliary coordinates | 197 | 197 |
| Quadratic residuals | 184 | 184 |
| Degree of every residual in coordinates | 2 | 2 |
| Degree of the sum of squares in coordinates | 4 | 4 |
| Integer content of every fixed-member quartic | 1 | 1 |
| Nonzero coordinate monomials for every allowed N | 2945 | 2945 |
| Terms when parameter powers are separated | 2945 | 2959 |
| Exact coefficient height | max(H0,A^2) | max(H0,K0*C^2) |
| First N where the parameter branch attains the maximum | 53 | 57 |

The coefficient of the fourth power of input coordinate x1 is exactly 1 and has no other parameter contribution. This proves degree four and content one after every allowed specialization. A gcd across the formally separated parameter coefficients alone would not suffice; the independent audit checks this stronger witness explicitly.

All 198 coordinates occur in both expanded polynomials. A fixed coefficient is not an additional quantified variable. The polynomial belongs to `Z[X,Y1,...,Y197]`, with delivered coordinate x1=X and xi=Y(i-1) for i>=2.

The coefficient crossovers are not sufficient defining thresholds. The arithmetic construction's sufficient threshold remains ineffective unless a separate argument establishes the chosen specialization.

## Polynomial-in-A wording

The unbalanced polynomial has exactly three parameter-dependent coordinate monomials. In the delivered coordinate numbering it is

```
P_A(x) = P_0(x) - 2*A*x104 - 44402*A*x104^2*x116 + A^2*x104^2.
```

Here P_0 is a fixed integer polynomial with 2942 nonzero monomials, and the three displayed coordinate monomials do not occur in P_0. Its maximum absolute coefficient is H0. Thus the coefficients are integer polynomials in A of degree at most two. The fixed parameter A is distinct from the scalar integer label a and the Lucas parameter a+1.

If the manuscript retains the settled specialization

```
A = 149^(2*BB(2^1000)+1),
```

the unbalanced table supports the exact phrase "coefficients polynomial in A" directly. In that presentation, take N=BB(2^1000). The finite audit does not establish that this Busy Beaver value exceeds the arithmetic defining threshold.

The preferred balanced polynomial is a polynomial in C. It has 685 pure linear-C profiles, including the coefficient `-2*C` of `x6^2*x87*x115`. Therefore its coefficient family cannot be expressed as polynomials in A=149*C^2. For example, no polynomial f over Q can satisfy `f(149*C^2)=-2*C` at all C=149^N, since that would make the polynomial `f(149*t^2)+2*t` vanish at infinitely many t and hence vanish identically, which its even/odd parts prevent.

Using the balanced presentation requires stating `C=149^BB(2^1000)` explicitly alongside A. Selecting the package's unbalanced presentation is the alternative if the precise polynomial-in-A wording must be preserved. The variable count and arithmetic input projection do not change under the certified balancing map. The integration decision belongs to the root task.

## Primitivity wording

Every unbalanced residual is primitive after every allowed A specialization. The checker proves this from its disjoint parameter support and the gcd at A=149^3; higher allowed powers introduce only the same prime 149.

Every balanced residual is primitive as a formal integer polynomial in C and the coordinates. After substituting C=149^N, however, row 54, `scalar.Bh.definition`, has integer content exactly 149 for every N>=1. It has the form

```
B*x11*x108 + 17*C*x11 - 17*C*x12*x110,
```

where the displayed constant B in the table has exactly one factor of 149 and is coprime to 17. All other specialized balanced rows are primitive. The complete fixed-member quartic still has content one because its input fourth-power coefficient is one.

Consequently "a sum of 184 integral quadratic squares, with quartic content one" is accurate for both presentations. "A sum of 184 primitive integral quadratic squares" is accurate without qualification for the unbalanced fixed members. For the balanced table it needs to refer to formal row normalization rather than assert primitivity after specialization. Dividing row 54 again after specialization would define a different sum-of-squares polynomial and would require new coefficient statistics; this audit did not do that.

## Complete independent reconstruction

The selected construction runs through the package's own affine-200 intermediate from Jose's pinned 204 table. It does not use the earlier shifted-200 or order-four-shift 199 constructions.

`independent198.py` imports no package producer or checker. SymPy performs substitutions, Laurent expansion, reduction modulo rho^2-2, row normalization, and every row-square expansion. The independent audit checked:

1. Every one of the 186 affine-200 rows against the pinned 204 table and the changed odd-fourth-label formulas, then every coefficient of its quartic.
2. Every one of the 184 inverse-198 rows. Inherited rows were reconstructed under the complete saved Laurent weight map; the twenty new rational inverse Vieta rows were derived directly from the physical scaled field equations. The R2=R^2 row was retained literally. The aggregate was independently reconstructed.
3. Every one of the 184 balanced rows under the complete saved integer C-weight map. Input weight zero, row division powers, primitive formal normalization, degree limits, and all coefficient dictionaries were checked.
4. Every coefficient of the unbalanced and balanced 198 quartics by independently expanding the complete sum of squares. All results matched the frozen tables exactly.
5. The positive scalar contact identity and the literal rescaled forced-prime equation, which exclude R=0 before Laurent inversion. These are finite identities plus the elementary positivity of beta=51X^2+2504 and its four contact factors.
6. A coefficient mutation and a missing factor two in the scalar chart, both of which were rejected by comparison with the independent formulas.

The final compact formal-coordinate list is `1,4,...,154,183,...,228`, with 198 entries. The first fourth-pair replacement removes 14 rational coordinates and adds ten; the inverse Vieta replacement removes sixteen rational coordinates and adds fourteen. The resulting count is 204-14+10-16+14=198. The row counts are 186-18+18-23+20+1=184.

The final physical inverse Vieta equations were checked as

```
u*v = R2*p,
p*w = r,
r*(u+v+w+2*m) + D*R2 = 0,
R2*p+w*(u+v) = m^2,
r2 = r^2,
F_U*r2 = u^2,
F_V*r2 = v^2,
L2*(m+u) = 2*R*S,
L2^0*(m+v) = -2*R*T_H,
Z_stored*(m+w) = -2*S.
```

Here p=x(Q2), and `Z_stored=2*z(Q2)/(R*z(H))`. R2 and r2 are different coordinates. The aggregate is `7+Tr(sum_i x(Q_i))/4`, not the offset-11 aggregate of the superseded 199 candidate. This audit verifies the actual source and table rather than transferring a prior candidate's semantics.

## Support and height proofs

The unbalanced coefficient profiles consist of 2942 constant profiles, two linear-A profiles, and one quadratic-A profile. Each profile contains a single power of A, so no allowed positive A can cancel a coordinate monomial. The linear coefficient magnitudes are 2 and 44402. Since A>=149^3>44402, their values are bounded by A^2. The pure A^2 profile at x104^2 and the pure H0 profile at x110^4 attain the exact maximum. The integer inequalities `149^210 < H0 <= 149^214` prove crossover N=53.

The balanced census is:

| Powers of C in one coordinate coefficient | Number of profiles |
| --- | ---: |
| 0 | 1697 |
| 1 | 685 |
| 2 | 549 |
| 0 and 2 | 14 |
| Total coordinate monomials | 2945 |

Twelve mixed profiles have same-sign coefficients. The remaining two, at x11^2 and x12^2*x110^2, have even constant term and odd C^2 coefficient 289. They are nonzero for every odd C, hence for every C=149^N. It would be incorrect to infer support 2945 for every positive real C from this parity argument.

For every linear profile cC, the independent checker proves `c^2<=H0*K0`. For every constant/quadratic profile a+bC^2 it proves `abs(a)*K0+abs(b)*H0<=H0*K0`. The pure profiles at x110^4 and x107^2*x115^2 attain H0 and K0*C^2. Hence the exact coefficient height is the maximum stated above. The comparison `K0*149^112 < H0 <= K0*149^114` proves crossover N=57.

For each fixed allowed parameter, the polynomial is exactly the sum of the 184 displayed residual squares. Over Q, this sum vanishes if and only if every residual vanishes. Multiplication by nonzero fixed parameter powers and nonzero rational row constants preserves those common zeros. The balancing map is invertible and fixes the input, so it preserves rational input projection. These finite equivalences do not by themselves establish that the common input projection equals Z.

## Native reproduction and evidence

Before execution, I inspected the deterministic builders, their sparse-arithmetic helper, the two relevant checkers, and both saved scaling certificates. No search script was run. The helper's unrelated filename and docstring do not import its arithmetic theorem; the builders use only its finite polynomial operations.

The scripts ran only in the isolated `native-package` copy. All six completed successfully:

```
build_affine200.py
check_affine200.py
build_inverse198.py
check_inverse198.py
balance_inverse198.py
check_balanced198.py
```

`run_native.py` fixes text writes to LF solely to avoid Windows newline changes. With that documented platform adaptation, the six rebuilt quadratic/quartic artifacts are byte-for-byte identical to the frozen package. Mathematical source and input data were unchanged. Per-script logs and hashes are recorded in `native-reproduction.json`.

The independent run used Python 3.14.7 and SymPy 1.14.0 from the existing task-local library. It completed 50,684 assertions, many of which are repeated schema and coefficient checks rather than separate mathematical propositions. Results are in `independent198-result.json`.

To reproduce in this workspace, set PYTHONPATH to the existing `work/jose200-audit-20261114/python-deps` directory, then run `independent198.py` and `run_native.py` with the recorded interpreter. Both scripts use paths relative to their own location; the independent checker also authenticates the selected Downloads archive by its pinned hash. Reproduction requires no network connection or credentials.

| Artifact | SHA-256 |
| --- | --- |
| Unbalanced quadratic | `c55d7eefe41f62fee88b467e3ea8f6be8ba1e66f6a94b30eb74b39f6f6e7efad` |
| Unbalanced quartic | `652b5141aaa0d9f54ef89196ae9e442787335b2fd498e250c2772dc3af98a36c` |
| Balanced quadratic | `e818e7cb659735ecdae722690f0e7a3c98854f0830a9562188b67ce175b8fc62` |
| Balanced quartic | `4150c823b1f137c75d35217585442b3965e710822cb94af5e8cb54028fcd7ac1` |
| Balancing weights | `567fb88f32077560562b8172c2c8e53533f22ddf402a669d8b15415c245f88b3` |
| Independent checker | `2a2cee362eb285e59bf6aab230244199f881c041ac79ff1b2722eb9dd63c9ed2` |

No finite reconstruction or coefficient check remains pending. The choice of presentation for the manuscript's A wording, the arithmetic theorem, and the Busy Beaver transfer remain with the root integration and its separate proof reviewers.

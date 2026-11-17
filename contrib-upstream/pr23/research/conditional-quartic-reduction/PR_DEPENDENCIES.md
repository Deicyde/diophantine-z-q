# Dependencies of the proposed 389-variable construction

**Status: draft PR; manuscript integration is pending.** This inventories the actual selected construction, domains and consuming passages. Historical derivations remain classified as prior evidence. The inventory does not assert mathematical priority, a newly discovered historical gap, or validation of the inherited global arithmetic.

The pinned upstream commit is `036cebe4f1a4aa7ca89820a9b48f3629b4c364d6`. The selected builder is [construction/builder.cjs](construction/builder.cjs), SHA256 `b4bf6af38a7620a5b6a572039da4fcb22cd6f4ce006c439d89588c1259231f3b`. Package paths are relative to this directory; upstream-source paths are relative to the repository root.

## Selected parameters and coordinate conventions

| Item | Selected value |
|---|---|
| Coordinates / quadratic residuals | 389 total including input / 357; 388 existential witnesses; zero further eliminations |
| Full test order list | 45,12,1,1,1,1,1,1,1,1,12,45,45,45,45,45 |
| Scalar order / exceptional set | 28 / {2,3,5,7,13,17} |
| Fixed anchor / forced depth / balancing base | S₀=3^2364 / 3^1181 divides a−1 / c=3^394 |
| Global height exponent | α=577/32=18.03125 |
| Conductor / height constants | C=2^32·3^9; H=3·2^106 C^6·46410^18+128; 665 bits |
| Actual scalar height target | h(β)<abs(a−1)/4≤(abs(a)+1)/4 |
| Balanced polynomial | 26,295 monomials; degree 4; content 1; max coefficient 28902·3^1576 with 757 digits and 2513 bits |
| Diagonal map | 13 changed coordinates: 12 ternary factors and 2 dyadic factors, with one overlap |
| Input / scalar product | β=2401+2754(2X+1)²; r=β(β−1)(32β+343); correction 42 |

All field coordinates use K=Q(ρ),ρ²=2 in the basis (1,ρ), with norm a²−2b². Consumed unramified valuations have v(p)=1; dyadic arguments explicitly use v(2)=1,v(ρ)=1/2. Heights are absolute logarithmic Weil heights. **Consumers below refer to semantic source coordinates before balancing. Decode all 13 changed coordinates before applying old point identities or square-scale arguments; the transformed stored height-scale coordinate need not itself be a rational square.**

## Inherited mathematical inputs

These retain their original qualifications. Exact arithmetic and independent agent reviews do not establish the inherited theorems.

| ID | Input and required qualification | Upstream argument |
|---|---|---|
| G_curve | The displayed normalized curve over Q(sqrt2) has the fixed infinite-order point P and 2E(K)=Z P; finite root labels are nonzero integers and h(x([n]P))>=n^2-6. Inherited source arithmetic input, not established by circuit checks. The square-abscissa equivalence is specific to this field and D. | `manuscripts/quartic_v10.tex`: `prop:generator`, `subsec:v5-point-source`, `eq:o8-indexheight`; `docs/quartic-523-540/addition.tex`: `subsec:v9-inputs`, `v9chart:prop:chart` |
| G_formal | Integral formal-group addition, inverse and multiplication series; exact local depths/leading residues at 2 and 3; unramified logarithm isometry and its recurrence/valuation bound. Positive-depth formal subgroups are stable under every integral multiple. Retained mathematical input; applications to actual orders and exceptional cases are checked by the cited local proofs. | `manuscripts/quartic_v10.tex`: `subsec:o8-anchor-subgroup`, `lem:quartic-reciprocal-log`, `lem:v5-unramified-log`; `docs/quartic-523-540/addition.tex`: `subsec:v9-local-depth`, `subsec:v9-deep-completeness` |
| G_quaternion | For every rational t, including 0, the three-witness conic u^2+6v^2-2w^2-3t^2+2=0 is soluble exactly when t is integral at 2 and 3. Inherited quaternion embedding/local-global criterion; finite anchor samples are not its proof. | `manuscripts/quartic_v10.tex`: `lem:v5-three-witness-anchor`, `lines 10973--11024` |
| G_height_geometry | The five-contact construction supplies a normal fiber field, an L-defined maximal-order QM action and full 3-torsion. Its compatible representations, normal extension, primitive modular level, character order and CM/non-CM realization supply the intermediate inequalities used in the retained Belyi/Jacobian/isogeny-height proof. The inherited geometric/modularity/isogeny-height theorems and their hypotheses remain conditional. The original manuscript assembles an exponent 19 estimate; the selected 577/32 estimate is a new explicit reapplication of its intermediate inequalities in T32, not a substitution into the old final theorem. | `manuscripts/quartic_v10.tex`: `lines 6861--7405`, `sec:h5-level-repair`, `thm:quartic-height19`, `lines 8915--9073` |
| G_pole | The pole predicate excludes negative odd valuations outside {2,3,17}; its converse and preparation-zero specialization hold under the stated positivity, square-denominator and local-square hypotheses. Retains the source restricted converse RC, corank and simultaneous two-twist realization dependencies. For preparation zero require b<17 and v2(b)>=3,v3(b)>=1,v17(b)>=2. | `manuscripts/quartic_v10.tex`: `hyp:RC`, `lem:corank`, `lem:original-seven-simultaneous-realization`, `hyp:o8-pole`, `lem:original-seven-parity-completeness`, `v5:preparation-zero-bridge` |
| G_one_place | The arbitrary-positive-order reciprocal-trace detector gives all specified test orders at one common place when the contact valuation is odd and the pole predicate holds. Retained uniform local proof, applied with the actual field, contact units and order list. Smaller prime exclusions must be justified by its hypotheses, not by simply deleting its printed cutoff. | `manuscripts/quartic_v10.tex`: `lem:v5-one-place`, `lines 11031--11061` |
| G_product_height | For odd root indices the height of the product of abscissae in K equals the sum of their heights, permitting three fixed-square scales. This is a height in K, not the rational norm; local signs and oddness must be established before use. | `docs/quartic-523-540/addition.tex`: `v9:lem:product`, `v9:cor:scales`, `v9:eq:height-transfer` |
| G_prime_pattern | The source simultaneous Gaussian prime theorem, Artin-pattern weighted count and diagonal argument supply selected contact primes with the prescribed classes, finite avoidances and real/denominator growth. All roots, scales, coefficient data and congruence conditions precede this asymptotic choice; repeated forms are merged with incidences retained. This global input is not independently proved here. | `manuscripts/quartic_v10.tex`: `thm:v5-simultaneous-primes`, `prop:v5-artin-patterns`, `subsec:v5-diagonal`, `lines 11244--11275` |
| G_reductions | The selected split reductions have cardinalities N(pi-1),N(pi+1); their doubling-image orders divided by 4 give the needed coprimalities. Only annihilating group orders are used; no unproved claim about exact point order is substituted. | `manuscripts/quartic_v10.tex`: `lem:v5-two-reductions`; `docs/quartic-523-540/addition.tex`: `lem:v9-bridge`, `v9:lem:separation` |
| G_progression | Finite-place continuity and the real-progression lemma preserve prepared scalar conditions and provide uniform real bounds on comparison tests in later compatible progressions. Bounds are chosen before future progression moduli and are then consumed by the real pole estimate. | `manuscripts/quartic_v10.tex`: `v5:scalar32-bridge`, `v5:real-progression-bridge`, `lines 11220--11241`; `docs/quartic-523-540/addition.tex`: `subsec:v9-completeness`, `subsec:v9-deep-completeness` |
| G_lucas | The stated Lucas identity/growth result supplies odd positive completeness labels and, from the literal residual F=0 and b!=0, log B>\|a\|-3. Retained arithmetic theorem and its sign/nonzero hypotheses; exact evaluation of the residual alone is not its growth proof. | `manuscripts/quartic_v10.tex`: `lem:o8-lucas`; `docs/quartic-523-540/addition.tex`: `subsec:v9-soundness`, `subsec:v9-completeness` |

## Retained transformations and their actual consumers

Every item states its mathematical type and domain. A predicate transfer or strengthening is not a bijection between all old and new witness tuples. Proof links name arguments; historical numerical examples are current only where a selected proof explicitly checks the replacement.

### T01 — Root chart and direct targets

**retained source-domain equivalence.** The four roots use x=h^2,j^2=x^2-D,y=hj without stored ordinates; comparison targets are Q_i and P directly. K=Q(sqrt2),D=(3-sqrt2)^2; roots finite nonidentity with h,j,x nonzero; field equations mean both rational components.

**Current consumer:** `point_modules`, `direct_targets`, `four`, `R`. Inherited inputs: G_curve.

**Proof:** [proofs/prior/round3/geometry_proof.tex](proofs/prior/round3/geometry_proof.tex) — opening root-domain argument.
Upstream application: `docs/quartic-523-540/addition.tex` (`lem:v9-bridge`, `v9chart:prop:chart`, `Using the chart without ordinate variables`).
Already part of the pinned 523 baseline; this inventory does not claim it as a new round 8 theorem.

### T02 — Complete primary reciprocal charts

**domain enlargement with checked arithmetic consumer.** For U_A,U_S,U_T,U_Z use f=g^2,l^2=1-Df^2; g=0,l=+/-1 represents O, while l never vanishes. For finite points recover x=1/g^2,y=l/g^3. The norm obstruction 7*N(g)^2=1 excludes l=0. Identity inputs use a separate congruence argument.

**Current consumer:** `reciprocalCharts`, `UA.g`, `US.g`, `UT.g`, `UZ.g`, `L1 through L4`. Inherited inputs: G_curve, G_formal.

**Proof:** [proofs/prior/round3/geometry_proof.tex](proofs/prior/round3/geometry_proof.tex) — Primary charts; Soundness of the new identity-input case; [proofs/prior/round4/geometry_round4.tex](proofs/prior/round4/geometry_round4.tex) — input-only G2 comparison, including U1=O.

### T03 — Complete subtraction and joint shared chart

**rational chart equivalence on the stated domains.** The variable-target reciprocal subtraction represents exactly U_i-Q_i, including U_i=O and tangency U_i=-Q_i, excluding identity output. The joint H,H-P chart uses fF=s^2 and the two hs*k equations. x_R+D f_U is totally positive; the equations force tau!=0. In the joint chart f,F,s,g are nonzero and k_H,k_V do not vanish. Recover old l,tau,M with the displayed rational formulas.

**Current consumer:** `subtractReciprocal`, `subtractSharedJoint`, `V0.f`, `V0.k`, `primaryRatio`, `V1 through V4`. Inherited inputs: G_curve.

**Proof:** [proofs/prior/round3/geometry_proof.tex](proofs/prior/round3/geometry_proof.tex) — A reciprocal difference formula, all exceptional cases; [proofs/prior/round4/geometry_round4.tex](proofs/prior/round4/geometry_round4.tex) — A joint chart for the shared point and its translate; exact recovery and nonzero denominators.

### T04 — Shared primary ratios and scaled alternate logs

**rational coordinate elimination and exact function evaluation.** L_i=k_H*g_i/l_i equals z(U_i)/z(H); store eta_i=ell(V_i)/h_i through (M_i-j_i)eta_i=-G, then conjugate the entire ratio ell(V_i)/ell(V0). H,H-P finite nonidentity; l_i and alternate logarithm denominators nonzero. U_i=O gives L_i=0 without forming log(O)/z(O).

**Current consumer:** `primaryRatio`, `L1 through L4`, `LP1 through LP4`, `logV*.scaled`, `V*.logDenominator`. Inherited inputs: G_curve, G_formal.

**Proof:** [proofs/prior/round3/geometry_proof.tex](proofs/prior/round3/geometry_proof.tex) — Primary charts; Scale logarithms by the root coordinate; identity-input case; [proofs/prior/round4/geometry_round4.tex](proofs/prior/round4/geometry_round4.tex) — joint-chart ratio recovery.
Upstream application: `docs/quartic-523-540/addition.tex` (`v9:sec:depth`, `subsec:v9-local-depth`).

### T05 — Degree 12 completion and input-only degree 2 log

**exact polynomial circuit plus nonzero-domain proof.** Use G12=a 12*U6^2+R6, deg(R6)<=6, evaluated with w^2,w^4,U6; retain G2 for V1 only. The completion is over Q, not an algebraic square-root choice. At both real embeddings 0<D f(V)^2<1; G12(1)>0 and G2(1)=7/15 prevent zero logs.

**Current consumer:** `aCoeffs`, `logSquareU`, `logSquareR`, `log`, `LV`, `logV0,2,3,4`, `logV1`. Inherited inputs: G_formal.

**Proof:** [proofs/prior/round5/geometry_round5.tex](proofs/prior/round5/geometry_round5.tex) — Complete a polynomial square; Nonvanishing and consumed local precision; [proofs/prior/round4/geometry_round4.tex](proofs/prior/round4/geometry_round4.tex) — Only the input comparison needs a degree-two alternate logarithm.

### T06 — Actual local precision and asymmetric comparisons

**uniform local arithmetic transfer.** G12 has relative precision 45r, G2 precision 12r, and raw z has error 4r at every consumed prime. Primary g_H order 45 gives depth 45; comparison gives Lucas labels mod p^45 and input label mod p^12. Consumed primes outside S6 are unramified and at least 11. Check a 3=-14/195 and tail bounds;13 remains excluded. First transfer integrality using one of h,h-1 being a unit, then make relative errors absolute; include U_i=O and inert places.

**Current consumer:** `tests`, `test0`, `test10 through test15`, `L1 through L4`, `LP1 through LP4`. Inherited inputs: G_formal, G_one_place.

**Proof:** [proofs/prior/round5/arithmetic_round5.tex](proofs/prior/round5/arithmetic_round5.tex) — Actual G2 and raw-z precision bounds with the current exception set; [proofs/prior/round6/arithmetic_round6.tex](proofs/prior/round6/arithmetic_round6.tex) — The retained logarithm supports order 45 and Pi^44; [proofs/detector_round8.tex](proofs/detector_round8.tex) — The promoted primary test preserves every old comparison premise; [proofs/arithmetic_round8.tex](proofs/arithmetic_round8.tex) — Actual height consumers retain local orders 28,45,12; [proofs/prior/round3/geometry_proof.tex](proofs/prior/round3/geometry_proof.tex) — Soundness of the identity-input case.
Upstream application: `docs/quartic-523-540/addition.tex` (`subsec:v9-local-depth`).

### T07 — Primary order promotion and retained alternate tests

**stronger local predicate with a complete existing-witness construction.** Use g_H at order 45, primary g(U_A) at order 12, and g(U_S),g(U_T),g(U_Z) at order 1; leave every conjugated f(V_i) test at order 1. The complete source order list is (45,12,1,1,1,1,1,1,1,1,12,45,45,45,45,45). The squared primary tests reuse f=g^2. At consumed contacts delta is a unit, so order 12 on g(U_A) implies the former order 1 premise at the same common place. Completeness chooses U_A=[n]H with integral n=beta(X); the existing Pi^44 progression puts H and hence U_A in formal depth 45. This equality is used only for the constructed completeness witnesses. The identity U_A=O is allowed and no alternate-depth condition is strengthened.

**Current consumer:** `tests`, `test1`, `squareTests`, `testSquare.1`, `testSquare.12`, `testSquare.45`. Inherited inputs: G_formal, G_one_place, G_prime_pattern, G_reductions.

**Proof:** [proofs/prior/round4/geometry_round4.tex](proofs/prior/round4/geometry_round4.tex) — Inverse-root tests and the shared primary depth; [proofs/prior/round6/detector_round6.tex](proofs/prior/round6/detector_round6.tex) — Arbitrary-order local consumer and Pi^44 progression; [proofs/detector_round8.tex](proofs/detector_round8.tex) — The actual test whose order changes; existing formal depth supplies its completeness.
Predicate strengthening is not a bijection on all old detector witness tuples. No new congruence or prime-selection condition is imposed.

### T08 — Grouped products and a uniform order 12 pair

**exact polynomial identity with shared quadratic gates.** Evaluate one uniform (12,12) pair, two groups of four order 1 factors and two groups of three order 45 factors. If U=g(U_A)^2 and V=D_cross^2, use 1+q12(U+V)+q12^2 UV. The shared field coefficient UV is retained, and q12^2 already exists as mixedHigh in the high-weight chain. The product identity is over the commutative field K; the primary predicate strengthening is justified separately in T07. No arithmetic distinctness or nonzero test is needed. Each detector deletes only the former q1*q12 coordinate, saving three coordinates in total.

**Current consumer:** `polyProduct`, `mixedTestProduct`, `coeffs`, `evalSym`, `detector*.mixed`, `detector*.W`. Inherited inputs: none beyond exact algebra and the stated domain.

**Proof:** [proofs/prior/round4/mixed_detector_block.tex](proofs/prior/round4/mixed_detector_block.tex) — Retained shared symmetric coefficients and remaining product groups; [proofs/detector_round7.tex](proofs/detector_round7.tex) — Retained direct weights and high-order chain; [proofs/detector_round8.tex](proofs/detector_round8.tex) — The shared uniform block and its exact cost.
All 16 underlying test functions are retained. q12-squared reuse is an actual stored-coordinate reuse, not an unmaterialized degree-three substitution.

### T09 — Three positive square scales and their height allowance

**real inequality and height-bound transfer.** Use the decoded square scales1,C0^2,(C0+C1)^2 for C=product x(Q_i). Real bounds give C0>=193 and C0+C1>=61. With alpha=577/32 and the selected H, the height transfer remains B^2-6<7H|N|^(alpha/k), including log50 for the fractional-linear coordinate change. Four roots are finite double points; oddness is required for product-height, not real positivity. Scales are fixed before prime selection, and coincident scales are allowed. After two-prime balancing the stored first scale coordinate is not itself the semantic square: decode A=C0^2=2^-19*y_scale before applying arithmetic arguments.

**Current consumer:** `heightProduct`, `heightProduct.scale0`, `heightProduct.scale1`, `scales`. Inherited inputs: G_curve, G_product_height, G_height_geometry.

**Proof:** [proofs/prior/round5/detector_final.tex](proofs/prior/round5/detector_final.tex) — One fewer coordinate for the third height scale; [proofs/prior/round5/arithmetic_round5.tex](proofs/prior/round5/arithmetic_round5.tex) — Retained three-scale transfer and log50 allowance; [proofs/arithmetic_round8.tex](proofs/arithmetic_round8.tex) — Apply the new height bound to the actual consumers; [proofs/diagonal_scaling_round8.tex](proofs/diagonal_scaling_round8.tex) — Decode the stored first height-scale coordinate.
Upstream application: `docs/quartic-523-540/addition.tex` (`v9:lem:product`, `v9:cor:scales`).

### T10 — Shifted contact coordinate and guard

**exact rational coordinate and local-unit calculation.** phi(t)=-49+1/t maps Theta={0,1/49,1/50,1/2450,32/1225} to the five height contacts; delta=98t-1 is a unit at consumed contacts outside S6. Unimodular matrix; contact denominators/differences supported at 2,3,5,7 and guard values introduce 13. A pole of t maps to -49, not a consumed contact outside S6.

**Current consumer:** `detector*.t`, `detector*.F`, `delta`, `roots`. Inherited inputs: G_height_geometry, G_one_place.

**Proof:** [proofs/prior/round5/arithmetic_round5.tex](proofs/prior/round5/arithmetic_round5.tex) — Choose the detector coordinate and guard together; [proofs/prior/round5/detector_final.tex](proofs/prior/round5/detector_final.tex) — Selected contacts, positivity and the guard; [proofs/detector_round7.tex](proofs/detector_round7.tex) — The normalization freedom in the actual local lemma.

### T11 — Positive lambda witnesses and removal of trace guards

**witness restriction with canonical completeness and forced nonzero domain.** Impose lambda=32/1225+u^2+v^2. All factors of W are >=1 in both embeddings, so W0>=1,N(W)>0 and no separate W0 inverse is needed. A>=1 and the direct weight equation force F>0. Completeness uses the retained unit-scale maximal-contact prime p=N(pi), divided by the square denominator; arbitrary positivity alone would not supply the two-square witnesses.

**Current consumer:** `lambda.positiveChart`, `lambda.positiveA`, `lambda.positiveB`, `detector*.normOver2w0`. Inherited inputs: G_prime_pattern, G_progression.

**Proof:** [proofs/prior/round3/positivity_proof.tex](proofs/prior/round3/positivity_proof.tex) — Domains from positivity; canonical Gaussian witnesses; [proofs/prior/round5/detector_final.tex](proofs/prior/round5/detector_final.tex) — Selected current contact and positivity chart; [proofs/detector_round7.tex](proofs/detector_round7.tex) — Nonzero domains and quadratic degree; [proofs/detector_round8.tex](proofs/detector_round8.tex) — Uniform pair factors remain positive; every reciprocal/norm denominator is retained.

### T12 — Contact-unit test normalization

**local predicate transfer with rechecked completeness.** The semantic tests are delta*D_j with R=F/(A^5 delta^6), and implemented factors use q_m=e^(2m-1)/delta. Delta is a contact unit, so this normalization preserves the specified contact order. The selected order list has eight order 1, two order 12 and six order 45 tests, including the separately justified primary promotion. The one-place lemma accepts arbitrary K-valued normalized inputs; delta is a unit only at consumed contacts. R and its square-denominator formula are unchanged. Every fixed-order weight is O(lambda^-1). The small-prime lower bound remains nu+(10m-6)(eta+gamma)-2c_p; for the promoted test m=12 gives nu+114(eta+gamma)-2c_p. All finite/real bounds are fixed before the later progression and prime choices. Here nu=v_p(v), eta=v_p(A), and gamma=v_p(98); this local gamma is unrelated to the global height exponent alpha.

**Current consumer:** `tests`, `detector*.mixed`, `detector*.E1`, `detector*.E45`, `detector*.B`. Inherited inputs: G_one_place, G_pole, G_prime_pattern, G_progression.

**Proof:** [proofs/detector_round7.tex](proofs/detector_round7.tex) — Normalization freedom and retained contact/off-contact/real estimates; [proofs/detector_round8.tex](proofs/detector_round8.tex) — Changed factor at contacts, real infinity and 2,3,17.
Upstream application: `manuscripts/quartic_v10.tex` (`lem:v5-one-place`, `v5:preparation-zero-bridge`, `lines 11220--11241`).

### T13 — Direct q1 and the seven higher-weight gates

**unique rational extension and shared circuit.** Define q1 F=A(A delta)^4 and E=q1 delta^2=R^-1. Compute E^2,E^3,E^3q1^3,(E^3q1^3)^2,q12, q12^2,q45; q12=E^11 q1^12,q45=E^44 q1^45. F,q1,E positive; quotient denominators E and q1^3 nonzero. delta^2 reuses t^2. The q1 square/cube are actual existing product-evaluation powers. No stored e or delta^3 survives.

**Current consumer:** `detector*.q1`, `detector*.eDelta`, `detector*.mixA through mixD`, `detector*.q12`, `detector*.q45`, `detector*.E1.power2`, `detector*.E1.power3`. Inherited inputs: none beyond exact algebra and the stated domain.

**Proof:** [proofs/detector_round7.tex](proofs/detector_round7.tex) — Compute the weights without storing e; Nonzero domains and quadratic degree; [proofs/detector_round8.tex](proofs/detector_round8.tex) — mixedHigh=q12^2 is reused by the uniform pair without an additional gate.

### T14 — Reciprocal-trace norm quotient

**exact field identity with proved domain.** For W=W0+W1*rho, n=N(W)/(2W0)=1/Tr(W^-1) and B=n^2/E=R/Tr(W^-1)^2. Total positivity of W supplies W0>0,N(W)>0,T!=0 before any pole predicate. At selected contacts trace residue 1 or 2 is a unit; elsewhere even R valuations stay even after division by a rational square.

**Current consumer:** `detector*.normOver2w0`, `detector*.B`, `detector*.Bsemantic`. Inherited inputs: G_one_place, G_pole.

**Proof:** [proofs/prior/round3/positivity_proof.tex](proofs/prior/round3/positivity_proof.tex) — positive norm and trace domains; [proofs/detector_round7.tex](proofs/detector_round7.tex) — Nonzero domains; contact/off-contact completeness; [proofs/detector_round8.tex](proofs/detector_round8.tex) — Changed factor retains contact trace residues, positivity and off-contact parity.

### T15 — Homogeneous pole coordinates

**input-fixed rational witness equivalence.** Normalize old e,p,s,q by b,b,b,b^2 respectively. For unprepared poles T=b; for prepared poles T=U^2/b. The two normalized conics use 17b and e(17-T). Only b and b^2 are divided by; b>0 is supplied independently by detector or scalar positivity. Keep all degenerate e,p,q,s branches permitted by the original predicate.

**Current consumer:** `pole`, `detector*.firstConic`, `detector*.secondConic`, `scalar.firstConic`, `scalar.secondConic`. Inherited inputs: G_pole.

**Proof:** [proofs/prior/round3/arithmetic_proof.tex](proofs/prior/round3/arithmetic_proof.tex) — Independent review of homogeneous pole coordinates.
Upstream application: `manuscripts/quartic_v10.tex` (`hyp:o8-pole`, `v5:preparation-zero-bridge`).

### T16 — Conic scalar preparation and square absorption

**rational witness equivalences including the parametrization endpoint.** Replace the rational preparation parametrization by U^2+bV^2=b^2 and use T=b-V^2,U^2=bT. For b=r_corr W^2 with r_corr=42r, rescale p,q by W and U by1/W, making r_corr the actual conic coefficient. b>0,W>=1. The omitted parametrization endpoint U=-b,V=0 is handled by changing U to +b because downstream uses its square. No extra nonzero condition on a pole witness is inserted.

**Current consumer:** `scalar.preparationT`, `scalar.preparationConic`, `scalar.correctedR`, `scalar.W2`, `pole`. Inherited inputs: G_pole.

**Proof:** [proofs/prior/round2/further_arithmetic_body.tex](proofs/prior/round2/further_arithmetic_body.tex) — One fewer coordinate for scalar preparation; [proofs/prior/round3/arithmetic_proof.tex](proofs/prior/round3/arithmetic_proof.tex) — homogeneous pole coordinates and three-coordinate preparation; [proofs/prior/round4/scalar_streamlining.tex](proofs/prior/round4/scalar_streamlining.tex) — Absorb the known square in the scalar pole input; [proofs/geometry_round7.tex](proofs/geometry_round7.tex) — unchanged pole consumer and W>=1.

### T17 — Current input map, three scalar contacts and correction 42

**local/global-consumer transfer for a new input label.** beta=2401+2754(2X+1)^2; r=beta(beta-1)(32beta+343); correction 42. Infinity and 2401 have even contact order, and the irrelevant 1/2 contact is absent. The anchor excludes X=-1/2 before the height theorem omitting beta=2401 is used. At consumed primes only 0,1,-343/32 can have odd contact. For integer X,42r is positive and locally square at 2,3,17.

**Current consumer:** `beta`, `scalar.rPair1`, `scalar.rThree`, `scalar.correctedR`. Inherited inputs: G_height_geometry, G_pole, G_progression.

**Proof:** [proofs/prior/round2/further_arithmetic_body.tex](proofs/prior/round2/further_arithmetic_body.tex) — exact contact set and removed 2beta-1 factor, as predecessor; [proofs/prior/round3/arithmetic_proof.tex](proofs/prior/round3/arithmetic_proof.tex) — Make one finite contact a square fibre; Fixed local correction and completeness; [proofs/geometry_round7.tex](proofs/geometry_round7.tex) — Odd contact valuations are already positive; [proofs/arithmetic_round8.tex](proofs/arithmetic_round8.tex) — Selected even anchor excludes X=-1/2 before applying the new height estimate.

### T18 — Adapted input coordinate and final integrality recovery

**input-fixed affine change plus denominator argument.** Store Y=X^2+X, use beta=11016Y+5155 and X^2=Y-X. Once n=beta is integral and the anchor gives X integral at 2,3, every denominator prime is excluded, including 17 via its coefficient valuation 1. X itself stays coordinate 0. Y and the physical anchor/scales stay materialized for lifted-degree control. The argument requires the current polynomial, not an arbitrary rational label.

**Current consumer:** `inputProduct`, `inputSquare`, `beta`, `anchor.physicalA`. Inherited inputs: G_height_geometry, G_quaternion, G_lucas.

**Proof:** [proofs/prior/round3/arithmetic_proof.tex](proofs/prior/round3/arithmetic_proof.tex) — Keep the input gate adapted to the new label; final input denominator argument; [proofs/arithmetic_round8.tex](proofs/arithmetic_round8.tex) — Actual input contradiction and final denominator-prime recovery.

### T19 — Packed parity from the abscissa product

**uniform local proof replacing private odd-chart witnesses.** For each nonzero root index n, normalized x([n]P) has residue rho or 2rho at 3. Hence v3(C0)=-sum e(n_i), so 3-integrality of C0 forces all four labels odd before product-height use. e(n)=0 for odd n and 2+2v3(n) for even n. Negative indices and all chart signs are covered; this is not inferred from finite samples. Old odd-chart witnesses can be restored existentially on odd labels.

**Current consumer:** `heightProduct`, `heightProduct.scale0`, `anchor.physicalA`, `anchor.equation`. Inherited inputs: G_curve, G_formal, G_quaternion.

**Proof:** [proofs/prior/round1/packed_anchor_note_body.tex](proofs/prior/round1/packed_anchor_note_body.tex) — Leading residues; one coefficient detects all four parities; projection/sign recovery; [proofs/arithmetic_round8.tex](proofs/arithmetic_round8.tex) — Retained even anchor: force oddness at 3 before any product-height use.
Upstream application: `docs/quartic-523-540/addition.tex` (`v9:prop:odd-chart`).

### T20 — Field-norm anchor with local input tests

**local predicate equivalence through the quaternion criterion.** Use Theta=N(w)+3S0 N(4096C0+X*rho), with the three-witness anchor. Opposite 3-adic parity separates the two norms; after parity is known, the dyadic condition forces X integral at 2. At 3, N is anisotropic and the basis is integral. Use the correct order: first force odd roots at 3, then derive 2-integrality of 4096C0 and w; only then isolate -6X^2. The quaternion criterion includes zero argument.

**Current consumer:** `anchor.physicalA`, `anchor.equation`, `inputSquare`, `heightProduct.scale0`. Inherited inputs: G_quaternion, G_formal, G_curve.

**Proof:** [proofs/prior/round3/arithmetic_proof.tex](proofs/prior/round3/arithmetic_proof.tex) — Use the existing quadratic field norm in the anchor; [proofs/prior/round6/arithmetic_round6.tex](proofs/prior/round6/arithmetic_round6.tex) — Exact anchor equivalence; dyadic condition; [proofs/arithmetic_round8.tex](proofs/arithmetic_round8.tex) — Selected even anchor domain and its noncircular local order.

### T21 — Stored-root physical anchor and selected depth

**local equivalence and checked numerical specialization.** Use N(w) in the physical anchor, where w=h_S*tau and tau^2=f(S-P), and set S0=3^2364. The exact point/input domain is four odd roots, X integral at 2 and 3, and 0!=a-1 in 2*3^1181 Z. For odd a, h_S is a 3-adic unit and v3(w)=1+v3(a-1). At 2, v(h_S)=-3/2 and v(w)=v2(a-1)>=1. The even-exponent formula is used; no optional odd-exponent generalization is needed.

**Current consumer:** `scalar.shiftedS.w`, `anchor.physicalA`, `fixedParameter`. Inherited inputs: G_curve, G_formal, G_quaternion.

**Proof:** [proofs/prior/round6/arithmetic_round6.tex](proofs/prior/round6/arithmetic_round6.tex) — Exact stored-root anchor equivalence for arbitrary even exponents and the dyadic argument; [proofs/arithmetic_round8.tex](proofs/arithmetic_round8.tex) — Retained even anchor and noncircular local order; exact margins for 2364.
The packing coefficient is still three. Old 2790/depth 1394 is a prior numerical specialization, not a current constraint. No odd-exponent generalization is used.

### T22 — Fused scalar shift and its indispensable guard

**rational function recovery on an explicit nonzero domain.** Store w through (x_P*x_S+D)w=h_P*h_S*j_S-x_S*j_P and x_S f(Q)=w^2. Delete the old M,k_Q outputs but retain the rational inverse of f(Q)_0. x_S and the first denominator are nonzero/positive. f(Q)_0=tau0^2+2tau1^2, so its inverse excludes Q=O/S=P and permits recovery of M=-(x_P+D f)/w. Tangency S=-P remains.

**Current consumer:** `subtractRootConstant`, `scalar.shiftedS.rootTimesInverseRoot`, `scalar.shiftedS.f`, `scalar.shiftedS.nonzeroRealF`. Inherited inputs: G_curve.

**Proof:** [proofs/prior/round4/geometry_round4.tex](proofs/prior/round4/geometry_round4.tex) — Fuse the scalar reciprocal difference; [proofs/prior/round5/geometry_round5.tex](proofs/prior/round5/geometry_round5.tex) — Restore exactly the deleted nonzero restriction.

### T23 — Real scalar proxy and the split 41 case

**two-place valuation replacement, not exact-ratio equality.** T0=Re(k_H*w) satisfies vp(T0)=vp((a-1)/h) once all four f(H),f(Q) coefficients are positive at the consumed prime. Only this rational coefficient is tested. Use both places when split. The recovered identity h_P(w*k_Q+h_P)+D f+j_Pw=0 gives w*k_Q=-h_P mod p; when h_P is nonunit at 41 use integrality of h_S instead of dividing by h_P. Trace of -h_P is 2.

**Current consumer:** `scalar.ratioProxyReal`, `scalar.directLeaf`, `scalar.leaf4`. Inherited inputs: G_formal, G_curve.

**Proof:** [proofs/prior/round4/scalar_streamlining.tex](proofs/prior/round4/scalar_streamlining.tex) — Use only the real coefficient of the scalar ratio; [proofs/prior/round5/geometry_round5.tex](proofs/prior/round5/geometry_round5.tex) — Uniform two-place trace argument including 41; completeness.

### T24 — Inverse 15 scalar chain and outer constant

**uniform scalar predicate transfer with full preparation.** Use kappa=r^-15 and y=T0/r^16. Set n=B^2/r^2+C^2/r, L=A^2/r+n^2/r^2, J=D^2+kappa*y^2, N=L^2+kappa*J^2, W=1+N. The conclusion remains M_S(beta)^28 | a-1. Actual beta makes any odd R=vp(r) positive. From W bound use N=W-1 by ultrametric inequality, allowing cancellation. Opposite parity inside each norm yields positivity of the first four coefficients before proxy, then vp(T0)>217R/8 and uniform lower bound >=28. Completeness uses the displayed finite bounds; no 28R claim.

**Current consumer:** `scalar.rInverse3`, `scalar.rInverse7`, `scalar.rInverse15`, `scalar.ratioProxyLeaf`, `scalar.n1OverR`, `scalar.nLeft`, `scalar.N`, `scalar.W`. Inherited inputs: G_pole, G_formal, G_progression.

**Proof:** [proofs/prior/round6/geometry_round6.tex](proofs/prior/round6/geometry_round6.tex) — inverse-weight chain and retained right-branch bounds; [proofs/geometry_round7.tex](proofs/geometry_round7.tex) — all sections: actual input positivity, outer constant, valuation descent and explicit preparation.

### T25 — Finite exceptional set in the height application

**reapplication of an inherited global proof to checked support.** Use S6={2,3,5,7,13,17} and B_S=46410. The five-contact geometry, local logarithms, contact units and pole obstruction satisfy their actual hypotheses outside this set. The new global estimate is h(z)<=H M_S(z)^(577/32), with H defined in T27 and derived in T32. Ramification support contains the fixed geometric bad primes, and even contacts introduce no new ramification. Each removal of a printed large cutoff is justified at its actual consumer. The Euler-product cutoff53 is numerical and does not add53 to S6 or remove its detector contacts. Completeness may still select primes>76176.

**Current consumer:** `tests`, `detector*.F`, `scalar.r`, `all height consumers`. Inherited inputs: G_height_geometry, G_formal, G_one_place, G_pole.

**Proof:** [proofs/prior/round4/arithmetic_round4.tex](proofs/prior/round4/arithmetic_round4.tex) — Finite-support reapplication of the geometry and LR proof with checked local consumers; [proofs/prior/round5/arithmetic_round5.tex](proofs/prior/round5/arithmetic_round5.tex) — Current contact set, conductor and logarithm exceptions; [proofs/arithmetic_round8.tex](proofs/arithmetic_round8.tex) — Precise inherited height inputs and elementary Euler-product refinement.

### T26 — QM commutant and sharper conductor constant

**conditional refinement of degree/conductor applications.** L-defined QM gives Gal(L(A[11])/L) in GL2(F11), hence degree divides 2^10*3^3*5^2*11. Full L-defined 3-torsion gives good reduction at 2,5,7; sharper different integration yields a 2<=34,a 3<=11,a 5,a 7<=2 and N<=2^32*3^9 R^2. Use divisibility, not only a degree upper bound. All endomorphisms are L-defined; 3-torsion theorem requires n>=3 prime to residue characteristic; at 3 retain 11-torsion field. Scalar character/cochain extensions, normality and companion at 3 conductor at 5 are retained.

**Current consumer:** `fixed numerical height constant consumed by arithmetic proof`. Inherited inputs: G_height_geometry.

**Proof:** [proofs/prior/round4/qm_conductor_anchor16.tex](proofs/prior/round4/qm_conductor_anchor16.tex) — An exact degree divisibility bound: matrix-unit commutant argument; [proofs/prior/round5/arithmetic_round5.tex](proofs/prior/round5/arithmetic_round5.tex) — Use the full three-torsion; Retain the sharp term in the different formula; [proofs/arithmetic_round8.tex](proofs/arithmetic_round8.tex) — Explicit reuse of N<=C R^2, rad(N)|R and t<=4608R with primitive-level and character-order conventions.
Upstream application: `manuscripts/quartic_v10.tex` (`lines 6861--7006`, `lines 7090--7405`, `lines 8915--9073`).

### T27 — Selected height constant and the three actual contradictions

**checked applications of inherited height and Lucas inputs.** Set alpha=577/32 and H=3*2^106*(2^32*3^9)^6*46410^18+128, a 665-bit integer. At S0=3^2364, scalar order 28 gives h(beta)<c/4<=(|a|+1)/4, c=|a-1|. High order 45 forces the literal Lucas residual F=0; input order 12 then forces n=beta. The previous c/80 target is not required or claimed. Use B^2-6<7H|N|^(alpha/k), |F|<5B^4, and b!=0. For c_*=2*3^1181 and b_*=c_*-1, exact checks give c_*^319>(4H)^896 and b_*^143>(24H)^360. Also 40H<2^670 and 100*670<b_* imply log(40H)<|a|/100. Thus input comparison gives log B<(487/500)|a|+19/20<|a|-3 for |a|>152, contradicting the inherited Lucas bound.

**Current consumer:** `Lucas.C`, `Lucas.AT`, `Lucas.F0`, `Lucas.F1`, `test14`, `test15`, `fixedParameter`, `anchor.equation`. Inherited inputs: G_height_geometry, G_product_height, G_lucas, G_curve.

**Proof:** [proofs/prior/round5/arithmetic_round5.tex](proofs/prior/round5/arithmetic_round5.tex) — Retained conductor inputs, log50 allowance and three-scale height transfer; [proofs/arithmetic_round8.tex](proofs/arithmetic_round8.tex) — New height bound and all three actual consumers, including the weaker sufficient scalar target.
Upstream application: `docs/quartic-523-540/addition.tex` (`subsec:v9-soundness`, `v9:eq:height-transfer`).
The uniform global reapplication is separately exposed in T32. Optional projective-height or odd-anchor results and the exploratory high44 alternative are not selected.

### T28 — Deeper-primary completeness and choice order

**global witness construction using inherited inputs.** Fix scalar preparation, roots, square scales and continuity modulus first. Choose separated Gaussian contact primes and solve h=0 mod Pi^44*M_minus,h=1 mod M_plus,h=h0 mod L. Alternate points retain depth 1; every constructed primary U_i=[n_i]H has depth at least45, which supplies the promoted U_A order 12 test. Use gcd(Pi,M_plus*L)=1 and direct-target doubling-image orders. Repeated forms retain their incidences. Do not demand that the same prime divide both h and h-1. Real and small-prime test bounds are fixed before prime selection. The finite3^1181 divisibility of a-1 is supplied by the existing arbitrary-divisibility scalar preparation.

**Current consumer:** `H and U_i witness construction`, `lambda positivity witnesses`, `all three detector poles`, `scalar preservation`. Inherited inputs: G_prime_pattern, G_reductions, G_progression, G_formal, G_pole, G_lucas.

**Proof:** [proofs/prior/round4/geometry_round4.tex](proofs/prior/round4/geometry_round4.tex) — Actual deeper-primary CRT consumer; [proofs/prior/round6/arithmetic_round6.tex](proofs/prior/round6/arithmetic_round6.tex) — High order 45 and Pi^44 progression; [proofs/detector_round7.tex](proofs/detector_round7.tex) — Retained contact-unit pole limits; [proofs/geometry_round7.tex](proofs/geometry_round7.tex) — Current scalar preparation; [proofs/detector_round8.tex](proofs/detector_round8.tex) — Integral formal multiplication and changed-factor completeness; [proofs/arithmetic_round8.tex](proofs/arithmetic_round8.tex) — Finite anchor 2364 divisibility and completeness choice order.
Upstream application: `docs/quartic-523-540/addition.tex` (`lem:v9-bridge`, `v9:lem:separation`, `subsec:v9-deep-completeness`); `manuscripts/quartic_v10.tex` (`lines 11220--11354`).

### T29 — Materialized anchor and affine translation

**invertible private-coordinate change and degree preservation.** Keep Theta, C0^2 and Y materialized; translate u=S0+(U-3V+3W)/4,v=S0/2+V/4,w=3S0/2+W/4. The anchor becomes -48Theta^2+U^2-6UV+6UW+15V^2-18VW+7W^2+8S0U=0. The affine map has nonzero rational determinant and fixes X. No cubic S0*C0^2 or substitution of Theta into its square is allowed. All rows stay quadratic if S0 is later lifted.

**Current consumer:** `anchor.physicalA`, `raw-translated-ir.json`, `anchor.equation`, `protected coordinate flags`. Inherited inputs: none beyond exact algebra and the stated domain.

**Proof:** [proofs/prior/round1/packed_anchor_note_body.tex](proofs/prior/round1/packed_anchor_note_body.tex) — Projection, quadratic degree, and source dependencies; [proofs/prior/round3/arithmetic_proof.tex](proofs/prior/round3/arithmetic_proof.tex) — adapted protected input coordinate; [proofs/diagonal_scaling.tex](proofs/diagonal_scaling.tex) — actual translated anchor row and exponent span; [proofs/diagonal_scaling_round8.tex](proofs/diagonal_scaling_round8.tex) — Selected ternary/dyadic map and rational primitive normalization after the same affine anchor translation.
Upstream application: `docs/quartic-523-540/addition.tex` (`subsec:v9-finite`).

### T30 — Certified compilation and complete SOS

**exact rational algebra and input-projection preservation.** The generic compiler preserves the rational zero projection and produces389 coordinates and 357 quadratic rows from 400 source coordinates and 368 residuals; no further elimination is used. Primitive nonzero rational row normalization followed by the complete sum of squares gives a quartic with the same rational zero set. Every removed coordinate has the displayed reversible pivot/assignment map. Coordinate0 is fixed, protected anchor/input/scale values remain materialized, and quotient domains remain separate proved obligations. Exact finite algebra does not establish the global arithmetic interpretation.

**Current consumer:** `construction/compiled/reduction-certificate.json`, `construction/final/verification.json`, `construction/compiled/polynomial.json`, `construction/tools/checker.cjs`. Inherited inputs: none beyond exact algebra and the stated domain.

**Proof:** [proofs/detector_round8.tex](proofs/detector_round8.tex) — Measured construction and verification scope:339 gate identities and 330 compiler operations; [proofs/geometry_round7.tex](proofs/geometry_round7.tex) — Retained scalar implementation and degree; [proofs/diagonal_scaling_round8.tex](proofs/diagonal_scaling_round8.tex) — Nonzero rational row rescaling and 357-row SOS equivalence.

### T31 — Two-prime balancing of the complete decimal quartic

**input-fixed rational diagonal bijection and row scaling.** With c=3^394 and S0=c^6, use old x_i=2^b_i*3^a_i*new y_i on13 existing coordinates. Twelve have the retained ternary factors c,c^2,c^4; two have dyadic factors, with one overlap: S.chart.x.0.quadratic gains2 and heightProduct.scale0.quadratic gains2^-21. Clear row denominators, divide by each nonzero signed rational content, and square/sum all 357 rows. The map is an input-fixed rational bijection and introduces no new variable or root choice. Decode every changed stored coordinate before interpreting semantic point functions or square scales. The scale value A=C0^2 becomes2^-19*y_scale, so y_scale need not itself be square. Five row divisors are nonintegral, with denominator 2^21 three times,2^42 once and 2^13 once. Each exact nonzero divisor is certified.

**Current consumer:** `construction/balanced/diagonal-certificate.json`, `construction/balanced/integer-ir.json`, `construction/balanced/polynomial.json`, `construction/quartic-389-balanced-decimal.txt`. Inherited inputs: none beyond exact algebra and the stated domain.

**Proof:** [proofs/diagonal_scaling.tex](proofs/diagonal_scaling.tex) — Retained ternary exponent-span derivation, with its earlier numerical example classified as prior; [proofs/diagonal_scaling_round8.tex](proofs/diagonal_scaling_round8.tex) — Complete13-coordinate map, rational row divisors, and exact full-table coefficient comparison.
The exact coefficient maximum is28902*3^1576, with 757 decimal digits and 2513 bits. The complete quartic has26,295 monomials, degree 4, content 1 and coefficient 1 on X^4; every one of the 389 coordinates occurs. Floating-point search is not a verification dependency or an optimality certificate.

### T32 — Euler-product and genus improvement of the global height bound

**conditional uniform reapplication of inherited geometric and height inequalities.** For all positive N, product_(p|N)(1+1/p)<(32/9)*rad(N)^(1/192). Thus d_H<T=2^14*C*R^(577/192). The retained surface realization gives g>=2; combined with g<=1+d_H/12 it gives g< T/6. Javanpeykar, the retained variation bound V<=T^6 and Bost yield h_F(A)<2^106*C^6*R^(577/32), including the CM branch by domination. The geometric comparison and 46410^(1/32)<3/2 give the H used in T27. Here R=46410*M_S(z) is the global height radical, distinct from the detector pole parameter R in T10–T14. The exact small-prime list consists of all 15 primes below 53; every normalized factor exceeds 1, their product is <32/9, and the monotone tail is <=1. The modular subgroup contains -I, so d_H has no extra factor 2; t is the nebentypus order, not the coefficient-field degree. The same stable Faltings metric, primitive level, rad(N)|R and normal-field hypotheses are retained. This uses the actual intermediate proof rather than only its final exponent 19 conclusion.

**Current consumer:** `fixedParameter: S=3^2364`, `scalar order28 height consumer`, `Lucas order45 height consumer`, `input order12 height consumer`. Inherited inputs: G_height_geometry.

**Proof:** [proofs/prior/round4/arithmetic_round4.tex](proofs/prior/round4/arithmetic_round4.tex) — Finite-support geometry and LR reapplication; [proofs/prior/round5/arithmetic_round5.tex](proofs/prior/round5/arithmetic_round5.tex) — Sharper conductor C=2^32*3^9; [proofs/arithmetic_round8.tex](proofs/arithmetic_round8.tex) — Euler-product refinement; Jacobian and isogeny-height bounds.
Upstream application: `manuscripts/quartic_v10.tex` (`sec:h5-level-repair`, `thm:quartic-height19`, `lines8915--9073`).
The new exponent is577/32=18.03125. No new global theorem is asserted proved, no exceptional prime is added, and no asymptotic exponent 18 estimate or optimal constant is claimed.

## Proof catalog: selected arguments and prior derivations

The JSON inventory binds all 30 proof texts. Their roles below distinguish selected statements from prior numerical examples.

| Proof | Role in the selected construction |
|---|---|
| [proofs/prior/round1/packed_anchor_note_body.tex](proofs/prior/round1/packed_anchor_note_body.tex) | Active uniform leading-residue/product-parity argument; old anchor form and numerical exponent are superseded. |
| [proofs/prior/round1/additional_circuit.tex](proofs/prior/round1/additional_circuit.tex) | Historical exact scalar-leaf fusion; its literal circuit is superseded by the current real proxy. |
| [proofs/prior/round2/birational-proof.txt](proofs/prior/round2/birational-proof.txt) | Historical normalized finite charts; their literal equations are superseded by complete reciprocal/joint charts. |
| [proofs/prior/round2/further_arithmetic_body.tex](proofs/prior/round2/further_arithmetic_body.tex) | Active conic-preparation argument and predecessor of local-input packing; old label, correction 21, four contacts and six difference guards are superseded. |
| [proofs/prior/round2/further_arithmetic_proof.txt](proofs/prior/round2/further_arithmetic_proof.txt) | Prior detailed arithmetic text; use with its displayed domains, not its superseded numerical parameters. |
| [proofs/prior/round2/scalar-preparation-proof.txt](proofs/prior/round2/scalar-preparation-proof.txt) | Active rational conic/parametrization equivalence for positive b, including the omitted endpoint; positivity is now supplied by current r and W. |
| [proofs/prior/round3/arithmetic_proof.tex](proofs/prior/round3/arithmetic_proof.tex) | Active field-norm packing, current beta/r/correction 42, adapted input coordinate, and homogeneous pole maps; old scalar order and anchor exponent are superseded. |
| [proofs/prior/round3/geometry_proof.tex](proofs/prior/round3/geometry_proof.tex) | Active complete reciprocal point/subtraction and scaled-log arguments, including identity/tangent cases; shared H and scalar equations are refined later. |
| [proofs/prior/round3/positivity_proof.tex](proofs/prior/round3/positivity_proof.tex) | Active Gaussian-witness/positive-product mechanism; old contact 1/2399 and guard t-1 are replaced by current contact 32/1225 and guard 98t-1. |
| [proofs/prior/round4/arithmetic_round4.tex](proofs/prior/round4/arithmetic_round4.tex) | Active reapplication of the height proof to finite ramification support and checks of actual local consumers; scalar order 24, old exceptional set and anchor 19 are not current. |
| [proofs/prior/round4/detector_reduction_proof.txt](proofs/prior/round4/detector_reduction_proof.txt) | Retained inverse-root and local mixed-product derivation; the literal high-order 40 weights and the old unequal pair are superseded. |
| [proofs/prior/round4/geometry_round4.tex](proofs/prior/round4/geometry_round4.tex) | Active joint H/H-P chart, scalar w fusion, inverse-root tests and input-only G2 argument; replace printed high order 40/CRT Pi^39 by current 45/Pi^44 via later proof. |
| [proofs/prior/round4/mixed_detector_block.tex](proofs/prior/round4/mixed_detector_block.tex) | Retained shared symmetric-product identities and coefficient construction; the selected pair is now uniform (12,12), replacing the displayed (1,12) pair. High-order groups remain 3+3 at order 45. |
| [proofs/prior/round4/qm_conductor_anchor16.tex](proofs/prior/round4/qm_conductor_anchor16.tex) | Active quaternionic commutant and degree-divisibility argument; its conservative conductor constants and anchor 16 are superseded. |
| [proofs/prior/round4/scalar_streamlining.tex](proofs/prior/round4/scalar_streamlining.tex) | Active two-place real-coefficient principle and square absorption in the scalar pole; exact-ratio leaf/tree are superseded. |
| [proofs/prior/round5/arithmetic_round5.tex](proofs/prior/round5/arithmetic_round5.tex) | Retained three-torsion/sharp-different conductor constant, contacts, guard, exception set, input-log estimates and three-scale height transfer. Its exponent 19 height constant, high order 44 and numerical anchor are superseded. |
| [proofs/prior/round5/detector_final.tex](proofs/prior/round5/detector_final.tex) | Active linear-combination square scale, log 50 height allowance, contact positivity and Gaussian witnesses; old weight chain/order 44 are superseded. |
| [proofs/prior/round5/geometry_round5.tex](proofs/prior/round5/geometry_round5.tex) | Active G12 completion/nonvanishing and scalar real proxy with its f(Q)_0 guard and split 41 argument. |
| [proofs/prior/round6/arithmetic_round6.tex](proofs/prior/round6/arithmetic_round6.tex) | Active stored-root norm anchor equivalence for arbitrary even exponents and high order 45 logarithm bound; selected 3072 and its constant chains are superseded. |
| [proofs/prior/round6/detector_round6.tex](proofs/prior/round6/detector_round6.tex) | Retained high-order 45 comparison and Pi^44 compatibility; literal delta^-3 weights are superseded by round 7 normalization and round 8 uniform pairing. |
| [proofs/prior/round6/geometry_round6.tex](proofs/prior/round6/geometry_round6.tex) | Active inverse15/right-branch and proxy-scaling argument; old left subtree/constant position is replaced by round 7. |
| [proofs/prior/round6/inverse_weight_family.tex](proofs/prior/round6/inverse_weight_family.tex) | Optional precision-family research; no general member or stronger scalar order from this file is a dependency of selected 389. |
| [proofs/detector_round7.tex](proofs/detector_round7.tex) | Retained contact-unit normalization, direct q1/E weights and local/pole estimates. Its old (1,12) pairing, order allocation and 392-count example are superseded by the round 8 primary promotion. |
| [proofs/geometry_round7.tex](proofs/geometry_round7.tex) | Current unchanged outer-constant scalar tree, actual-input odd-valuation argument and completeness preparation. |
| [proofs/arithmetic_round7.tex](proofs/arithmetic_round7.tex) | Prior anchor 2790 specialization and exponent 19 numerical margins. Uniform even-anchor arguments remain available, but the selected exponent 2364, height exponent 577/32 and c/4 consumer are justified by round 8. |
| [proofs/diagonal_scaling.tex](proofs/diagonal_scaling.tex) | Prior twelve-coordinate ternary diagonal map and exponent-span argument. Its 905-digit392-variable table and integer-only row divisors are historical; round 8 adds two dyadic factors and uses rational row divisors. |
| [proofs/optional_anchor_height_round7.tex](proofs/optional_anchor_height_round7.tex) | Optional odd-exponent anchor/projective-height research; neither improvement is needed by the selected 389 construction. |
| [proofs/detector_round8.tex](proofs/detector_round8.tex) | Current primary U_A order 12 promotion, uniform (12,12) pair and q12-squared reuse, with domains, common-place soundness, all completeness estimates and measured 389-count circuit. Its isolated count example keeps anchor 2790 only to measure the detector change separately. |
| [proofs/arithmetic_round8.tex](proofs/arithmetic_round8.tex) | Current Euler-product/genus reapplication yielding height exponent 577/32 and 665-bit constant; even anchor 2364 with depth 1181; actual c/4, order 45 and order 12 consumers and completeness. |
| [proofs/diagonal_scaling_round8.tex](proofs/diagonal_scaling_round8.tex) | Current input-fixed two-prime diagonal map on13 coordinates, exact rational primitive row normalization, complete357-row SOS and 757-digit coefficient maximum. |

## Explicitly unselected paths

- Old labels2X^2+3 or1224X^2+2451, corrections21/105/Boolean selectors and four/five-factor scalar products.
- Six rational difference guards and earlier finite-only primary charts; current complete charts include the stated identity and tangent branches.
- Exact scalar ratio circuits; the retained real proxy has its own nonzero-domain and split41 proof.
- Old G9/G10 circuits, alternate-depth>=2 experiments, high orders 40/42/43/44/46/48/51/52 and scalar orders 24/27/31/32/56. The exploratory high44 numerical margin at 2364 is not a selected circuit or proof dependency.
- Anchor exponents 2^26,2^19,2^16,2^13,4096,3072 and 2790, including their literal old constant chains. The uniform even-exponent proof is reused at 2364, with depth 1181.
- Old exponent 19 height coefficient and the previous scalar c/80 numerical target; selected alpha=577/32,665-bit H and c/4 are independently checked at the actual consumers.
- The previous mixed(1,12) pair and its q1*q12 coordinate; selected tests are paired uniformly at(12,12) and reuse q12^2.
- General inverse-weight-family, optional projective-height and odd-exponent-anchor research; none is needed by selected 389.
- Old delta^-3 weight chains and the unvetted stronger delta^2*D normalization. The selected weights remain delta^-1 and R is unchanged.
- The prior 392-variable905-digit ternary-only table and 12-coordinate-only diagonal certificate; the current map changes 13 coordinates and requires rational row divisors.
- Any six-node, total-variable-count, anchor-exponent or coefficient-optimality claim.

## Verification and manuscript handoff

384 detector source assertions,7 Laurent identities,3 normalization identities and 2 uniform-pair component identities; a separate157-assertion detector-promotion review; unchanged69 scalar assertions with 7 chart/proxy identities and 10 valuation bounds;339 gate identities and 330 compiler operations. Arithmetic has97 source/numerical assertions plus a separately written67-assertion exact certificate. The two-prime audit must verify all 357 rational row divisors and compare every one of 26,295 coefficients in the complete JSON and decimal SOS tables.

Finite checks and independent agent reviews do not prove the inherited group, quaternion, global geometric/modularity/height, restricted-converse/pole-realization, simultaneous-prime or Lucas inputs. No whole-proof Lean certification or independent human peer review is asserted.

- Verify the pinned source and selected builder hashes before edits; confirm the current proof hashes in this catalog.
- Read each cited argument and check its domain at the current consumer. A receipt hash is a binding, not the mathematical argument.
- Preserve identity/tangent branches, the scalar f(Q)_0 guard, full conjugation, first-four formal premises, decoded square scales and completeness choice order.
- Use the full selected test order list, including U_A order 12; scalar order 28; S0=3^2364; depth 1181; alpha=577/32; the 665-bit H; and the actual c/4 consumer. Do not reuse old numeric examples as current hypotheses.
- Decode13 changed coordinates before interpreting the balanced table, and verify every signed rational row divisor including the five nonintegral cases.
- Run the current exact source/gate/arithmetic/table/diagonal checkers and repository audit-history checker after any relevant changes.
- Keep manuscript integration pending until each connecting argument or exact reference is present at its consuming passage and reviewed. Do not refresh historical audit hashes merely to silence failures.

**Historical disposition:** this is an inventory of supplied derivations and current applications, without a priority or new-gap claim. **Manuscript disposition:** incorporation of the 389-source composition remains pending. Finite checks alone do not change that status.

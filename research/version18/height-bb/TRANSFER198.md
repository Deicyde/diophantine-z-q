# Busy Beaver transfer to the frozen Conant198 family

Date: 2026-11-15. Author/reviewer: height lane of the Version18 integration team.

Disposition: the historical repaired BB argument extends to Conant198 with the same two BB arguments, 2^1000 and 2^2000. This note supplies the new transfer proof and an executable notation for its changed enumeration. It is a newly authored transfer, not a claim that the old 222/213 acceptance already covered 198. The retained arithmetic premises and exact 198 reconstruction remain separate inputs. Root must independently review this transfer and bind the final manuscript assembly.

## Frozen sources and historical status

- C198: work/v18-198-dependency-inventory-20261114/C198.tex, SHA-256 3f8a91ccffc6c7138c166532fd2732f89448284f42d011d41b287260d4e1c5de. Its theorem is lines 34–53; scalar estimates 183–233; aggregate and soundness 235–303; completeness 305–379; balanced comparison 382–404.
- JWT: the same inventory's JWT.tex, SHA-256 75ff9bc3bf6ebee4ae200568a1537b3e24fede021aa0262368f7babc494018fe. Lines 96–141 give no constant abelian translate for nonzero signed indices and arbitrary torsion translates; lines 143–198 freeze zero-index coordinates and verify the projective-family hypotheses.
- Later historical proof: work/quartic213-release-20261113/bb-author/bb-specialization213.tex, SHA-256 7a31b81d82ae654b18f40736016ab59edb5d5467d26735bd52f00f119ae0176a. Geometry/records are lines 28–316; quantitative threshold 318–386; corrected real preparation 388–469; compiler 482–694; strict coefficient wrapper 696–750.
- Reused compiler: bb-machine-review/compilation-replacement.tex, SHA-256 a2b65ec02e3fd2461c0e7311b465980d8cf8dbb2ecb3dab2c813a23aa4231d9b. Its independent review is bb-machine-independent-review/REVIEW.md. Reused strict coefficient lemma: coefficient-proof-replacement.tex, SHA-256 b57342bd53aa9fe9ebb852925ddd4a5a8d8c6e47e9f7e2dbcf0bffd3ff942090.
- Historical independent arithmetic/geometry reviews are bb-independent-review/REVIEW.md, GEOMETRY-REVIEW.md, HARMONIC-PROOF-SUPPLEMENT.md and ASSEMBLY-REVIEW.md; bb-consumer-review/REVIEW.md joins their final accepted hashes. The geometry supplement resolves the superseded geometry hash mentioned in the earlier review.

The first work/busy-beaver-threshold-20261111 draft was expressly unreviewed. Its fixed neighborhood of 64P did not prove compatibility with arbitrary finite preparation. The later Haar argument repairs that gap. Its old generic compiler/decoder estimates were also replaced by explicit counter and tape constructions. Use these later repairs, not the first draft alone. No prior reviewed argument permits transferring a BB bound merely because a new threshold is ineffective.

The quantitative family input is Von Buhren, JTNB29 (2017), Theorem 3.1, printed p312, with constants (3.2), not merely its qualitative Theorem 1.1. I checked the final published text at https://www.numdam.org/article/JTNB_2017__29_1_307_0.pdf. The graph-height bridge uses the later review's final published Zhang, Positive line bundles on arithmetic varieties, JAMS8 (1995), Theorem 5.2 p208, plus the explicit local intersection/Chow comparison in the reviewed supplement. These are theorem applications, not new unproved arithmetic hypotheses.

## Convention and the two distinct parameterizations

BB(s) is the maximum number of transitions before halting among deterministic machines with exactly s working states, a distinguished initial state, binary symbols 0 and 1, one two-way infinite tape initially all 0, and left/right moves. There is a separate uncounted halting state. Its entering transition, including write and move, counts. Unused working states are allowed. There are finitely many tables and at least one halting table. Padding proves BB is nondecreasing.

Set N_BB=BB(2^1000) and A_BB=149^(2*N_BB+1). These are different integers. The unbalanced 198 table is polynomial in A; its sum of 184 primitive integer squares has

    H(P_N)=max(H0, A_N^2),
    A_N=149^(2N+1),
    K0=31581660^28,
    H0=(5898050446009651968*K0)^2.

The branch A_N^2 dominates at N>=53. The balanced presentation instead uses C=149^N and contains nonzero terms linear in C. It is not an integer-polynomial presentation in A=149*C^2. To retain the user's settled wording, use the unbalanced table in the main BB theorem. Neither A nor N is a quantified coordinate.

## Covering precisely the enlarged point domain

Write R0=(1+sqrt(2),2sqrt(2)), P=2R0. The retained group theorem writes every point of E(K) uniquely as [m]R0+tau, m in Z and tau in E[2](K). The finite torsion possibilities are (0,0),(d,0),(-d,0), besides the identity O. Every finite point is covered by m>=0 and tau in E[2](K), omitting only (m,tau)=(0,O), for the purpose of its abscissa: replacing a negative m by its absolute value preserves x because -tau=tau. Preserve the signed labels separately in estimates.

For a quadruple put S=sum m_i^2 and

    T=7+(1/4)Tr(sum_i x([m_i]R0+tau_i)).

Freeze each zero-index coordinate to its one of three finite torsion points and omit that factor. Each of four coordinates has four stratum choices: active, or one of three fixed torsion values. Thus there are at most 4^4=256 strata. Active torsion translates need not be fixed: they all belong to the same fixed finite-rank group and JWT's no-translate lemma allows them. The all-frozen strata have S=0 and cannot produce a record.

For a stratum with k>=1 active coordinates, use A_k=E0^(2k), with its product plane-cubic/Segre embedding, and the graph of

    F=c+(d/4)sum X_i+(d'/4)sum X'_i,

where c includes 7 and the frozen contributions. Each frozen trace contribution is 0 or +/-3/2; hence 1<=c<=13 and its denominator divides 2, so h(c)<=log26. This is an integral graph over P1. Its dimension is 2k, its source dimension parameters are at most the old 8-factor parameters, and its degree is at most (2k+1)!*3^(2k)<=9!*3^8<2^32. The same complete cubic restriction maps verify the source embedding condition. JWT excludes all positive-dimensional abelian translates through actual active points in the corresponding fiber, including boundary translates meeting the rational-map domain.

The unchanged addition and duplication calculations give h_add,C_haut<100. The dense torsion graph-height argument survives the added constant: the old active trace height bound below 40 increases by at most h(c)+log2<4, giving below 44. The plane-factor sum is below 80 and the Euclidean adjustment below 5. Use essential minimum 200 in place of 125. The same reviewed intersection/Chow calculation then gives h(V)<2^100, since its comparison error is still below 2^60. This is a new check of the constant term, not an identification of h(T) with h(T-7).

The paired product canonical height equals alpha*S with alpha=6*hhat(R0). The retained quantitative bound hhat(P)>=1/2, used and independently reviewed in the historical BB geometry, gives alpha>=3/4 because P=2R0. Torsion translates do not change canonical height. In the canonical metric, normalized directions are the ordinary vectors (m_i)/sqrt(S), padded by zeros in omitted coordinates. They lie in the four-dimensional direction cube.

## Uniform finite record bound

Use exactly U=2^(2^600). In every stratum the historical upper envelopes Lambda<2^1700, psi<2^568 and log2(e3)<19440+13600*2^568+100 remain valid. In particular mu,e2^2,e3<U/4. The change alpha>=3/4 is therefore harmless in the badness test below. The same direction covering has at most K=8*ceil(4e1+1)^4 records per stratum, with log2(K)<2^584. Consequently 256*K<U. These numerical margins are much larger than the finite stratum multiplier.

Enumerate positive integer codes q_i=4m_i+e_i, where e=0,1,2,3 encodes O,(0,0),(d,0),(-d,0). All q_i>=1 encode finite points. Enumerate quadruples by their maximum code, with finite lexicographic shells. Compute S=sum floor(q_i/4)^2 and the exact rational T above. Let b(T) be the bitlength of max(|numerator(T)|,denominator(T)) in reduced form with positive denominator; h(T)<=b(T)<=2h(T)+1.

Start r=U. A record occurs exactly when S>U*r and S>U*b(T); then set r=S. Each record has canonical height >=(3/4)S>e3 and >mu*h(T). Consecutive records have height ratio >U>e2^2. Any subsequence in one stratum and one direction cell retains this growth, so the quantitative family theorem allows at most eight in that cell. Thus the total record count j_* is finite and j_*<U.

Set r_*=U if there is no record, otherwise the final recorded S. Every bad tuple has S<=U*r_*; any later violation would give another record, and earlier running values are no larger than r_*. All tuples therefore satisfy

    S <= U*b(T)+U*r_* <= 2U*h(T)+U*(r_*+1).

For the actual 198 labels n=m1/2, a=m2, t=m3, b=2*m4+1 (with signed m_i before taking absolute values),

    B=max(1,|n|,|a|,|t|,|b|),
    B^2 <= 9*(S+1) <= 18U*h(T)+10U*(r_*+1).

The last inequality uses U*(r_*+1)>=9. Thus M1=18U and M2=10U*(r_*+1) work uniformly over the full 198 solution domain.

## Converting the record to an all-larger-N threshold

Keep G(r)=U^32*(r+1). Let N>=G(r_*). The actual contact supplier and exceptional prime set are unchanged. The historical crude product bound is B_Sigma<2^1295013, and the same supplier gives H2<2^4000000. Put C=2*M1*H2=36U*H2<U^2. Absorb M1*log2 from h(T)<=h(t0)+h(t1)+log2 into J1=32U*(r_*+1). Then J1<G(r_*)<=N.

The scalar extraction in C198 gives c=|a|>=149^L_N, L_N=floor(9(2N-1)/4)+1>=N, and

    h(beta)<=C3*149^(-L_N)*c*(1+log(c)/3), C3=2^330770.

In particular B>=c>N. If Delta is nonzero, C198's actual cubic divisibility M_j^3|Delta and |Delta|<=14B^4 imply

    B^2 <= C*14^(7/18)*B^(14/9)+J1
         <= C*14^(7/16)*B^(7/4)+J1.

The first term is below B^2/2 because B>U^32 and C*14^(7/16)<4U^2. The second is below B^2/2 because J1<N<B and B>2. Hence Delta=0.

For nonzero input numerator J_X, C198 gives J_X<=4B*exp(h(beta)). Absorbing J1 yields

    log B <= (6/5)log(2C)+(7/5)log4+(7/5)h(beta)
           <= C'+7*C3*149^(-L_N)*c*(1+log(c)/3),
    C'=4log(2C)+7log2<U.

The changed affine-label Lucas argument gives log B>=(c-6)log(c-3), rather than the old (c-5)log(c-2). The same enormous G suffices: c>=exp(12) implies c-6>0.9c and log(c-3)>log(c)-1, whose product exceeds 2c+c*log(c)/3. Also c>C' and 7*C3*149^(-L_N)<1. This contradicts the upper bound. Thus J_X=0 and the retained squarefree denominator argument gives integer input. Every inequality persists for every larger N; no monotonicity of polynomial zero sets is asserted or needed.

## Explicit completeness with the new scalar factor two

Reuse the reviewed Haar preparation on the identity component G^0 of the closure of the paired orbit of P. Each projection of G^0 is onto the corresponding real identity circle. The elliptic-integral tail bound gives a fixed compact neighborhood with both |z(H)|>1/2000, avoiding the finite chart exclusions. For every finite preparation modulus L0, enlarge it by the finite component-group order and 64; multiples are dense in G^0. The scalar point can subsequently be chosen near O with both |z(Q2)|<=1 and with all required finite divisibilities, including the new 3|a0.

The 198 scalar quotient is Z=2z(Q2)/z(H), so each real value is below 4000 and both rational components are below 2^12. Since H is on both real identity components, |F|=|Norm(1/x(H))|<=1/7. The unchanged physical formula therefore gives, for R>=1,

    0<W_s<(2^48+2^24+1)*R^(-4)<2^49*R^(-4),
    0<b_s<2^112*R^(-6).

R>=2^20 suffices for b_s<17. The input-uniform lower bound R>=149^(2N+1)/(1+149^2) and N>=G(r_*) suffice. The extra scalar factor two improves 2-adic depth and is a unit at all odd preparation places; the required finite data can be chosen arbitrarily deeply as in C198. The actual final pole input is realized only after H is fixed. All further labels, prime lists, slopes, progression moduli and pole certificates may depend on (N,input) but impose no further lower bound on N, by the retained constructive completeness argument. The aggregate T>=1 and its possible repeated contacts are handled by that argument's merged finite rational contact list, not by an assumption of twenty distinct contacts.

## The corrected halting selector and state count

record_machine198.py implements precisely the code enumeration above; its SHA-256 is 109b5061f360be5ab98e90e879a2b147a1bb627a7c1e20de62d95718d176af1d. It changes the historical program's generator to R0, includes the four torsion choices, adds the constant 7, and measures S with the decoded indices. It computes G(r) and then performs G(r) increments. It never attempts to recognize the final record. For hardwired j=j_* it halts; j=0 immediately uses r=U.

The finite checker finds 1398 syntax nodes, 15 functions, acyclic call depth 10, and maximum literal 600. All source divisions occurring in the enumeration have nonzero divisors: each encoded point is finite, and the chord/tangent routine handles identity and inverse cases before division. All field values are exact rational triples. The source has no library calls, recursive calls, dynamic calls or input-dependent tuple size.

Use the reviewed explicit counter compiler, with deliberately looser allowances: fewer than 2^12 nodes per function and depth <=12 imply fewer than 2^156 fully inlined nodes; tuple/return flattening costs <2^10 per node, and the explicit signed arithmetic templates fit <2^20 instructions and counters per scalar node. Thus the core uses fewer than 2^186 instructions and counters. Hardwire j_* in at most 2^600 bits by the reviewed X<-2X+bit prefix with two reused scratch counters. The total counts satisfy L<2^605 and R<2^187. The reviewed unary-block/binary-tape simulation uses fewer than

    2^20*(L+1)*(R+1)<2^814<2^900<2^1000

working states. Its final increment loop plus initialization has running time strictly greater than G(r_*). Padding therefore proves

    N_*=G(r_*)<BB(2^1000).

Combining this with the all-larger-N arithmetic proof selects N_BB=BB(2^1000). The unknown final record value is computed by the machine; only its ordinal j_* is hardwired. There is no hidden encoding of an arbitrary ineffective constant.

## Strict coefficient bound

The historical independently reviewed wrapper chooses an existing maximizing 2^1000-state halting table, encodes its 2006*2^1000 bits, simulates it exactly, computes H=149^(4*BB(2^1000)+2)+1, and runs for H+1 increments. Its explicit compilation uses fewer than 2^1200<2^2000 working states. Thus

    149^(4*BB(2^1000)+2)+1 < BB(2^2000).

This is an existence construction; it neither finds the maximizing table nor evaluates BB. A padded 54-state chain gives N_BB>=54>53 independently of the arithmetic threshold. The frozen unbalanced198 coefficient formula and the exact H0<149^214 check yield

    H(P_BB)=A_BB^2=149^(4*BB(2^1000)+2)
             <149^(4*BB(2^1000)+2)+1<BB(2^2000).

In particular do not copy the old exact coefficient equality A^2+1: the 198 maximum is A^2. The old +1 remains useful solely as a strict wrapper majorant.

## Verification boundary and required integration checks

FINITE-CHECKS.json checks the new syntax/domain examples, R0 doubling, 128 finite encoded points and their doubles, exact shifted traces, the zero-record branch, the state-exponent arithmetic and H0 crossover. It does not run U, BB or the production search. The mathematical argument above supplies the unbounded proof.

Still required outside this lane: independent review of this newly authored transfer; exact final manuscript import/parameter/row binding; confirmation by the reconstruction lane of the selected unbalanced198 table, its 2945 support count, and its coefficient profile after specialization. The foundational arithmetic remains relative to the manuscript's stated premises. No whole-foundation acceptance, minimum-variable theorem, decimal expansion, or effective procedure for choosing the threshold is claimed here.

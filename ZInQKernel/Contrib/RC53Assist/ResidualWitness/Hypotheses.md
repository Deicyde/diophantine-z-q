# Residual-model hypothesis inventory

The targets are `Mattuck.residualRankCounts_genuine` and
`GenuineInst.residualRankCounts_actual`. Both are constructors of
`ResidualRankCounts`, not assertions that their input data exist.

## Standing arithmetic and local data

1. **Field and integral models.** A number field K and, at every finite place w,
   an integral Weierstrass equation E_w whose generic fiber over K_w is elliptic.
2. **Quadratic radicand hα.** An integer k and an algebraic integer α with
   [K:Q] = 2, α² = k, and Q[α] = K.
3. **hK, w, hw.** K is totally complex; w is a complex infinite place.
4. **hN and hA.** N is a nonzero natural number and the number of distinct
   prime divisors of |k| is at most A. The constructors do not require N to
   equal the conductor of the actual curve.
5. **hr, hD, hDodd.** r is prime; D is a finite set of odd primes. The charged
   rational primes are the prime divisors of 2N, together with r and D.
6. **cond and hcondD.** A condition is assigned to every ideal of the integers
   of K. A relaxed derivative condition may be assigned only above a prime of D.
7. **hfull.** At each old-Kummer place the local curve has exactly four rational
   points killed by 2.
8. **Support agreement.** The intended smaller support is S₀, the places above
   the charged rational primes. The target types do not force the local-count
   support Sloc, the support S used in the support comparison, and S₀ to agree.
   A genuine instance should specify their agreement rather than exploit this freedom.

## Residual model and its identifications

9. **Dsel and finite terms.** Dsel is a diagram G → L ← U of complexes of F₂-vector
   spaces. Every term of each of G, U and L is finite-dimensional. Its Selmer cone
   has term Cⁿ = Gⁿ ⊕ Uⁿ ⊕ Lⁿ⁻¹ and differential
   d(a,u,x) = (da,du,res(a) − ι(u) − dx).
10. **s and hs.** s is a finite set of integer degrees contained in {0,1,2}.
    Neither target states that s contains every nonzero degree. An empty s would
    make all three rank hypotheses empty; that is not a nonzero witness.
11. **eG.** For each n in s, Gⁿ is F₂-linearly isomorphic to genuine continuous
    Hⁿ(G_{K,S₀}, F₂²), with the trivial action on F₂².
12. **hUm.** The sum over n in s of dim Uⁿ is at most the sum of the dimensions
    of the specified genuine local conditions over all places above the charged
    primes. The old-Kummer dimension is the one obtained from E_w by Mattuck.
13. **hLm.** The sum over n in s of dim Lⁿ⁻¹ is at most the sum of genuine local
    cohomology dimensions in degrees 0,1,2 at the same charged places.
14. **Bounds a,b.** The residual cone is zero outside the integer interval [a,b].
15. **pP.** An actual cochain map from this bounded residual cone to the genuine
    smaller-support Selmer complex, inducing isomorphisms on homology in every
    integer degree. Separate dimension witnesses for eG, hUm and hLm do not
    provide this map.

## Support comparison and minimal model

16. **hSS', hS', hset.** S is contained in the finite support S'. The coefficient
    prime pr is prime, S is finite and contains all places above pr; if pr = 2,
    K is totally complex. The coefficient ring F₂ is finite, pr is nilpotent in
    it, and it is self-injective. Consequently pr must equal 2 here.
17. **M and its instances.** M is a finite discrete F₂-vector space with a jointly
    continuous F₂-linear action of G_{K,S}.
18. **ψ and hψ.** At each new place q in S' minus S, localization G_{K_q} → G_{K,S}
    factors through the genuine unramified quotient G_{K_q}/I_q, by the supplied
    continuous group homomorphism ψ_q.
19. **Δ.** Genuine old local conditions, i.e. complexes U_v with actual cochain
    maps U_v → C_cont(G_{K_v},M).
20. **Dfull, f, hDp.** The larger-support diagram with unramified conditions is
    obtained from Dfull by restricting its condition complex along f.
21. **g, hfg, hinj, hsurj, hex.** In every degree the sequence
    0 → U_unramified → U_full → W → 0 is exact, with maps f and g.
22. **hW.** The quotient complex W is acyclic in every degree. The manuscript
    obtains such acyclicity after the limit and inversion of t; it is not an
    automatic property of ordinary full/unramified local conditions over F₂.
23. **L, hLmin, pL.** L is a finite-dimensional complex, zero outside [a,b], with
    differentials landing in the maximal ideal times the target term. Over F₂
    this means its differential is zero. An actual map pL from L to the genuine
    larger-support Selmer cone induces homology isomorphisms in every degree.

## Extra hypotheses of the actual-coefficient constructor

24. **E, j, χ₀.** E is an actual Weierstrass curve over K, j is a natural number,
    and χ₀ is a character of G_{K,S₀} valued in A_{j+1} units, where
    A_i = (Z/2^i)[t]/(t^i). Its residual module is F₂ tensor over A_{j+1} of the
    actual coefficient module M_{j+1}.
25. **hT₀, hM₀, h2₀, htriv₀.** E(K_{S₀}) has respectively (2^{j+1})², (2^j)²,
    and four points killed by the indicated orders, and every Galois element
    fixes every point killed by 2.
26. **eGact.** In item 11 replace F₂² by the actual residual coefficient module.
    The supplied coefficient comparison transports this to eG.
27. **χ and the support coefficient module.** The module in item 17 is the actual
    residual module over S, with its genuine residual action. Continuity and
    finiteness are explicit hypotheses over S.

## Printed inputs, unchanged

- Milne, *Arithmetic Duality Theorems*, second edition (2006), Chapter I,
  Theorem 4.10(c), pages 56–57: global vanishing above degree two over a totally
  complex field, with primes above 2 in the support.
- The same source, Chapter I, Theorem 5.1, page 67: finiteness and the global
  Euler characteristic.
- The same source, Chapter I, Theorem 2.8, page 31: the local Euler characteristic.
- The same source, Chapter I, Corollary 2.3, page 28: local duality, in the
  trivial-coefficient form.
- Nekovář, *Selmer complexes*, Astérisque 310 (2006), Proposition 7.8.8(ii),
  pages 186–187: genuine support comparison.

These are already explicit proposition arguments of the targets. No proof of
these published global propositions is supplied merely by choosing a curve.
The Milne proposition definitions mark their source verification as unverified.

## Scope of the small case

The least positive admissible curve parameter is 11. The compiled instance uses
K = Q(i), k = −1, A = 0, N = 66, r = 5, D empty, and j = 0. All three supports
S₀, Sloc and S agree with the finite places above {2,3,5,11}; S' = S. The actual
coefficient character is trivial. Its residual module has four elements and
F₂-dimension two, with the genuine trivial Galois action.

Only rational 2-torsion and trivial 1-torsion are needed at j = 0; the higher-torsion
ramification infrastructure is unnecessary. The same actual integral equation
is used at every local place, its generic fiber is the base change of E₁₁,
and exactly four rational points are killed by 2 at every finite place.

The full condition at every charged place is a genuine row of the local-condition
table. Its local identity cone is contractible. Thus the genuine full-condition
Selmer complex computes actual global cohomology. The residual model retains this
cohomology in degrees 0,1,2, has zero differential and zero remaining local pieces
after cancellation, and is connected to the genuine Selmer complex by an actual
quasi-isomorphism. Its total rank is at least six: H⁰ has dimension two and the
printed Euler characteristic forces H¹ to have dimension at least four.
Both target constructors apply to this same instance and give rank at most 238.

This proves conditional non-vacuity of the target interfaces, not the manuscript's
particular final-companion or old-Kummer/active-support instance. In particular:

- Q(i) is expressly excluded from the manuscript's final companion choices.
  It satisfies the target types, which require only a totally complex quadratic field.
- N = 66 is a support parameter. No equality between 66 and the conductor of E₁₁
  is asserted or proved.
- The test uses full old conditions, not old-Kummer conditions. The local torsion
  prerequisite for old Kummer is proved, but the old-Kummer Selmer model and its
  comparison maps pP and pL are not constructed here.
- There are no new active places. Thus the support-factorization condition is
  empty and the singular quotient is genuinely zero. A nonempty active-support
  instance still needs the factorizations and the acyclicity hW after the stated
  limit and inversion of t. A plain F₂ full/unramified comparison does not provide
  that acyclicity merely because the residual representation is trivial.
- The existing printed propositions remain explicit arguments. The locators
  above are the ones supplied by the RC53 interfaces and their cited counting
  statements; this contribution does not independently verify the scans.

Mathematical locators: manuscript `ex:limits-residual-bound`, lines 4453–4648;
curve and rational 2-torsion, lines 1761–1767; actual coefficients, lines 2724–2727;
residual coefficient comparison, lines 4479–4480 and 4521–4531; final companion,
lines 2595–2614.

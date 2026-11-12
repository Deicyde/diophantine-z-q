# rv-a6-route results log

## Computations (scratch/rv-a6-route/quat_check.py, ~/pyenv/bin/python, PARI) — VERIFIED
- hilbert(2,-3,p): p=2: -1, p=3: -1, p=oo: +1. So B=(2,-3) is ramified exactly at {2,3}; B⊗Q_3 division.
- Lambda=Z<i,j> (i^2=2, j^2=-3, ij=-ji): det of trace form on 1,i,j,ij = -576 = -24^2: reduced disc 24, 3-part 3 => Lambda⊗Z_3 maximal.
- manuscript L411: B=(2,-3), O=Z[i,(1+j)/2] ⊇ Lambda (VERIFIED by reading).
- k=1: every c in Lambda/9 with c^2=0 lies in 3Lambda (exhaustive, 3^8 elements). k=2: every c in 3Lambda/81 with c^2=0 lies in 9Lambda (exhaustive over 3^12).
- Lambda/Pi^a (Pi=j) as groups: a=1:(3,3), 2:(3,3,3,3), 3:(9,9,3,3), 4:(9,9,9,9), 5:(27,27,9,9).
  => FINDING F1: pkg-I2 §4.2 step 2 "cardinality 3^{4n} with exponent 3^n forces A[3^n] ≅ Lambda/3^n" is FALSE as stated
     (Lambda/Pi^{2n-1} ⊕ Lambda/Pi has order 3^{4n}, exponent 3^n). Repair: use the full group structure (Z/3^n)^4 (I2-Tors gives it): for n ≥ 2 it forces freeness; for n=1, F_9^2 = Lambda/Pi ⊕ Lambda/Pi is group-isomorphic to (Z/3)^4, so freeness at n=1 is NOT forced by counting (the route only needs n=2k ≥ 2).
- Split contrast: in M2(Z/9), [[0,1],[0,0]] squares to 0 and is not divisible by 3: the division property at 3 is essential.

## Lean (scratch/rv-a6-route/A6.lean) — VERIFIED: compiles with `lake env lean`, no sorry
- Copy of scratch/pkg-I2/I2.lean lines 1-443 (namespace renamed RvA6) + §10.
- New glue statement `QuatUnipotentTrivial` (pure algebra over a CommGroup; NOT proved, enters as a hypothesis).
- `RvA6.goodReduction_of_QM_rational3` (same statement as PkgI2's, plus hypothesis hAlg : QuatUnipotentTrivial):
  PROVED from NeronOggShafarevich, RaynaudCriterion, TorsionStructure, QuatUnipotentTrivial.
  `#print axioms`: [propext, Classical.choice, Quot.sound].
- Helper defs `galHomPts`, `endPts` (Galois action / endomorphism as MonoidHom on points; uses MonObj.one_comp, MonObj.mul_comp).

## Findings
- F1 (wording, repaired): see computation above; freeness of A[3^n] needs the group structure (Z/3^n)^4 and n ≥ 2.
- F2 (wording, repaired): pkg-I2's "nrd = x²-2y²+3z²-6w² is anisotropic mod 3" is false for the quaternary form ((0,0,1,0) is a zero mod 3);
  the correct input is that v_Π is a valuation on Λ⊗Z_3 (B⊗Q_3 division; nrd anisotropic over Q_3), or the finite check c²≡0 mod 9 ⇒ c∈3Λ (VERIFIED above).
- Route verdict: SOUND AFTER REPAIRS (F1, F2 wording; the algebra lemma is glue with a complete proof in the report).

## Lean (scratch/rv-a6-route/QuatVal.lean) — VERIFIED: compiles, no sorry; axioms [propext, Classical.choice, Quot.sound]
- `RvA6.quat_base`: 9 | every coordinate of x² (x = a+bi+cj+d·ij in Z<i,j>) ⇒ 3 | a,b,c,d.
- `RvA6.quat_sq_dvd k`: 3^{2k} | every coordinate of x² ⇒ 3^k | a,b,c,d (all k). This is §3 step 4 of the report
  (the valuation step, repair R2) for all k, in coordinates x² = (a²+2b²-3c²+6d²) + 2a(bi+cj+d·ij).
- Remaining unproved glue: steps 1-3, 5 of QuatUnipotentTrivial (T free of rank one over Λ/3^{2k}; N = right mult by c).

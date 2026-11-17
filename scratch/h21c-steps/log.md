# h21c-steps results log

Task: lower the GLUE of frozenTarget's `h21C : ZInQ.Contrib.TYZGenusFold.TYZThm21PairsC`
(ZInQKernel/Contrib/OneProof/TYZThm11Genus.lean:44). Base e1b31749.

## Sources read (VERIFIED, ~/tyz-src/Period7.tex)
- L536-550: pi = JL transfer of f_E (E: y^2=x^3-x); pi_Z = integral-valued elements of pi; U_n = R_n^ x K_{n,2}^x;
  "pi_Z^{U_n} free of rank 1"; f_n a Z-generator. L551-559: P(d1,d2), Theorem 2.1.
- L602-606: U = prod U_p, U_p = O_{B,p}^x (p odd), U_2 = Z_2^x(1+4 O_{B,2}).
- L612-638: Theorem 2.4(1): pi^U 6-dim with orthogonal basis f_delta, delta in {(+-i+-j)/2, (+-j+-k)/2, (+-k+-i)/2}/{+-1},
  f_delta determined by restriction to 1+2O_{B,2}, f_delta(1+2x) = (-1)^{tr(delta x)}.
- L643-661: Lemma 2.5 (8 classes x -> 1+2x; uniform measure). L665-705 its proof ("straightforward to check").
- L715-760: pi in A_0; A_0^U -> functions on O_B,2/(Z_2+2O_B,2) perpendicular to 1 and (-1)^tr; A_0^U = sum C f_delta.

## Plan
- U4 := (1 + 4 O_B^)^x (units w with (w-1)/4, (w^-1 - 1)/4 in O_B^). Q^^x U = Q^^x U4 since U_2 = Z_2^x (1+4O_{B,2})
  and Z_2^x (at 2, 1 elsewhere) is in Q^^x.
- Surjectivity: copy of HfxProof.exists_twoRep_of_unit (its unit w is in U4).
- Injectivity: HfxProof.two_adic_b1 with omega = 0 + a decide check mod 4.
- f_delta: psi_delta(t) = (-1)^{tr(delta x_t)} on the 8 reps, extended by invariance.
- Dictionary: InPiZ <-> span{f_delta} and U_n-invariant (Fourier on F_2^3, character orthogonality by decide).

## Results (compiled)
- ZInQKernel/Contrib/OneProof/TYZThm21Span/FDelta.lean (namespace ZInQ.Contrib.H21CSteps): COMPILES (lake build, no errors).
  - `exists_twoRepU`: every unit of B^ lies in B^x (1+2x_t) GU, GU = <U4, Q^^x> (surjectivity). VERIFIED (compiled).
  - `twoRep_mem_DCU_iff`: twoRep v t in DCU (twoRep v t') <-> t = t' (injectivity), via two_adic_b1 (omega = 0) and
    `mod4_sep` (decide +kernel: 64 pairs x 24 units x 16 (X,Y)). VERIFIED (compiled).
  - `GU_le_HgrpN`: GU <= <U_n, Q^^x>. `GU_le_SgC`. VERIFIED.
  - `deltaQ`, `xRepQ`, `trdQ`, `psiDelta δ t = (-1)^{floor tr(δ x_t)}`; `psiDelta_eq_tab` (48 cases, norm_num):
    exponents a+b+c, a+b, b+c, b, a+c, a for δ = (i+j)/2, (i-j)/2, (j+k)/2, (j-k)/2, (k+i)/2, (k-i)/2. VERIFIED.
    Consistency with Thm 2.4(3) (chi0 f_{(i+j)/2} = f_{(i-j)/2} etc.): by hand from the table, chi0 = (-1)^c. VERIFIED (hand).
  - `psi_orth`, `psi_sum`, `psi_sum_chi0` (decide +kernel). VERIFIED.
  - `fDelta`, `fDelta_eq_of_mem` (B^x-left, Q^^x U-right invariant), `fDelta_twoRep`. VERIFIED.
- ZInQKernel/Contrib/OneProof/TYZThm21Span.lean: COMPILES.
  - `InPiSpan`, `IsTestVectorSpan`, `TYZThm21Span` (new leaf), `fourier8`, `inPiZ_iff_inPiSpan`,
    `isTestVector_iff_span`, `exists_testVectorSpan` (non-vacuity), `tyzThm21PairsC_of_span`, `tyzThm21Span_of_pairsC`.
- Split into two separate Lean Props (Thm 2.1 / Thm 2.4(1)): BLOCKED — pi (JL transfer of f_E) has no Lean definition;
  Thm 2.4(1) enters only as pi^U = span f_delta, substituted into Thm 2.1. Result: one leaf replacing h21C.
- FoldCheck.lean: COMPILES; frozenTarget_h21S, frozenTarget_h21S' standard axioms only. VERIFIED.
- Discharges.lean: `DISCHARGES [h21C] by ZInQ.Contrib.H21CSteps.tyzThm21PairsC_of_span, still assumes
  [TYZThm21Span], axioms standard`. VERIFIED.

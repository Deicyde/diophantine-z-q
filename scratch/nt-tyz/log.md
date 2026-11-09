# nt-tyz log

## Step 1 (sources)
- arXiv:1411.4728 has exactly one version, v1 (18 Nov 2014, 42 KB; abs page "Submission history").
  TeX source Period7.tex (3357 lines) downloaded (kept outside the repo; sha256 of e-print recorded in note).
- Numbering (shared counter per section, \newtheorem{thm}{Theorem}[section]): §1: Thm 1.1 (lg), Thm 1.2 (lg'),
  Remark 1.3, Cor 1.4. §3: Prop 3.1 choice, Prop 3.2 CM point1, Thm 3.3 GZ, Prop 3.4 congruence, Thm 3.5 m3,
  Thm 3.6 CM point2, Lem 3.7, Prop 3.8, Cor 3.9, Lem 3.10, Prop 3.11, Cor 3.12, Prop 3.13, Lem 3.14,
  Lem 3.15 multiples1, Lem 3.16 torsion1, Lem 3.17 torsion3, Lem 3.18 torsion2, Lem 3.19 multiples2,
  Lem 3.20, Lem 3.21 betaaction.
- Statements of Thm 1.2 and Thm 3.5(2) as quoted in tyz-5b §1.1: VERIFIED identical to v1 source
  (lines 389-415, 1353-1374). Both end "all decompositions non-ordered with all d_i>1" (Thm 1.2 only;
  Thm 3.5(2) does not repeat the sentence!). Prop 3.4 statement has no "d_i>1" clause, and its proof
  (line 2024ff) uses d_1''=1 ("contribution by d_0=d_0''=n, d_1=1 is the single term Z(n)").
- Proof of Thm 3.5(2), n≡5 (lines 2489-2600): read, each step checked (see note §2).

## Key finding (step 1)
- The (7,3) bracket needs only: Thm 3.5 first assertion, recursion definition of P(n) (line 1320ff),
  ε classification of Thm 3.3, Lemma 3.21(1),(4), Lemma 3.18, integrality of L(m) and Thm 1.1 for m≡3 (8)
  (unambiguous: unique class-3 factor). Prop 3.4's coefficient of Z(e) can be proved as
  c_n(e) ≡ η(e,n/e) L(n/e) mod 2Z[i] by a swap involution (a,b)->(b,a) on ordered splittings, with no
  expansion of L. Then for e≡7 the coefficient is real, and c_2 = Σ_{e≡7} g(e)L(n/e) = T_5b.

## Step 2 (other sources, test of the readings)
- arXiv API: TYZ has only v1. Citing papers fetched (TeX): Burungale-Tian 2104.06732v2 (cites TYZ only for
  ">50% of n≡5,6,7 congruent (cf. TYZ, Sm1)", pages 721-773), Dalawat 2201.11071v2 (TYZ only in a commented-out
  passage; mentions an expository "tianiccm" not on arXiv: UNCHECKED), Feng-Liu-Pan-Tian 2405.11132 (method only),
  Zhang 2111.11618 (Thm 1.1/Cor 1.3 for s_2(n)=0), Guo-Ye-Yin 2505.13133 (general), Sun 2610.31631 (method §§3.1,3.3).
  None restates Thm 1.2 except Smith.
- Smith 1603.08479 v1 and v2 (28/29 Mar 2016; differ only in abstract and acknowledgement wording):
  Theorem 2.1 (cnc.tex label thm:TYZ, "[Theorem 1.1, 1.2]{Tian14}") states row 5(b) separately:
  "if n is 5,6,7 mod 8 and row x agrees with n mod 8, analytic rank exactly one if L_x(n) nonzero";
  L_5b = Σ_{d0≡7,d1≡3} g(d0)g(d1)L(n/d0d1). Unrefereed (no journal ref on the abs page).
- literal_reading.py: for all squarefree n≡5 (8), n<~52000, ≤7 primes, with ellanalyticrank 3 (32 curves):
  reading A (d1=1 admitted) second sum even on all 32 (consistent with the theorem), T5a=T5b=0 on all 32.
  Readings B (d1>1 unordered) and C (d1>1 distinguished) give an odd second sum for n=26565=3·5·7·11·23 and
  n=33117=3·7·19·83 (g(n)=1). certify_counterexamples.py: ellrank 3..3, 3 points, height det 39.4 / 269.7;
  g certified by bnfcertify and equal to Redei's formula on all divisors. kummer_independence.py: Kummer images
  of torsion + 3 points have F2-rank 5 (exact), so rank ≥ 3, so by GZK ord_{s=1} ≠ 1, root number -1 gives ord ≥ 3,
  L(n)=0. => Under readings B, C Theorem 1.2 is FALSE (VERIFIED); only reading A is a true statement.

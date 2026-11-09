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

### deligneComponentsY3PrintedAb

* Bundle field `HDec.HSyn.OpenAddedLeaves17.deligneComponentsY3PrintedAb`; kind **published**, strict **GLUE**; flag: pending reading: depends (medium), whether one display states that the PEL moduli scheme with its uniformization is the canonical model at B = (2,-3|Q), level K3 (Deligne 389 section 5, Milne 2005 section 14).
* Source: Deligne, Sem. Bourbaki 389 (1971) Thm 2.4 and 3; PSPM 33 (1979) 2.1.3, 2.6.3; Milne 2005 Thms 5.17, 13.6 (UNVERIFIED): pi0(Y x_Q Qbar) = Q_{>0}^x \ A_f^x / nrd(K3) with sigma acting by the cyclotomic idele to a fixed sign, for G = B^x, B = (2,-3|Q), at level K3, on one fine witness Y3 (with the R1fp clause list and Lemma QP, as for r1r2); over Mathlib's FiniteAdeleRing, QuaternionAlgebra, cyclotomicCharacter, ConnectedComponents
* packet [R4](#packet-r4); label bigger (a bigger investment); tier T4 (model triage, unreviewed); discussion: [elliotglazer #79](https://github.com/elliotglazer/diophantine-z-q/issues/79).
* Human readings recorded: none.
* Status: open.

```lean
ShimuraGlue.DeligneComponentsY3PrintedAb
```

> shimura-glue, printed form, on abelian schemes (route-a-fold): Deligne's theorem on the connected
> components of a Shimura variety for `G = B^×` at level `K₃` on one fine witness `Y₃` (Deligne, Sém. Bourbaki
> 389 (1971) Thm 2.4, §3; PSPM 33 (1979) 2.1.3, 2.6.3; locators UNVERIFIED).

### shimuraIntegralModelRep

* Bundle field `HDec.HSyn.OpenAddedLeaves17.shimuraIntegralModelRep`; kind **consequence**, strict **GLUE**; flag: pending reading: Kottwitz 1992 section 5 is the PEL functor; the polarization-free integral form needs a relative Lemma P over every locally noetherian base and the rational-to-integral level comparison; Buzzard and Morita may require level prime to D (level 3 at 3 | 6); locators UNVERIFIED.
* Source: Kottwitz, J. AMS 5 (1992) section 5; Buzzard, Duke Math. J. 87 (1997) sections 1-4; Morita, Hokkaido Math. J. 10 (1981); Carayol, Compositio 59 (1986) secondary (locators UNVERIFIED); Lan 2013, Thms 1.4.1.11 and 5.3.3.1 (second locators)
* discussion: [elliotglazer #79](https://github.com/elliotglazer/diophantine-z-q/issues/79).
* Human readings recorded: none.
* Status: open.

```lean
SGRSplit.ShimuraIntegralModelRep
```

> Representability over Z_(p), p > 324, of the moduli problem of QM abelian surfaces (disc 6) with full level 3, by a proper smooth curve (printed form on QMAbScheme): Kottwitz, J. AMS 5 (1992) 5; Buzzard, Duke 87 (1997) 1-4; Morita, Hokkaido 10 (1981); locators UNVERIFIED

### shimuraMainThmIDeligneY3AbU

* Bundle field `HDec.HSyn.OpenResearchLeaves21.shimuraMainThmIDeligneY3AbU`; kind **composite**, strict **GLUE**.
* Source: Shimura, Ann. of Math. 85 (1967) Main Theorem I (reciprocity at CM points); Deligne, Sem. Bourbaki 389 (1971) sections 3-4 (adelic form, PEL moduli interpretation, canonical model); Milne, Introduction to Shimura varieties sections 12-14; fine moduli of QM abelian surfaces with level 3 (R1fpPropsAb, as for r1r2Ab); locators UNVERIFIED
* discussion: [elliotglazer #86](https://github.com/elliotglazer/diophantine-z-q/issues/86).
* Human readings recorded: none.
* Status: open.

```lean
RayClassCFT.ShimuraMainThmIDeligneY3AbU
```

> gt-rayclass (shimura-cft, rayclass-cft), composite of printed theorems: Shimura's Main Theorem I for the level-3 group K3 of B = (2,-3|Q) in Deligne's adelic form on the fine moduli scheme Y3 of QM abelian surfaces (R1fpPropsAb): the uniformization B^x_+ \ (H x (B (x) A_f)^x) / K3 = Y3(C), holomorphy in tau, the moduli clause at every u in O-hat^x (the object at Psi(tau,u) is C^2/iota(O)(tau,1)^T) and Shimura's reciprocity law at CM points. Replaces rayClassCMAb and shimuraFamilyAb.

### deligneComponentsX6PrintedAb

* Bundle field `HDec.HSyn.OpenAddedLeaves17.deligneComponentsX6PrintedAb`; kind **published**, strict **LEAF**; flag: locator UNVERIFIED (see the source).
* Source: Deligne, Sem. Bourbaki 389 (1971) Thm 2.4 and section 3; PSPM 33 (1979) 2.1.3, 2.6.3, at level O-hat^x on X6 (locators UNVERIFIED)
* packet [R4](#packet-r4); discussion: [elliotglazer #86](https://github.com/elliotglazer/diophantine-z-q/issues/86).
* Human readings recorded: none.
* Status: open.

```lean
ShimuraGlue.DeligneComponentsX6PrintedAb
```

> x6-glue (shimura-glue), printed form (on abelian schemes): Deligne's theorem on the connected components of a
> Shimura variety (Sém. Bourbaki 389 (1971) Thm 2.4, §3; PSPM 33 (1979) 2.6.3; locators UNVERIFIED) for
> `G = B^×` at level `𝒪̂^×` on one canonical coarse witness `X₆` (the double coset is computed in Lean).

### babaGranathRationalAb

* Bundle field `HDec.HSyn.OpenResearchLeaves21.babaGranathRationalAb`; kind **published**, strict **LEAF**; flag: one table reading (CM assignment, section 3.1) UNVERIFIED.
* Source: Baba-Granath 2008, rationality of the genus-2 curves with QM by the order of discriminant 6 (locator UNVERIFIED)
* packet [R4](#packet-r4); discussion: [elliotglazer #86](https://github.com/elliotglazer/diophantine-z-q/issues/86).
* Human readings recorded: none.
* Status: open.

```lean
HDec.QMSplit.Moduli.BabaGranathRationalAb
```

> x6-glue, printed form (on abelian schemes): Baba–Granath, Canad. J. Math. 60 (2008), Thm 2.1 and Lemma 3.1
> (read by the locator audit), on one canonical coarse witness `X₆`: a coordinate `π : X₆ → P¹` whose fibres are the
> `Aut(𝒪)`-twist classes, with three distinct rational values at the CM points of discriminants `−4, −3, −24` (the
> CM assignment read from the §3.1 table, UNVERIFIED).

### bostLowerBound

* Bundle field `HDec.HSyn.OpenResearchLeaves21.bostLowerBound`; kind **published**, strict **LEAF**; flag: locator UNVERIFIED (see the source).
* Source: Bost, Sem. Bourbaki 795 (Asterisque 237, 1996): h_D(A) >= -(g/2) log 2pi, Deligne normalization (display UNVERIFIED, height-split §2)
* packet [R5](#packet-r5); label long-pole (statement checks first; Lean only at Mathlib scale); tier T4 (model triage, unreviewed); discussion: [elliotglazer #85](https://github.com/elliotglazer/diophantine-z-q/issues/85).
* Human readings recorded: none.
* Status: open.

```lean
ZInQ.HeightSplit.BostLowerBound
```

> height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795), replaces `r21`.

### deRhamH1AbVarT

* Bundle field `HDec.HSyn.OpenResearchLeaves21.deRhamH1AbVarT`; kind **published**, strict **LEAF**.
* Source: H^1_et(A_Fbar, Q_p), written Hom(V_p A, Q_p), is de Rham with the printed D_dR (Faltings 1989; Tsuji 1999; Scholze 2013 Cor. 1.8, wording read by h-leaves)
* packet [R7](#packet-r7); label long-pole (statement checks first; Lean only at Mathlib scale); tier T4 (model triage, unreviewed); discussion: [elliotglazer #84](https://github.com/elliotglazer/diophantine-z-q/issues/84).
* Human readings recorded: none.
* Status: open.

```lean
ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
```

> **LEAF (the de Rham comparison for `H¹` of an abelian variety, printed `D_dR`).** As
> `DeRhamH1AbVar`, with `H¹_ét(A_{F̄}, ℚ_p)` replaced by `Hom_{ℚ_p}(V_p(A), ℚ_p)` with the
> contragredient action (the standard identification; Milne, *Abelian varieties*, Thm 15.1(a),
> UNVERIFIED) and `D_dR` in its printed form `(B_dR ⊗ W)^{G_F}`. Faltings 1989; Tsuji 1999; Scholze,
> Forum Math. Pi 1 (2013), Cor. 1.8; Fontaine 1982 for abelian varieties.

### dsThm965

* Bundle field `HDec.HSyn.OpenResearchLeaves21.dsThm965`; kind **published**, strict **LEAF**.
* Source: Diamond-Shurman, GTM 228, Thm 9.6.5 (Deligne 1971; Shimura 1971 Thm 7.14 for k = 2), coefficients extended along iota_L o iota_C^-1
* packet [R7](#packet-r7); label long-pole (statement checks first; Lean only at Mathlib scale); tier T4 (model triage, unreviewed); discussion: [elliotglazer #84](https://github.com/elliotglazer/diophantine-z-q/issues/84).
* Human readings recorded: none.
* Status: open.

```lean
ZInQ.Contrib.HodgeSplit.DSThm965
```

> **LEAF (Deligne's theorem, in Diamond–Shurman's form).** Diamond–Shurman, *A First Course in
> Modular Forms*, GTM 228 (2005), Thm 9.6.5 (for `k ≥ 2`; from Deligne, Sém. Bourbaki 355 (1969)
> [the Bourbaki talk, publ. 1971], and Shimura 1971 Thm 7.14 for `k = 2`; numbering UNVERIFIED): for a
> normalized eigenform `f ∈ S_k(N, χ)`, `k ≥ 2`, and `λ ∣ ℓ` in `K_f`, there is a continuous
> `ρ_{f,λ} : G_ℚ → GL₂(K_{f,λ})`, unramified at every `p ∤ ℓN`, such that for every maximal ideal `𝔭`
> of `ℤ̄` over `p` the arithmetic Frobenius `Frob_𝔭` has characteristic polynomial
> `x² − a_p(f) x + χ(p) p^{k−1}`. Lean form: coefficients extended along `K_{f,λ} → ℚ̄_ℓ` given by
> `ιL ∘ ιC⁻¹` (the place `λ` is the one `ιL ∘ ιC⁻¹` induces), places of `ℚ̄` as valuation subrings,
> arithmetic Frobenius as pkg-I4's `IsArithFrob`. The semisimplicity of the row is not part of this
> form (Ribet 1977 gives irreducibility; here it is the glue `Semisimplification2`).

### gaudronRemondThm14

* Bundle field `HDec.HSyn.OpenResearchLeaves21.gaudronRemondThm14`; kind **published**, strict **LEAF**.
* Source: Gaudron-Remond, Duke Math. J. 163 (2014) Thm 1.4 (read by the audit), over the published stable height
* packet [R5](#packet-r5); label long-pole (statement checks first; Lean only at Mathlib scale); tier T4 (model triage, unreviewed); discussion: [elliotglazer #85](https://github.com/elliotglazer/diophantine-z-q/issues/85).
* Human readings recorded: none.
* Status: open.

```lean
ZInQ.HeightSplit.GaudronRemondThm14
```

> height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces `r19`.

### gonzalezRotgerProp56X6

* Bundle field `HDec.HSyn.OpenResearchLeaves21.gonzalezRotgerProp56X6`; kind **published**, strict **LEAF**; flag: restated: Prop. 5.6 (read by the locator audit) for every witness of the moduli description of X0(6,1), with no existence claim; D(R) as the product of the p | D with (R/p) = -1 to be confirmed against the paper.
* Source: Gonzalez-Rotger, J. Math. Soc. Japan 58 (2006) Prop. 5.6, p. 943 (read by the audit) at (D,N) = (6,1), on every coarse witness of X0(6,1) (with the R1fp/X6 clause lists and Lemma QP, as for r1r2)
* discussion: [elliotglazer #86](https://github.com/elliotglazer/diophantine-z-q/issues/86).
* Human readings recorded: none.
* Status: open.

```lean
GRCountX6.GonzalezRotgerProp56X6
```

> gt-grcount, printed form: Gonzalez-Rotger 2006 Prop. 5.6 at (D,N) = (6,1) on X0(6,1), for every witness of the moduli description (no existence claim; the model comes from gonzalezRotgerX6Ab). Replaces gonzalezRotgerCountX6Ab.

### gonzalezRotgerX6Ab

* Bundle field `HDec.HSyn.OpenResearchLeaves21.gonzalezRotgerX6Ab`; kind **published**, strict **LEAF**; flag: locator UNVERIFIED (see the source).
* Source: Gonzalez-Rotger 2006 on X6 (printed form; locator UNVERIFIED)
* packet [R4](#packet-r4); discussion: [elliotglazer #86](https://github.com/elliotglazer/diophantine-z-q/issues/86).
* Human readings recorded: none.
* Status: open.

```lean
HDec.QMSplit.Moduli.GonzalezRotgerX6Ab
```

> x6-glue, printed form (on abelian schemes): González–Rotger, J. Math. Soc. Japan 58 (2006), Thm 5.12 (read by
> the locator audit), residue fields of CM points, on one canonical coarse witness `X₆`.

### hodgeTateDecompAbVar

* Bundle field `HDec.HSyn.OpenResearchLeaves21.hodgeTateDecompAbVar`; kind **published**, strict **LEAF**.
* Source: C_p (x) V_p(A) = C_p(1)^g + C_p^g, G_F-equivariant (Fontaine, Invent. Math. 65 (1982); Tate 1967 4; Faltings 1988), bases of the two g-dimensional spaces chosen
* packet [R7](#packet-r7); label long-pole (statement checks first; Lean only at Mathlib scale); tier T4 (model triage, unreviewed); discussion: [elliotglazer #84](https://github.com/elliotglazer/diophantine-z-q/issues/84).
* Human readings recorded: none.
* Status: open.

```lean
ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
```

> **LEAF (Hodge–Tate decomposition of the Tate module of an abelian variety).** Fontaine,
> *Formes différentielles et modules de Tate des variétés abéliennes sur les corps locaux*, Invent.
> Math. 65 (1982), 379-409, Théorème principal (with Tate 1967 §4, Cor. 2 of Thm 3 for good
> reduction, and Faltings, JAMS 1 (1988), for `H¹_ét`; all locators UNVERIFIED): for an abelian
> variety `A` of dimension `g` over a finite extension `F` of `ℚ_p` there is a `G_F`-equivariant
> `ℂ_p`-linear isomorphism `ℂ_p ⊗_{ℚ_p} V_p(A) ≅ (ℂ_p(1) ⊗_F t_A) ⊕ (ℂ_p ⊗_F t_{A'}^*)` with
> `dim_F t_A = dim_F t_{A'}^* = g` (`t` = tangent space at the origin, `A'` the dual). Lean form:
> after choosing `F`-bases of the two `g`-dimensional spaces, `ℂ_p(1)^g ⊕ ℂ_p^g`; `G_F` acts on
> `ℂ_p ⊗ V` by `σ ⊗ ρ(σ)` and on `ℂ_p(1)` by `c ↦ χ(σ) σ(c)`, through pkg-I4's `gfToGqp`
> (the embedding `ℚ̄_p ≅ F̄` behind Mathlib's `Field.absoluteGaloisGroup.map`, which identifies
> `ℂ_F` with `ℂ_p`). Specialization of the printed statement (bases chosen).

### javanpeykarBound

* Bundle field `HDec.HSyn.OpenResearchLeaves21.javanpeykarBound`; kind **published**, strict **LEAF**.
* Source: Javanpeykar, Algebra Number Theory 8 (2014) Thm 1.1.1 (read by the audit), for curves over K with a K-rational Belyi function, over the published stable height
* packet [R5](#packet-r5); label long-pole (statement checks first; Lean only at Mathlib scale); tier T4 (model triage, unreviewed); discussion: [elliotglazer #85](https://github.com/elliotglazer/diophantine-z-q/issues/85).
* Human readings recorded: none.
* Status: open.

```lean
ZInQ.HeightSplit.JavanpeykarBound
```

> height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi function,
> replaces `r18`.

### pazukiCor13Upper

* Bundle field `HDec.HSyn.OpenResearchLeaves21.pazukiCor13Upper`; kind **published**, strict **LEAF**.
* Source: Pazuki, Bull. SMF 140 (2012) Cor. 1.3(2), upper half (read by the audit; RISK: Pazuki's level-2 coordinates, height-split §8)
* packet [R5](#packet-r5); label long-pole (statement checks first; Lean only at Mathlib scale); tier T4 (model triage, unreviewed); discussion: [elliotglazer #85](https://github.com/elliotglazer/diophantine-z-q/issues/85).
* Human readings recorded: none.
* Status: open.

```lean
ZInQ.HeightSplit.PazukiCor13Upper
```

> height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`.

### r9a

* Bundle field `HDec.HSyn.OpenResearchLeaves21.r9a`; kind **published**, strict **LEAF**.
* Source: Faltings 1983 Satz 3
* packet [R7](#packet-r7); label long-pole (statement checks first; Lean only at Mathlib scale); tier T4 (model triage, unreviewed); discussion: [elliotglazer #37](https://github.com/elliotglazer/diophantine-z-q/issues/37).
* Human readings recorded: none.
* Status: open.

```lean
PkgI3.FaltingsSemisimple
```

> **I3.F1 — Faltings 1983, Satz 3 (semisimplicity).** For an abelian variety `A` over a number
> field `K` and a prime `ℓ`, the representation of `G_K` on `V_ℓ(A)` is semisimple.

### r9b

* Bundle field `HDec.HSyn.OpenResearchLeaves21.r9b`; kind **published**, strict **LEAF**.
* Source: Faltings 1983 Satz 4, Kor. 1
* packet [R7](#packet-r7); label long-pole (statement checks first; Lean only at Mathlib scale); tier T4 (model triage, unreviewed); discussion: [elliotglazer #37](https://github.com/elliotglazer/diophantine-z-q/issues/37).
* Human readings recorded: none.
* Status: open.

```lean
PkgI3.FaltingsTate
```

> **I3.F2 — Faltings 1983, Satz 4 (`A = B`) and Korollar 1 (Tate's conjecture).** For abelian
> varieties `A, B` over a number field `K` and a prime `ℓ`, the natural map
> `Hom_K(A, B) ⊗ ℤ_ℓ → Hom_{ℤ_ℓ}(T_ℓ A, T_ℓ B)` is injective with image the `G_K`-equivariant maps.

### raynaudSemistableSH

* Bundle field `HDec.HSyn.OpenResearchLeaves21.raynaudSemistableSH`; kind **published**, strict **LEAF**; flag: reading risk (reduct-b section 5): the print may assume an algebraically closed residue field; rated low by the next-fold review.
* Source: SGA 7 I Exp. IX Prop. 4.7 (Raynaud's criterion) over a strictly henselian DVR: m >= 3 invertible in O and A[m] rational over K imply semistable Neron models at O (number UNVERIFIED); with strictHenselizationPair gives the general-DVR 4.7 and, by K1 (Mumford 4 and [m] etale), 3.6
* packet [R1](#packet-r1); discussion: [elliotglazer #85](https://github.com/elliotglazer/diophantine-z-q/issues/85).
* Human readings recorded: none.
* Status: open.

```lean
ReductGlue.RaynaudSemistableSH
```

> reduct-glue (reduct-b), printed form, strictly henselian base: Raynaud's criterion, SGA 7 I Exp. IX
> Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR `O`: if `m ≥ 3` is invertible in `O` and the points of
> order `m` are rational over `K`, then `A` has semistable Néron models at `O`. Unrestricted in `K` and the residue
> field (`r6` is stated over every field); reading risk: if the print assumes an algebraically closed residue field,
> this form is stronger than the print for imperfect residue fields. Replaces, with `strictHenselizationPair`,
> `raynaudSemistable` and (by K1) `semistableReductionDVR`.

### semistablePersistsSHcp

* Bundle field `HDec.HSyn.OpenResearchLeaves21.semistablePersistsSHcp`; kind **published**, strict **LEAF**; flag: restricted form (char K = 0, perfect residue field): a specialization of every reading of the print.
* Source: SGA 7 I Exp. IX Prop. 3.3, first assertion, over a strictly henselian DVR with K of characteristic 0 and algebraically closed residue field, K'/K finite (number UNVERIFIED); with strictHenselizationPair gives SS1 and SS3 at number fields (ReductB.ss1_ss3_of_cp)
* packet [R1](#packet-r1); discussion: [elliotglazer #85](https://github.com/elliotglazer/diophantine-z-q/issues/85).
* Human readings recorded: none.
* Status: open.

```lean
ReductB.SemistablePersistsSHcp
```

> reduct-b, printed form, restricted: SGA 7 I Exp. IX Prop. 3.3, first assertion (number UNVERIFIED), over a
> strictly henselian DVR of a field of characteristic `0` with perfect, hence algebraically closed, residue field
> (a specialization of every reading of the print). With `strictHenselizationPair` replaces `semistablePersistsDVR`
> at its two uses, SS1 and SS3, which are over number fields.

### sga7_IX_3_3_SH

* Bundle field `HDec.HSyn.OpenResearchLeaves21.sga7_IX_3_3_SH`; kind **published**, strict **LEAF**; flag: locator UNVERIFIED: SGA 7 IX 3.3 may assume an algebraically closed residue field; then the print is SGA7PersistsNF.SGA7_IX_3_3_SHcp, or BLR 7.4 (numbering to read) covers this form.
* Source: SGA 7 I Exp. IX Prop. 3.3, second assertion, over strictly henselian traits: N0 x_S S' -> N'0 is an isomorphism for semistable reduction (number UNVERIFIED); with neronBaseChangeStrictHenselization (BLR 1.2/2) and fpqc descent gives the general-DVR field sga7_IX_3_3
* discussion: [elliotglazer #85](https://github.com/elliotglazer/diophantine-z-q/issues/85).
* Human readings recorded: none.
* Status: open.

```lean
SGA7PersistsNF.SGA7_IX_3_3_SH
```

> gt-sga7, printed form: SGA 7 I, Exp. IX, Prop. 3.3, second assertion (N0 x_S S' = N'0 for semistable reduction) over strictly henselian traits (number UNVERIFIED). With neronBaseChangeStrictHenselization, sga3_VIB_3_10 and geomConnOfRationalPoint replaces sga7_IX_3_3 (SGA7PersistsNF.sga7_IX_3_3_of_SH).

### sga7_IX_3_5_ForwardGeom

* Bundle field `HDec.HSyn.OpenResearchLeaves21.sga7_IX_3_5_ForwardGeom`; kind **published**, strict **LEAF**; flag: locator UNVERIFIED: if Prop. 3.5 reads semistability on the k(s) fibre, this form is a consequence through SemiAbelianDescendsSepClosed (standard for every separably closed field); if its display lacks the echelon clause, the square-zero bound comes from IX 2.4 (consequence).
* Source: SGA 7 I Exp. IX Prop. 3.5, forward direction at sigma = tau, over a strictly henselian DVR with K^s (number UNVERIFIED)
* discussion: [elliotglazer #85](https://github.com/elliotglazer/diophantine-z-q/issues/85).
* Human readings recorded: none.
* Status: open.

```lean
UnipotentForward.SGA7_IX_3_5_ForwardGeom
```

> gt-unip, printed form, strictly henselian base: SGA 7 I Exp. IX Prop. 3.5, direction semistable => (sigma-1)^2 = 0 on T_l = lim A(K^s)[l^n] for sigma in inertia, one sigma at a time (the print gives (sigma-1)(tau-1) = 0 and the converse); number UNVERIFIED. Semistability read on the geometric special fibre; reading risk: if the print reads it over k(s), this form exceeds the print by UnipotentForward.SemiAbelianDescendsSepClosed for imperfect residue fields only (the reading-robust variant is UnipotentForward.semistableUnipotent_of_forward). Replaces semistableUnipotent; StrictHenselizationInside and the K^s axis are proved.

### hCM

* Argument `hCM` of `frozenTarget`; kind **published**, strict **LEAF**; flag: unread: new printed leaf, no reading recorded; locator UNVERIFIED (numbers).
* Source: Shimura 1971 (Introduction to the arithmetic theory of automorphic functions) Thm 5.4, Shimura's reciprocity law at CM points, in idelic form (number UNVERIFIED)
* packet [R3](#packet-r3); tier T2 (model triage, unreviewed); discussion: [elliotglazer #74](https://github.com/elliotglazer/diophantine-z-q/issues/74).
* Human readings recorded: none.
* Status: open.

```lean
T5Glue.ShimuraMainCM
```

> **LEAF SHIMURA-5.4 (the main theorem of complex multiplication, with torsion; printed form in
> Weierstrass coordinates).** Let `K = ℚ(√−m) ⊂ ℂ` (through `κ`, `√−m ↦ i√m`), `e : Kˢ → ℚ̄`
> normalized (`ιC ∘ e = κ` on `K`), `σ ∈ Aut(ℂ)` and `s ∈ 𝔸_K^×` with `σ = [s, K]` on `K^ab`
> (`ArtinCond`). Let `𝔞 ⊂ K` be a lattice, `P` a period pair with lattice `κ(𝔞)` and `P'` one with
> lattice `κ(s⁻¹𝔞)`. Then there is `μ ∈ ℂˣ` such that `(x, y) ↦ (μ⁻²x, μ⁻³y)` is an isomorphism
> `E_P^σ ≅ E_{P'}` (`σ(g₂(P)) = μ⁴g₂(P')`, `σ(g₃(P)) = μ⁶g₃(P')`) and, for `u ∈ K \ 𝔞` and any
> `v ∈ K` representing `s⁻¹u ∈ K/s⁻¹𝔞` (`s_f v − u ∈ 𝔞̂`),
> `σ(℘_P(u)) = μ²℘_{P'}(v)` and `σ(℘'_P(u)) = μ³℘'_{P'}(v)`.
> 
> Source: Shimura 1971, *Introduction to the arithmetic theory of automorphic functions*, Thm. 5.4:
> for an analytic isomorphism `ξ : ℂ/𝔞 → E(ℂ)` there is a unique `ξ' : ℂ/s⁻¹𝔞 → E^σ(ℂ)` with
> `ξ(u)^σ = ξ'(s⁻¹u)` for all `u ∈ K/𝔞`; Lang, *Elliptic functions*, Ch. 10, Thm. 3; Silverman,
> *Advanced topics*, GTM 151, Thm. II.8.2 (for `𝒪_K`) (theorem numbers UNVERIFIED, from memory).
> Here `E = E_P : y² = 4x³ − g₂(P)x − g₃(P)` with `ξ = (℘_P, ℘'_P)`; every analytic isomorphism
> `ℂ/s⁻¹𝔞 → E^σ(ℂ)` is `z ↦ (μ²℘_{P'}(z), μ³℘'_{P'}(z))` for some `μ ∈ ℂˣ` (`ξ'(0) = ξ(0)^σ = O`,
> a holomorphic map of complex tori fixing `0` is `z ↦ αz`, and isomorphisms of short Weierstrass
> models are `(x, y) ↦ (μ²x, μ³y)`), so this is the printed statement, restricted to `u ∉ 𝔞` (then
> `v ∉ s⁻¹𝔞`, since `K ∩ 𝔞̂ = 𝔞`, so `℘_{P'}(v)` is a value, not the junk value at a pole); the
> conclusion holds for every representative `v` because two of them differ by an element of `s⁻¹𝔞`. Normalization:
> Shimura's `[s, K]` sends a uniformizer at `𝔭` to the arithmetic Frobenius, as Tau Ceti's Artin map
> does; then `E^{Frob_𝔭} ≅ ℂ/𝔭⁻¹𝔞`, consistent with `j(𝔞)^{Art 𝔭} = j(𝔭⁻¹𝔞)` used by the kernel's
> `MainTheoremCMj` (Tau Ceti: `globalArtinMap_isArithFrobAt`, `isArithFrobAt_of_globalArtinMap_ofAdicCompletion_eq`;
> re-check this direction if the Artin map is ever replaced). The Weierstrass-coordinate form is a standard consequence
> of Thm. 5.4; Silverman's II.8.2 covers only `𝒪_K`, while this leaf quantifies over lattices of every order.

### h33

* Argument `h33` of `frozenTarget`; kind **published**, strict **LEAF**; flag: sign of [i] verified from the paper (alpha = -i, L1564-1566) and pinned by TYZ Thm 3.6(1) in Lean (h33-sign); no human review of the paper itself.
* Source: Tian-Yuan-Zhang, Thm 3.3 (Gross-Zagier formula), printed form for n = 5, 7 (mod 8) (arXiv:1411.4728v1 L1299-1311)
* packet [R3](#packet-r3); label long-pole (statement checks first; Lean only at Mathlib scale); tier T4 (model triage, unreviewed); discussion: [elliotglazer #74](https://github.com/elliotglazer/diophantine-z-q/issues/74).
* Human readings recorded: none.
* Status: open.

```lean
ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33
```

> **Leaf TYZ-3.3: TYZ Theorem 3.3 ("Gross–Zagier formula"), printed form, for `n ≡ 5, 7 (mod 8)`.**
> 
> Source: Tian–Yuan–Zhang, *Genus periods, genus points and congruent number problem*,
> arXiv:1411.4728v1 (Asian J. Math. 21 (2017) 721–774), Theorem 3.3 (`\label{GZ}`, Period7.tex
> L1299–1311), with the definitions of §3.1: `Cl_n = Gal(H_n/K_n)`, `Cl'_n`, `σ` (L1263–1265), `Φ` and
> `P_χ` (L1279–1284), `𝒫(n) = 2^{−1−ρ(n)} 𝓛(n) α_n ∈ A(K_n)^- ⊗ ℚ` (L1288–1295), `h₂` (L992). The
> statement, for every positive squarefree `n ≡ 5, 7 (mod 8)`, every `Φ` and every character
> `χ : Cl_n → {±1}`:
> 
> * `P_χ` is non-torsion only if `χ = χ_{d₀,d₁}` with `n = d₀d₁`, `0 < d₀ ≡ 5, 6, 7`,
> `0 < d₁ ≡ 1, 2, 3 (mod 8)` (the character of `K_n(√d₁)`, resp. `K_n(√d₁*)` for `n ≡ 7`);
> * in that case `P_χ = ε(d₀,d₁) 2^{h₂(n)} 𝓛(d₁) 𝒫(d₀)` in `A(H'_n(i)) ⊗ ℚ`, `ε(d₀,d₁) = ±i` on
> `(5,3)`, `±1` otherwise.
> 
> Encoding (a reading of the same display, never stronger):
> * Model: the leaf is stated over the kernel's `basePt`, i.e. Heegner points on the eta-quotient model
> `X0.phiC`, whereas TYZ build `z_n` from an arbitrary identification `i_0`. Passing from the print to the
> leaf uses that the eta-model coordinates are rational functions on `X₀(32)` (q-expansion principle;
> `IsRatModFn 32` in Bridge.lean), so `phiC = [M]∘i_0` with `M ∈ End_ℚ(A) = ℤ`, which the existential
> `𝒫` absorbs. So the leaf is TYZ Theorem 3.3 carried along the eta model, not its literal display
> (statement review v2, M1).
> * `A(H'_n(i)) ⊗ ℚ ⊂ A(ℚ̄) ⊗ ℚ`; a vector of `A(ℚ̄) ⊗ ℚ` is `Q/m`; equality is "the difference of the
> cleared multiples is torsion". `A` is the kernel's `y² = x³ + 4x ≅ X₀(32)`, `ℚ`-isomorphic to TYZ's
> `2y² = x³ + x` by `(x, y) ↦ (2x, 4y)`, compatibly with `[i]`; `z_n = f_n(P_n)` is the kernel's
> pinned point `TYZ35.basePt n` (cm-numeric/cm-bridge; `(1 − [i]) f₀(P_n)` for `n ≡ 5`). TYZ print
> `f_n = f₀ − f₀∘[i]` (L1196) with `[i]` an automorphism of `X_U ≅ X₀(32)_{ℚ(i)}`; reading it as
> `(1 − [i])∘f₀` with this sign of `i` is fixed by the paper: in the proof of the Hecke-action
> proposition for `n ≡ 5` the cusps `[∞,1]`, `[0]` lie on the component of `P_n` and `α = −i`
> (about L1238, L1519, L1551, L1564-1566), so TYZ's `[i]` acts as `+i` there; with this sign
> `f_n = f₀∘[1 − i]` (about L1584) is `ϖ`-invariant up to 2-torsion (about L1586-1589), as Prop. 3.1
> and the proof of Thm 3.3 (about L1909-1912) need. It agrees with cm-numeric's numerics. With the
> other sign the lifts do not commute with `[i]`, the contributing and excluded characters swap,
> and the leaf would be false, not weaker (statement review of tyz-split, 2026-11-14).
> * Non-vacuity: the hypothesis on `ℓ` is satisfiable only if every `𝓛(m)²` (`m ≡ 1, 3`) is an integer
> square, i.e. together with `TYZThm11Integral` (TYZ Thm 1.1); otherwise the leaf (and the row,
> through `IsTYZLcal`) is vacuously true.
> * `h₂` is defined in TYZ §2 (L992) and reused in §3 (L2354).
> * `𝒫(d)` enters only through `Q d / m d` with `Q d ∈ A(K_d)^-` and `Q d` torsion when
> `ord_{s=1} L(E_d, s) > 1` (then `𝓛(d) = 0` by its definition, L338–345, so `𝒫(d) = 0`, L1295).
> This forgets the value `2^{−1−ρ(d)}𝓛(d)` of the coefficient (it needs Néron–Tate regulators,
> not in Mathlib): the leaf is weaker than the printed theorem, not stronger.
> * `𝓛(d₁)` (`d₁ ≡ 1, 3`, `n` odd) is defined up to sign (L364); `ℓ` is any integer choice with
> `ℓ(d₁)² = 𝓛(d₁)²` (`lcalSq`), the sign absorbed in `ε` (`ε` is chosen after `ℓ`).
> * Only `n ≡ 5, 7` (TYZ: `n ≡ 5, 6, 7`); then `d₀, d₁` are odd, so the classes `6, 2` do not occur
> (they are kept in the statement as printed).
> * `Φ` is encoded by lifts (`IsPhi`), `χ` is a character of `Cl_n = Gal(H_n/K_n)` itself.

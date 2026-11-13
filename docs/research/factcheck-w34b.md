# Fact-check of the wave 22-24 notes at origin/wip/integrate-w34b = 01267822

Read-only checkout (`.swarm-worktrees/zq-factcheck-w34b`, detached at 01267822). No Lean built; claims were checked with git grep and reading against the Lean at that commit. Six parallel readers covered the 13 notes. Items marked **[V]** I re-verified myself; the rest were checked by one reader only. Build times, `#print axioms` outputs, literature locators and model-review verdicts can't be checked from source and are not listed.

## Priority checks

**(a) leaf-adopt 48 of 56: CONFIRMED [V].**
- `scratch/h-decomposition/Leaves.lean` has exactly 8 `opaque … : Prop` (L18980 R01b, L18988 R03, L19008 R17, L19016 R18, L19040 R22, L19045 T10, L19050 T11, L19054 T12), no `axiom`, and one `sorry` (L19204, in `glueOutputs_of_leaves`; the other six "sorry" hits are docstring prose).
- `HSyn.ResearchLeaves` (L19109) has 26 fields and `HSyn.TextbookLeaves` (L19152) has 37. Leaf by leaf, 18 research + R1 partial + 4 opaque, and 30 textbook + 3 opaque. That gives 48/56 concrete plus R1(a,c,d), with placeholders R3, R17, R18, R22, T10, T11, T12 and R1(b), exactly as leaf-adopt.md:14-25 says.
- T32 is glue now (`HSyn.t32a_glue`, after L19054), not a field.
- Caveat already disclosed in the note: R16 (via `IsJ1`) and R19-R21 (height may be ⊤) may be vacuous.

**(b) bp-hecke-fe: CONFIRMED [V].**
- `BpHeckeFE.literature_hecke_fe_of_gaussPointCount (h1 : GaussPointCount) : HeckeContinuation5 ∧ ZInQ.Literature.FunctionalEquation5` (scratch/bp-hecke-fe/HeckeFE.lean:2700-2702). The second conjunct is the kernel Prop itself (ZInQKernel/Hypotheses/CR3Literature.lean:178-182): conductor 32d², root number −1, strip 0 < Re s < 2. No extra hypotheses, no `sorry` in the file.
- `GaussPointCount` (HeckeFE.lean:1863-1866) matches the note character for character.
  - Sign: LHS = p − #affine points = a_p = p + 1 − #E(𝔽_p).
  - π: `unitOf` (L419-424) makes unitOf(α)·α primary (≡ 1 mod 2+2i), so the RHS is π + π̄.
- Numeric check of the Lean statement as written: both sides agree for all 80 primes p ≡ 1 (mod 4) below 1000, and unitOf(α)·α is primary in every case (e.g. p = 5: −2 = −2).

**(c) rv-qm-polar Lemma P: conditions cited consistently, with two exceptions.** Details in items 2 and 3 below.
- Lean (scratch/rv-qm-polar/QMPolar.lean, namespace `RvQMPolar`, imported by nothing) formalizes the lattice level only, for N5's fixed μ = 2j+k:
  - `eq_smul_E0` (:239-241);
  - `eq_pm_E0_of_principal` (:274-277);
  - `riemann_sign` (:692-694);
  - `lemmaP_lattice` (:718-719): `∃! r : ℚ, (r•gram).det = 1 ∧ ∀ x ≠ 0, 0 < r·E0R(xj, x)`.
- It has no field F, no characteristic, no A or ι, no 𝒪v, and no general μ. No lemma relates `E0R` (:582) to `E0`.
- The citations of Lemma P all say "characteristic 0", except:
  - bp-qmmoduli.md:50-51 (§0 item 2), which omits "over F" and "abelian surface";
  - the `QML3` docstring (item 2 below).
- Name clash: route AP has its own "Lemma P" (`ZInQ.Mult.lemmaP_*`, ZInQKernel/Multiplication/Completeness/AP/LemmaP.lean, nt-22p.md:238). Consider renaming the QM one ("Lemma QP").

## Discrepancies, worst first

### Statement-level overclaims (some in Lean docstrings, including kernel copies)

1. **[V] `fibre_conjugates_isomorphic` does not say what the note and its docstring say.**
   - leaf-qm-fp.md:43-45 and the A7 row :350 claim "for every rational `j₀` there is an object `P` over `ℚ̄`, at a point over `j₀`, all of whose Galois conjugates …".
   - The Lean conclusion is `∃ P : QML3 Qbar, ∀ σ, ∃ Q, IsBaseChangeOf σ P Q ∧ ∃ α, Nonempty (QMIso (P.q.twist α) Q.q)`. `j₀` is used only in the proof. Places: scratch/leaf-qm-fp/QMLeaves.lean:1372-1375 (docstring :1367-1371 overclaims too); kernel ZInQKernel/HDecomp/QM/Leaves.lean:429; scratch/h-decomposition/Leaves.lean:15518.
   - Fix (Lean, preferred): strengthen the conclusion to `∃ Y Φ π y P, Φ Qbar y = M3.mk P ∧ π y = j₀ ∧ ∀ σ, …`. The proof already has these from `exists_fibre_object`.
   - Fix (or the docs): "∃ P : QML3 ℚ̄ whose conjugates are all Aut(𝒪)-twist-isomorphic to P; the link to a point over j₀ is in the proof, not the statement (use `exists_fibre_object` + `conj_twist_of_rational` for the linked form)".

2. **[V] The `QML3` docstring states Lemma P with no characteristic-0 condition.**
   - It says "a principal polarization … exists and is unique", while `QML3 K` is defined for every field K (no `CharZero`).
   - Places: scratch/leaf-qm-fp/QMLeaves.lean:208-210; kernel ZInQKernel/HDecomp/QM/Structures.lean:213-215.
   - The `R5fp`/`R5fpCount`/`QMLeaves` docstrings (QMLeaves.lean:1428-1429, 1463-1464, 1478-1479) also omit it, which is tolerable only because of the ℚ̄ context.
   - Fix: "in characteristic 0, a principal polarization … exists and is unique (SPECULATIVE: bp-qmmoduli §2.2; lattice core `eq_pm_E0_of_principal`)".

3. **[V] rv-qm-polar.md:73-76 (and :251-253) overclaim the compiled part.**
   - Claim: "Lemma P holds on every QM torus ℂ²/𝒪v, with every step in Lean except class number one … and the descent".
   - Not in Lean: the E0R = E0⊗ℝ identification; the combination with `eq_smul_E0` (docstring prose only, QMPolar.lean:713-717); the transport 𝒪 → 𝒪v; Riemann forms ↔ polarizations; μ other than N5's.
   - The `lemmaP_lattice` docstring (:713-717) makes the same "every QM torus" claim.
   - Fix: "…with its lattice steps in Lean for N5's μ on Λ = 𝒪 (`eq_smul_E0`, `eq_pm_E0_of_principal`, `lemmaP_lattice`); the E0R/E0 identification, Λ = 𝒪v, Riemann forms ↔ polarizations, class number one and descent are not".

4. **[V] rv-qm-polar.md:305-308, repair 3 points at the wrong place.**
   - The parenthesis "`λ' = ±λ∘ι(μ⁻¹μ')`, `μ'` rescaled to norm 6" is not in leaf-qm-fp.md §2.2 (:200-212).
   - It is in the `R1R2fp` docstring: scratch/leaf-qm-fp/QMLeaves.lean:1184-1185, kernel ZInQKernel/HDecomp/QM/Leaves.lean:240-241, and scratch/h-decomposition/Leaves.lean:15330-15331.
   - Fix: retarget repair 3 to those three docstrings.

5. **rv-qm-polar.md:297-304, the repair list is incomplete.**
   - The same SPECULATIVE premise text is now also in the kernel: ZInQKernel/HDecomp/QM/Leaves.lean:201-213, 485-486, 521, 537-539, and QM/Structures.lean:213-215.
   - It is also in leaf-qm-fp.md:189-191 and h-decomposition.md:161, 259, 319-320, 480, 508, 568, 880, 998, 1021, 1030.
   - Fix: add these locations to repair 2.

6. **[V] rv-jac-ext.md:148-149 says base change is missing; it isn't.**
   - Claim: "Base change `AbVar K → AbVar K̃` … is not in our layer (WP4)".
   - `PkgI3.AbVar.baseChange (A : AbVar K) (L) [Field L] [Algebra K L] : AbVar L` exists at ZInQKernel/HDecomp/Objects.lean:376. It was already there at the note's commit, and hdec-adopt3.md:76-77 uses it.
   - Fix: "Base change exists (`PkgI3.AbVar.baseChange`, Objects.lean:376); what is missing is the bridge `A_{K̃} ≅ ofJacobian J` (and polarizations)".

### Wrong numbers

7. **[V] hdec-adopt2.md:9 and :94: "93 … added here (179 before)", "all 93 new entries, like the 179 earlier ones".**
   - scripts/print_axioms.lean went from 182 (parent of 9a826482) to 272, so 90 were added. 93 is the line count of scratch/hdec-adopt2/axioms_section.lean, including its 3 header lines. log.md:32 repeats it.
   - Fix: "90 … (182 before)", "all 90 new entries, like the 182 earlier ones". The 272 total is right.

8. **[V] leaf-adopt.md:18 "All 118 `#print axioms`".**
   - Leaves.lean has 115 `#print axioms` lines for 114 declarations; `HSyn.sixContactMin_of_leaves` is printed twice (L19251, L19349).
   - Fix: "All 115 `#print axioms` lines (114 declarations)". Optionally drop the duplicate line.

9. **leaf-adopt.md:124: "one `sorry` warning (L19192)".**
   - `glueOutputs_of_leaves` is at L19202 (the `sorry` at L19204) after f2aa85b1's 10 header lines.
   - Fix: "L19202".

10. **[V] def-faltings.md:196-204 lists 15 `#print axioms`; the file has 16.**
    - The missing one is `ZInQ.DefFaltings.GroupModel.omegaAt_genericPt` (Faltings.lean:1933, theorem at :1248), added in e5605439.
    - Fix: add it to the §6 list.

### Imprecise claims about the Lean

11. **leaf-push2.md:30, `linYangTuple_onQMLocus` "is exactly … `OnQMLocus`".**
    - LeafPush2.lean:2069 and `onQMLocus_of_linYangTuple` (:2089) prove only tuple ⇒ `OnQMLocus`.
    - Fix: "implies `OnQMLocus` (the direction F1 uses)".

12. **leaf-push2.md:8-12, "13 of the 14 placeholders … now concrete".**
    - This counts R1, but R1(b) is still `opaque R01b_ComplexUniformization` (Leaves.lean:18980), and no concrete R1(b) exists anywhere.
    - Fix: "13 of the 14 (R1 only in parts (a), (c), (d))".

13. **leaf-push2.md:36-38, "T11a, T11b and T12 … rest on `UniformizationExists`".**
    - `T11b_Rigidity` (:2221) doesn't involve it.
    - `T11a_RiemannEnd` (:2210) takes Φ as a hypothesis; only its non-vacuity needs it.
    - Fix: "T12 (glue) and the non-vacuity of T11a rest on `UniformizationExists`".

14. **leaf-adopt.md:63 (also h-decomposition.md:311-312), "The four report files import kernel modules".**
    - Only QMLeaves.lean and ModCurveLeaves.lean do; T32a.lean and Faltings.lean import only Mathlib.
    - Fix: "Two of the four report files (QMLeaves, ModCurveLeaves)…".

15. **rv-qm-polar.md:41-44 (C3; also :96-97), "E_c is unimodular exactly when c𝒪 is the different … compiled as part of `type_eq_mu_mul`".**
    - `type_eq_mu_mul` (QMPolar.lean:403-404) gives c = μv, nrd v = 1, v† = v, E_c(x,y) = E0(x, vy). Nothing on determinants or the different.
    - Fix: "unimodularity of E_c follows from `type_eq_mu_mul` and `gram_det`; the 'exactly when the different' direction is not compiled".

16. **rv-qm-polar.md:50-52 cites the wrong lemmas.**
    - Anticommutation with μ is `chi2_mu`/`chi3_mu` (:517-518). `dag_conj_*` (:546-551) say Ad χ commutes with †.
    - Fix: cite `chi2_mu`, `chi3_mu` for anticommutation and `dag_conj_chi2/3` for "λ unchanged".

17. **rv-qm-polar.md:19-22, :31-33, :47-49: compiled scope.**
    - Lemma P is stated "for any μ with μ² = −6", but the Lean covers N5's μ only.
    - Uniqueness of v in "λ_μ∘ι(v) for a unique †-symmetric v" is not compiled; `type_eq_mu_mul` gives existence. The note elsewhere writes λ_μ∘ι(εv).
    - `twist_type` (:479-480) is the algebra only; ε and the family statement are argued.
    - Fix: mark each "(Lean: N5's μ only / existence only / algebra only)".

18. **rv-jac-ext.md:86, "G2 currently proves `[K:ℚ] ≤ 324!`".**
    - The Lean is the generic `GlueRepo.Numerics.splitting_degree_le` (ZInQKernel/HDecomp/Repo/Numerics.lean:29) for any separable f of degree ≤ 324. It is not about the fibre field.
    - Fix: say so.

19. **rv-jac-ext.md:3, :18, :188, :212 cite `docs/research/axiom-bridge.md` §4 and `AxiomBridge.ofJacobian`.**
    - Neither is on this branch (commits 4dfb22c2, 1d6fa26c are not ancestors).
    - Fix: "(on the axiom-bridge branch, not merged here)".

20. **rv-blueprints.md:75 (R19), "κ is monotone in the height, so the h_F form is stronger (`faltings_kappa_le`)" [V].**
    - `faltings_kappa_le` (scratch/rv-blueprints/Normalizations.lean:62-66) proves only the inner max inequality; monotonicity of κ is not in Lean.
    - Fix: say so.

21. **rv-blueprints.md:30, :186, "R16 transfers along any isomorphism `J ≅ J'`".**
    - `exists_quotient_transfer` (R16Transfer.lean:48-50) needs `[IsMonHom e.inv]`.
    - Fix: "along any isomorphism of group objects".

22. **def-faltings.md:212-214, "`AcceptanceEC` becomes a theorem modulo H5".**
    - Per §4 (:153) and Faltings.lean:1713-1717 it also needs AT1a and M2 for the minimal model.
    - Fix: "modulo H5, AT1a and M2 for the minimal model".

23. **bp-analytic.md: three imprecisions.**
    - :5-6 and :358 say "no warnings", but Torus.lean:20 disables `linter.unusedSectionVars`.
    - :168, :240, :322-323 call `analyticRep` a ring hom; it is three lemmas (`analyticRep_id/_comp/_mul`, :1594/1601/1620), not a bundled `RingHom`.
    - :67 and :309 state Liouville without hypotheses; `holomorphic_const` (:263) needs a full lattice in finite-dimensional E.

24. **leaf-qm-fp.md:351 (A10 row): `cm_of_val` is described as an equality.**
    - It gives one inclusion; the converse is the `R2X6Props` clause (QMLeaves.lean:1026). No t or j coordinate is in Lean.
    - Fix: "`cm_of_val` with `R2X6Props`: CM(ℤ[i]) = the fibre of π₆ over 0".

### Stale (integration already done, or line numbers moved)

25. **leaf-qm-fp.md:17-18, :324-338 (integration plan "SPECULATIVE"): already done by leaf-adopt.**
    - ZInQKernel/HDecomp/QM/ exists. `ResearchLeaves` uses `LeafAdopt.R1R2fpRep` (Leaves.lean:18705, with `R2X6PropsIff` and `R1pi0Props`), `R1rec`, `R5fp` and `R5fpCount`. R1(b) is `R01b_ComplexUniformization`.
    - :337 calls the structure `HSyn.Leaves`; it is `HSyn.ResearchLeaves`.

26. **leaf-modcurves.md:16-18, :285-288 (integration): done.**
    - Leaves.lean:19140 (`r16`), 19192 (`t33`), 19195 (`t34`); kernel ZInQKernel/HDecomp/ModCurves/.
    - :128-129, :208-210, :243: MC9 is now a citation-chain fact, not a leaf (Leaves.lean:16340-16345, rv-blueprints M1).
    - :279-283: the glue targets also include `VSurjOfSurjective`.
    - :288: "Copy §A-§H" should be "§A-§J".

27. **glue-t32a.md:10, :26-28, :85-89: integrated.**
    - ZInQKernel/HDecomp/B3Unram/T32a.lean:377. In Leaves.lean T32 is no longer a `TextbookLeaves` field (L19190; `HSyn.t32a_glue` L19071).
    - :11-12: the cited lines are L11918-11941 now, not L11908-11932.
    - :4: the file is 2266 lines, and the verbatim range is T32a L9-1816 = B3b L3-1810.

28. **rv-blueprints.md:89-90: the R20 additivity remark it calls false is already corrected** in h-decomposition.md:765-770 (leaf-adopt, credited to rv-blueprints F1). Fix: "the former remark … (corrected)".

### Nits (one line each)

- leaf-adopt.md:16, "19.2k lines": the file is 19350 lines.
- leaf-adopt.md:80, "same four fields": both `AbVar`s have five (`X` + four instances; Leaves.lean:2524, 17798). The L16670 docstring repeats "four".
- leaf-push2.md:45-46, "Every `#print axioms`": every theorem new in this task (10 of 72 theorems).
- leaf-push2.md:126-127: R3 disjunct 2's ≅ is a scheme isomorphism (`A.X ≅ E₁.X ⊗ E₂.X`, no `IsMonHom`).
- h-decomposition.md:306, "the 14 placeholder leaves", sits in a historical block but reads as current (now 7 + R1(b)).
- leaf-qm-fp.md:135: `Mathlib.IsPullback` should be `CategoryTheory.IsPullback`.
- leaf-modcurves.md:60-63: `rhoF_attached` is the trace clause in `Representation` form, not literally `AttachedTo`'s.
- hdec-adopt2.md:12: "eleven clusters" sits beside a 10-row table (Sqrt covers two drafts).
- rv-jac-ext.md:225: split the `routeW_degree` (ℕ) and `routeW_finrank` (field) rows.
- rv-jac-ext.md:218: `#print axioms` covers 5 of 8 theorems directly.
- glue-t32a.md:78-81: the "earlier glue" list misses `val_natCast_ne_zero`, `smul_sq_cases`.
- rv-qm-polar.md:244-245: relative to ι∘α the kept λ has type α⁻¹(μ) (as QMLeaves.lean:1184 says).
- rv-qm-polar.md:336: `pure_of_sq` gives the explicit equation (QMPolar.lean:596), not "nrd j = 1".
- rv-qm-polar.md:177: "integral" is `Enu_int` (:338).
- def-faltings.md:34-36: AN3's g is not tied to dim A in the Prop (Faltings.lean:1371-1375).
- def-faltings.md:182-183: `IsIsogeny` = `IsMonHom` + the project's `IsIsogenyMor`.
- def-faltings.md:73: the `AbVar` copy drops `IsCommMonObj`; `AbVar.dim` comes from Objects.lean:181.
- rv-blueprints.md:30, :380: `R5Repair.lean` is QMAbVar minus its `#print axioms` block.
- rv-blueprints.md:25-31: `audit_tail.lean` is an appended fragment, not a fourth compiled file.
- bp-analytic.md:310: `section Hom` is about 94 lines, not 120. :311: `QM.det_im_ne_zero_of_linearIndependent` is in `namespace QM`.
- bp-hecke-fe.md:33: `unitOf` has 8 unit entries on (ℤ/4)², 0 elsewhere. :293: `functionalEquation5_of_deuring_fourier` also takes d ≡ 5 (mod 8) and squarefree.
- scratch/rv-blueprints/R16Transfer.lean:3-21: the module header was copied from Jacobian.lean and describes declarations the file doesn't contain.
- QMPolar.lean:12: "New here (§§5-7)"; §8 is new too.

## Clean

No wrong claims were found in bp-hecke-fe, bp-analytic, def-faltings (bar item 10), leaf-modcurves (stale only) or hdec-adopt3. Every code block quoted in leaf-qm-fp and leaf-modcurves matches the Lean exactly. `same.py`'s hdec-adopt3 counts (T32a 19/19, ModCurves 84/99, QM 143/143, Faltings 133/138) reproduce.

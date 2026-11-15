# triage2 agent R: packet R1 (semistable reduction)

Read-only survey on wip/triage2 (base 9a100aa72). Nothing compiled. All paths are relative to the repo root.
Line numbers are at this base. Tags: VERIFIED = I read the code at file:line. SPECULATIVE = my inference.
Earlier triage (scratch/gap-triage/agent-CD.md, base e38375b3) is cited where I did not re-read the code.

## 0. Where the four fields go (the live path)

`sixContactMin_of_open28` (TailZ34:171) → ... → `sixContactMin_of_open17` (TailZ23:811) → `researchLeaves9_of_open14`
(TailZ23:773) → `sixContactMin_of_open11/10/9` (TailZ13:68, TailZ11:55, TailZ9:143) → `_of_open8` (TailZ4:257) →
`_of_open7` (TailX:277) → `_of_open6` (TailO:2920) → `_of_open4` (TailK:351). VERIFIED.

| field | converted at | becomes | used by (live) |
|---|---|---|---|
| raynaudSemistableSH | TailZ23:727 `raynaudSemistable_of14` (+ pair from `neronBaseChangeStrictHenselization`, TailZ28:119) | `ReductSplit.RaynaudSemistable` | (i) r6 (TailZ23:790); (ii) K1 → `semistableReductionDVR_of14` (TailZ23:734) → SS1 (TailZ23:763) |
| semistablePersistsSHcp | TailZ23:765 `ss1_ss3_of_cp` | `SemistablePersistsDVRnf` | SS1 (`semistableReductionThm_of_leaves_nf`, TailZ23:509, used twice, as `h33`) and SS3 |
| sga7_IX_3_3_SH | TailZ33:110 `sga7_IX_3_3_of_SH` | `CToPrinted.SGA7_IX_3_3` | SS2 only (`semistableNeronBaseChange_of_printed_full`, TailZ23:794) |
| sga7_IX_3_5_ForwardGeom | TailZ33:105 `semistableUnipotent_of_forwardGeom` | `ReductSplit.SemistableUnipotent` | r6 only (TailZ23:790); its other use, r8 (TailZ9:99), is dead |

VERIFIED: r8 is dead. `ResearchLeaves3.r8` (TailD:55) is never projected. Grepping `\.r8\b` finds only constructors.

Final consumers:
- **r6** (`PkgI2.RaynaudCriterion`, HDecomp/Objects.lean:1436, stated over every field). Three live uses, all in
  `gluePieces_of_open4` (TailK:319, 336, 338). VERIFIED:
  - `kernelFieldExists_of_split''` (TailC:6918) → `good_of_QML3` (TailC:5947) → `LeafQM.AV.QML3.goodReduction`
    (LPrefix:4229) → `goodReduction_of_QM_rational3'`. hRay is applied at LPrefix:833 with **m = 3, ℓ = 3** to a
    **QM abelian surface** (I² = 2, J² = −3, B = (2,−3), disc 6) whose A[3] is K-rational. The output feeds
    `quatUnipotentTrivial` (LPrefix:715), then NOS (r7a) gives good reduction. K is a number field
    (`FiniteDimensional ℚ K`). O is a DVR of K with 3 a unit.
  - `modelG3G6_of_leaves3` (TailI:53) → `qmModelG3_of` (TailF:2293): the same `QML3.goodReduction`. K ≤ L' with
    L'/ℚ finite, so K is a number field.
  - `linkedTateLocal_of_leaves3` (TailI:99) → `linkedTateLocal_of_tateBridge35` (TailH:5755) → `raynaudPlace_of_R6`
    (TailH:2577) and `raynaudPlace_rational` (TailH:2448).
    - Applied to the G7 model A over a number field: dim 2, `finrank End_K(A) = 4`, so QM over K (G7Out,
      TailA:1912).
    - Applied over F = K(A[m]) with **m ∈ {3, 7}** (p ≥ 7; TailH:2675) and m = q ∈ {3, 5} in the descents
      (TailH:3078, 3131).
    - ℓ is **any prime ≠ p**. The conclusion is used only for wild inertia, in the form "(σ−1)² = 0, p-power
      order ⇒ trivial".
  - So **every r6 use is at an abelian surface with QM, over a number field, at a DVR with finite residue field.**
    It is used only in the Galois form: inertia unipotent ⇒ trivial (by QM at ℓ = 3, or by p-power order).
- **SS1** (`semistableReductionThm`) and **SS2** (`semistableNeronBaseChange`) feed `heightRowsNo20_of8`
  (TailZ4:153) and `r20Lower_of8` (TailZ4:174), through `isStableFaltingsHeight_iff`.mpr and
  `stableFaltingsHeight_eq_of_semistable` (TailY:163, 210). VERIFIED.
  - The objects are those of agent-CD F1 (VERIFIED there at e38375b3, not re-read): the QM surface A, J₁(N)_L,
    P = A×Z and Z.
  - J₁(N) does **not** have potentially good reduction, so neither SS1 nor SS2 narrows to potentially good A.
  - The kernel height's own base-change invariance is already proved (`stableHeightBaseChange_of_hodgeLine`,
    TailK). SS1 and SS2 serve only to identify the printed (published) stable height with the kernel's.
- **SS3** (`semistablePersists`) has one consumer, `r20Lower_of8` (TailZ4:174) → `r20Lower_of_leaves'` (TailY:666).
  There it is applied only with L₁, the SS1 witness for A (and L₂ for B), to put A and B semistable over the
  compositum. VERIFIED (TailY:675-683).

None of the four is used only syntactically:
- `raynaudCriterion_of_leaves` (TailZ7:395) applies both hR (:402) and hU (:405);
- K1 applies hR (TailZ23:226);
- SS1 applies h33 (TailZ23:555, 562);
- SS2 applies hSS2 in the identification (TailY:173). VERIFIED.

---

## 1. raynaudSemistableSH: `ReductGlue.RaynaudSemistableSH` (TailZ14:1105)

1. **Statement.** O is a strictly henselian DVR of any field K, m ≥ 3 is invertible in O, and every point of
   A(K̄)[m] comes from A(K). Then every Néron model of A over O has a semistable geometric special fibre (SGA 7 IX
   4.7 at a strictly henselian base).
2. **Consumers.**
   - r6 via `raynaudCriterion_leaves` (TailZ14:243): QM surfaces over number fields, m ∈ {3, 5, 7} (§0).
   - SS1 via K1 `semistableReductionDVR_of_raynaud` (TailZ23:211): m ∈ {3, 4}, at DVRs of number fields, for all
     A in the height rows (J₁(N)_L etc.).
3. **Weakest form used.** `RaynaudSemistableSHcp` (TailZ23:303: `[CharZero K]`, perfect residue field) with
   m ∈ {3, 4, 5, 7}, and K a number field after the pair. SS1 alone already needs it for every A.
4. **Bypass or provable?** No removal.
   - Its SS1 use needs semistable reduction for J₁(N), which is general A.
   - Restricting to the cp form is the known narrowing (reduct-b §1, unipotent-b §4). It requires restating r6 over
     number fields: about 25 consumers, all of which are in fact at number fields (VERIFIED for the three live
     ones).
   - It also *subsumes* the SS1 use of semistablePersistsSHcp (§2).
5. **Tier.** Keep (T4). The cp narrowing is integrator work (T2), with no field-count gain.

## 2. semistablePersistsSHcp: `ReductB.SemistablePersistsSHcp` (TailZ23:315)

1. **Statement.** O is a strictly henselian DVR of a characteristic-0 field K with perfect (hence algebraically
   closed) residue field, K'/K is finite and O' lies over O. If A has semistable reduction at O, every Néron model
   of A_{K'} at O' is semistable (SGA 7 IX 3.3, first assertion).
2. **Consumers.**
   - SS1 (`semistableReductionThm_of_leaves_nf`, TailZ23:509). Persistence is used to move from the per-place
     witnesses F(O) of 3.6, and from K, to the global L₀.
   - SS3 → `r20Lower_of_leaves'` (TailY:666), only along L₁ ⊆ L₁L₂, where L₁ is SS1's witness. VERIFIED.
3. **Weakest form used.** Semistability of A_L and B_L over a single number field L, for both isogenous varieties
   in R20-lower, plus SS1. Persistence along arbitrary extensions is **not** needed.
4. **Bypass (new finding; SPECULATIVE glue, VERIFIED ingredients).** The field is removable.
   - **(b) Raynaud route.** Let L₀ = K'₃ ⊔ K'₄ ⊆ K̄, where K'_m is the field of definition of A[m]
     (`torsionFieldOfDefinition_of`, TailZ7:894).
     - At each DVR O'' of any finite L' ⊇ L₀, pick m ∈ {3, 4} invertible (`exists_three_le_isUnit`, TailZ23:193).
     - A_{L'}[m] is L'-rational: run K1's proof (TailZ23:217-245) with `fixedTorsionRational_inter` (TailZ23:143),
       `torsion_descends_etale` (TailZ14:1427) and hfix weakened by L' ⊇ K'_m.
     - Raynaud then gives `SemistableNeronModels (A.baseChange L') O''`.
     - `SemistableLocalGlobal` (TailZ7:737, proved: `semistableLocalGlobal_leaf` TailZ14:1072 from GapBLR) with
       `hasSemistableReduction_of` (TailZ7:333) gives IsSemistable for every Néron model over 𝓞_{L'}.
     - This proves SS1 with no persistence and no `SemistableAlmostAll`.
     - It also proves the "SS1 for every L' ⊇ L₀" form, so r20-lower takes L' = L₀(A) ⊔ L₀(B) and needs no SS3.
     - Cost: `OpenResearchLeaves9`/`8` carry SS3 as a field. This needs a bypass fold straight to
       `OpenResearchLeaves7` + `R20Lower`: a new `r20Lower` term and `heightRowsNo20_of8`'s terms (memory note:
       "fold with a weaker leaf: bypass").
   - **(a') SS2 route (overlap).** 3.3's second assertion implies its first. Prove `SemistablePersistsDVRnf`
     (TailZ23:425) from the already-derived `sga7_IX_3_3` (TailZ19:249; it is `sga7_IX_3_3_of_SH`,
     SGA7PersistsNF:379):
     - identity components commute with base change, already proved (`idComp_baseChange`, TailZ19:1238);
     - transport the semi-abelian witness along κ̄(O) → κ̄(O'), with connectedness via the same 04KV argument;
     - an open subgroup contains the identity component.
     - Then `ss1_ss3_of_cp`'s two terms work unchanged, with no chain restructuring.
5. **Tier.** (b) T2: K1 copy T1 plus the bypass fold. (a') T2–T3: scheme-fibre transport, where the memory notes
   warn of defeq/rw pitfalls. Recommend (b) for SS1 and either one for SS3.

## 3. sga7_IX_3_3_SH: `SGA7PersistsNF.SGA7_IX_3_3_SH` (Contrib/OneProof/SGA7PersistsNF.lean:60)

1. **Statement.** O ⊆ O' are strictly henselian DVRs with K'/K finite, and A is semistable at O, with Néron
   models 𝒩 and 𝒩'. For any hom c : 𝒩×_O O' → 𝒩' that is an iso on the generic fibre, the identity component U
   of 𝒩×_O O' maps by an open immersion onto 𝒩'⁰ (SGA 7 IX 3.3, second assertion).
2. **Consumers.** sga7_IX_3_3 → `identityComponentBaseChangeDVRRange_of` → `semistableNeronBaseChange_of_printed_full`
   (TailZ19:1650) → SS2 → `stableFaltingsHeight_eq_of_semistable` (TailY:163). This feeds R18, R19, R21, R22,
   StableHeightFinite and R20-lower, for all A in the rows (A, J₁(N)_L, P, Z; agent-CD F1).
3. **Weakest form used.** Only the inequality 𝒩₀.height ≤ 𝒩'.height for a semistable 𝒩₀. Its proof needs the
   open immersion 𝒩₀⁰ ×O_{L'} → 𝒩'. The proved `HeightAntitone` gives only the opposite inequality. Number fields
   suffice: the cp form `SGA7_IX_3_3_SHcp` (SGA7PersistsNF:79; gt-sga7 §4 option B).
4. **Bypass?** None. The published-height identification needs exactly this, and no potentially-good restriction is
   possible because of J₁(N). It overlaps §2: it implies the persistence uses, per (a').
5. **Tier.** Keep (T4). The cp restriction is a manual bypass already specified in gt-sga7 §4 (no count gain).

## 4. sga7_IX_3_5_ForwardGeom: `UnipotentForward.SGA7_IX_3_5_ForwardGeom` (Contrib/OneProof/UnipotentForward.lean:420)

1. **Statement.** O is a strictly henselian DVR, K^s is given, and ℓ is invertible in O. If A has semistable
   reduction at O, then (σ−1)² = 0 on T_ℓ for σ in inertia (SGA 7 IX 3.5, forward direction).
2. **Consumers.** r6 only (TailZ23:790; r8 dead). The objects are QM surfaces over number fields (§0):
   - m = ℓ = 3 for the `QML3.goodReduction` uses;
   - any ℓ ≠ p for the linkedTate wild-inertia use.
3. **Weakest form used.** "A[m] rational (m ≥ 3, p ∤ m) ⇒ inertia acts **unipotently** on T_ℓ" for QM abelian
   surfaces over number fields. The echelon-2 clause is not essential:
   - in `QML3.goodReduction`, B ⊗ ℚ₃ is a division algebra, so a unipotent element of the B-commutant is 1;
   - in linkedTate, unipotent plus p-power order already implies trivial.
4. **Bypass (SPECULATIVE, research-scale).** For the two `QML3.goodReduction` uses there is a semistability-free
   Galois proof:
   - ρ₃(G_K) ⊆ 1 + 3M₄(ℤ₃) is pro-3 (A[3] rational), so wild inertia acts trivially.
   - The tame 3-part is procyclic with φtφ⁻¹ = t^q, which gives N = log ρ(t) with φNφ⁻¹ = qN.
   - N lies in D₃^op (B ramified at 3), so Nrd(N)(q² − 1) = 0, hence N = 0.
   - So inertia is trivial on T₃, and NOS gives good reduction.
   - This needs the tame-inertia Frobenius relation at number-field places (not found in the repo:
     Tau Ceti has finite-level `TamelyRamified/Basic.lean`; `UnramProcyclic` (Contrib/UnramRoots/Reduction.lean:68)
     is only G/I procyclicity).
   - The linkedTate use (general ℓ ≠ p, at bad p) would additionally need:
     - Serre–Tate 1968 §2 ("potentially good ⇒ good over K(A[m]), m ≥ 3, p ∤ m"; numbering UNVERIFIED, same paper
       as r7a);
     - QM potential good reduction at p = 3 via ℓ = 2 (B is also ramified at 2);
     - threading End_K rank 4 / G3Out into `LinkedTateLocal`.
5. **Tier.** Removal by this bypass is T3–T4 (Galois machinery plus restructuring three consumers). Otherwise keep
   (T4). The cp/NF restriction (`SemistableUnipotent0`, unipotent-b) needs r6 restated, with no count gain.

## Summary of answers to the key questions
- **Applied to which abelian varieties?**
  - r6 (fed by raynaudSemistableSH and 3.5): only QM abelian surfaces over number fields (potentially good
    everywhere). VERIFIED.
  - SS1/SS2/SS3 (fed by raynaudSemistableSH via K1, persistsSHcp and 3.3_SH): every abelian variety in the height
    rows, including J₁(N)_L. No good-reduction bypass exists there.
- **Semistability used beyond unipotent inertia / Néron base change?**
  - r6: only via unipotent inertia.
  - Heights: only via Néron identity-component base change (SS2) and the existence of a semistable field (SS1,
    SS3). Height base-change invariance of the kernel height itself is already proved.
- **Overlaps.**
  - raynaudSemistableSH implies the SS1 use of semistablePersistsSHcp, and with a bypass fold also its SS3 use.
  - sga7_IX_3_3 (3.3 second assertion) implies semistablePersistsSHcp's use (3.3 first assertion) via the proved
    `idComp_baseChange` plus fibre glue.
  - **semistablePersistsSHcp is the removable one (T2).**
- **No field is syntactic-only.**

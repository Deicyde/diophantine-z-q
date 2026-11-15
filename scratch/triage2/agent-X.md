# triage2 agent X: packet R4 (the X6 Shimura-curve group)

Fields: `babaGranathRationalAb` and `deligneComponentsX6PrintedAb`. This was a read-only survey at base 9a100aa72. Nothing was compiled.
Paths are relative to the repo root. VERIFIED means I read the code at the given file:line. SPECULATIVE means it is my inference.

## 0. The live path (shared by both fields)

* Both fields pass through unchanged from the top bundles (OpenResearchLeaves21 at TailZ34:53 and OpenAddedLeaves17 at TailZ34:130) down to
  OpenResearchLeaves14 / OpenAddedLeaves12. The converters are TailZ34:104/163, TailZ33:111, TailZ29:110, TailZ28:113,
  TailZ27:115, TailZ26:122/184, TailZ25:127, TailZ31:61, TailZ30:65 and TailZ24:829. VERIFIED by grep.
* Each field has exactly one live reader, `x6Rows_of_open14` (TailZ23:712-722). VERIFIED. It builds `X6Leaves` (TailZ21:1444):
  * `deligneX6P := (deligneComponentsX6Printed_iff_ab hR).mpr l.deligneComponentsX6PrintedAb` (TailZ23:716);
  * `babaGranathR := (babaGranathRational_iff_ab hR).mpr r.babaGranathRationalAb` (TailZ23:720).
  
  Its output `(R1R2fpRep, X6ConicModel)` becomes `r1r2` (TailZ23:775) and `x6ConicModel` (TailZ23:749).
  The older x6Rows_of_open13 (TailZ22:264, which reads l.deligneComponentsX6PrintedAb at TailZ22:269) is not on the
  chain: sixContactMin_of_open17 (TailZ23:819) uses `_of_open14`.
* `x6Rows_of_leaves` (TailZ21:1453) calls `r1r2_of_published` (TailZ21:1428-1432) twice, the second time inside
  `x6ConicModel_of_published` (TailZ21:1436-1441). That gives
  `r1r2fpRep_of_printed_t5 (deligneComponentsX6_of_printed hD) hE hT (babaGranathX6'_of_rational' hB) ...`
  (TailZ20:1938-1942). This is the only place either field is consumed. VERIFIED.

## 1. deligneComponentsX6PrintedAb

**Statement.** `ShimuraGlue.DeligneComponentsX6PrintedAb` (TailZ22:33) says: there exist (Y,Φ,X,Ψ,fY) with
`R1fpPropsAb Y Φ ∧ X6Props Y Φ X Ψ fY ∧ DelignePi0 X Kfull`. `DelignePi0` (TailZ12:1300 area; the def is just above
`DeligneComponentsY3Printed`) is a bijection π₀(X ×_ℚ ℚ̄) ≃ ℚ^×_{>0}\A_f^×/nrd(Kfull), with a Galois-equivariance
clause.

**Consumers, followed to the end (all VERIFIED):**
1. `deligneComponentsX6_of_printed` (TailZ12:1372-1383) uses only the bijection `c`. It discards the sign ε and the
   Galois clause (`obtain ⟨..., c, -, -⟩`). With `pi0_Kfull_eq_one` (TailZ12:984, proved) it gets
   `ConnectedSpace (baseQbar X)`, which is `DeligneComponentsX6` (TailZ12:1266).
2. `geomConnX6_of` (TailZ20:1801-1803) applies the field `geomConnOfAlgClosure` to get `R1pi0Props X`, i.e.
   `GeometricallyConnected X.hom` (LPrefix:5143). That is `GeomConnX6` (TailZ20:1770).
3. `canonicalCoarseX6_of` (TailZ20:1777) passes `hpi` into the last clause of `CanonicalCoarseX6` (TailZ20:185).
   From there it goes to:
   * `coarseX6OfFine_of` (TailZ20:212-219): `hpi0` goes into the last clause of `CoarseX6OfFine` (TailU:1882);
   * `r1r2fpRep_of` (TailU:1915-1922): `hpi0` becomes the last clause `R1pi0Props X` of `R1R2fpRep` (LPrefix:5218-5223);
   * the other readers of `CanonicalCoarseX6` drop it: `canonicalModelY3_of_coarse` (TailZ20:1719) and
     `pairsLift_of_canonical` (TailZ20:1026-1028, which has a `-` in the last position).
4. **No reader of `R1R2fpRep` reads `R1pi0Props`.** I checked every theorem that takes `R1R2fpRep`:
   * `R1R2fp_of_rep` (LPrefix:5229) has `-` in the last position. The other consumers go through it: TailI:83/85,
     TailK:75-81, TailU:1992, TailN:41, TailC:8344/8452, and LPrefix:12543/12549.
   * `pairsLift_of_rep` (TailZ20:1031), `r1rec_of_rep` and `r5fp_of_rep` (TailZ5:261, 270) also have `-` in the last position.
   * `descend_main` (TailO:1245) reads `hR1, -`.
   
   The earlier triage reached the same result (scratch/gap-triage/triage.tsv row R01: "R1pi0Props discarded").

**Weakest form used.** The only part of the field that is used is the existence of one witness (Y,Φ,X,Ψ,fY) with
R1fpProps(Ab) ∧ X6Props. Its connectedness reaches only a conjunct that nothing reads. This is a syntactic-only use.
The same kind of witness comes with `babaGranathRationalAb`, `gonzalezRotgerX6Ab` and `elkiesX6StarPrinted`.

**By-product.** The field `geomConnOfAlgClosure` (TailZ34:133) has the same single live reader, TailZ23:718. It
is used only in `geomConnX6_of`. VERIFIED by grep `\.geomConnOfAlgClosure|geomConn :=`: the other hits are TailZ22:270
(not on the chain) and `l.geomConn` in TailZ19:1775/1781, which is a different structure (GeomConnOfRationalPoint).
So the prune removes that field too. Note that OPEN.md:66 shows it as "held by the project (claim)".

**Plan (tier T2; mechanical, but it touches many sites).** Use the semantic prune recipe as in docs/research/sem-prune.md §1.1.
* P1, threaded weaker variant. Define `R1R2fpRepW` as `R1R2fpRep` without `R1pi0Props X`, with an
  `R1R2fp_of_repW` that has the same proof. Replace the type `LeafAdopt.R1R2fpRep` by `R1R2fpRepW` in:
  * the `r1r2` fields of the old bundles: TailD:42, TailE:6460, TailN:67, TailX:72, TailZ4:67, TailZ9:26, TailZ15:26,
    LPrefix:11590, LPrefix:13624;
  * the dependent fields `∀ h : R1R2fpRep, ...`: TailD:470/475, TailE:6462/6556, TailN:69, TailI:183, TailU:1967/2274;
  * the 13 consumer theorems listed in item 4.
  
  Then:
  * `r1r2fpRep_of` (TailU:1915), `r1r2fpRep_of'`, `r1r2fpRep_of_split`, `_split5`, `_split6`, `_printed`, `_printed_t5` all lose
    `CoarseX6OfFine`'s / `CanonicalCoarseX6`'s pi0 clause. They then take `CanonicalCoarseX6W` from any witness, e.g. the one in
    `GonzalezRotgerX6` or in `BabaGranathX6'`.
  * `r1r2_of_published` loses `hD` and `hE`.
  * `X6Leaves` loses `deligneX6P` and `geomConn`.
  
  About 80 occurrences: `grep -c R1R2fpRep` gives 80 lines. A long rebuild (LPrefix) is expected.
* P1', a cheaper variant (SPECULATIVE, so check the policy first): delete the last conjunct from the def of
  `R1R2fpRep` itself (LPrefix:5223). Then fix the one producer (TailU:1922, drop `hpi0`) and the 4–5 destructuring
  patterns (drop the trailing `-`). This edits a chain definition, so a hash or faithfulness guard may object
  (memory: "hash guard without base tree").
* P2, bypass with no prune (tier T3): prove `R1pi0Props` on the Elkies witness from `X6Glue.ElkiesCharts`
  (TailZ21:1127).
  * `t.U` and `t.V` are affine with ring `ElkiesRing ≅ ℚ[s,r]/(r²+3s²+3)`. Over ℚ̄ this ring is
    `ℚ̄[u,u⁻¹]`, where `u = r+√−3·s` and `u(r−√−3 s) = −3`, so it is a domain. Two irreducible opens that meet give an
    irreducible, hence connected, X_ℚ̄. Then apply `GeomConnOfAlgClosure`, which stays a field.
  * This removes only Deligne.
* Recommendation: P1. It removes two fields and needs no new mathematics.

## 2. babaGranathRationalAb

**Statement.** `HDec.QMSplit.Moduli.BabaGranathRationalAb` (TailZ22:91-103) says: there exist a witness (R1fpPropsAb ∧ X6Props)
and π : X → P¹, with three distinct values t₄, t₃, t₂₄ ∈ P¹(ℚ), such that:
* π(x) = π(x') ⟺ the pairs are Aut(𝒪)-twists, and
* HasCM4 / HasCM3 / HasCM24 ⟺ π(x) = t₄ / t₃ / t₂₄ (biconditionals).

**Consumers (VERIFIED).**
* Its only use is `babaGranathX6'_of_rational'` (TailZ21:760, through `_of_rational` at TailZ21:678-695). That function applies a
  Möbius map to send (t₄, t₃, t₂₄) to (0, ∞, −16/27) and gives `BabaGranathX6'` (TailZ20:1808), whose content is
  `R2X6PropsIff` (LPrefix:5152). From there:
  * `babaGranathX6_of` (TailZ20:1816) and `hauptmodulOfX6_of` (TailZ20:221) feed the `R2X6PropsIff` clause of `R1R2fpRep`
    (TailU:1922);
  * `R1R2fp_of_rep` (LPrefix:5230) splits that clause into `R2X6Props` (the forward directions) and
    `CMExists = cmExists_of_iff h2 hs.1` (LPrefix:5181). **So the "⟸" direction is used only to produce `CMExists`**
    (Leaves.lean:141), the existence of ℚ̄-points with CM by ℤ[i], ℤ[ζ₃] and ℤ[√−6].
* `CMExists` is really consumed. For example, `conicOfWitness_of_elkies` (TailZ20:1888-1906) passes `hcm` to `HauptmodulUniqueX6S`,
  `cm_of_val` (Leaves.lean:205) uses it, and so does `cmObjectsExist_of_R1R2fp` (TailL:250).

**Overlap with another field (VERIFIED).** `ElkiesEquationsX6Ab` (TailZ22:73-85) is already derived on the live path from the
open field `elkiesX6StarPrinted` (TailZ34:74) by `ElkiesX6Star.elkiesEquationsX6Ab_of_printed` (Contrib/OneProof/
ElkiesX6Star.lean:118; used at TailZ29:112). It has on its own witness:
* the same fibre clause;
* the forward CM clauses at the distinct rational values t = 1, ∞, 0.

The only thing BG adds is the converse direction. Given the fibre clause and one CM point of each kind, the converse is
exactly `cm_of_val` (Leaves.lean:205-221), using `hasCM*_twist` (Pairs.lean:178-183) and `HasCM*.of_iso`
(Pairs.lean:148-165). So:

    BabaGranathRationalAb ⇐ ElkiesEquationsX6Ab ∧ CMPairsExist,
    CMPairsExist := (∃ P : QMPair Qbar, HasCM4 P.q) ∧ (∃ P, HasCM3 P.q) ∧ (∃ P, HasCM24 P.q)

Take t₄ = 1, t₃ = ∞, t₂₄ = 0, and `x := Ψ.symm (mk P)` for the CM points. This step is T1 (a few hours) and is pure glue.

**Weakest form used.** `CMPairsExist`, meaning that QM surfaces over ℚ̄ with CM by each of the three orders exist. This is in
addition to fields already in the bundle. No proved or bundled statement gives that existence today:
* `R5ptProps`, `GonzalezRotgerProp56X6`, `CMOptimalEmbedding` and `QMCentralizerCMC` are all conditional on a CM object
  (TailC:2270, TailU:1484; gt-grcount.md §2 says "no existence claim").
* The pi0-x6 route (LPrefix:9502) needs the unproved `AGInputs`.

**Can CMPairsExist be proved from fields already on the path? (SPECULATIVE plan; the pieces are VERIFIED.)**
1. Get a CM object over ℂ from the open leaf `shimuraMainThmIDeligneY3AbU` (Contrib/OneProof/RayClassShimura.lean:1152).
   * Its `ModuliAtUnits` clause (RSh:1135) at u = 1 (`OhatQ_one`, RSh:1235) gives, for every τ, a `P' : QML3 ℂ`
     uniformized by Λ_τ = ι(𝒪)(τ,1)ᵀ with `IotaCompatible` (TailC:7514).
   * Pick τ with ι(β)(τ,1)ᵀ = λ(τ,1)ᵀ:
     * β = i+j (β² = −1): τ = √2 + i;
     * β = (1+j)/2 (β²−β+1 = 0): τ = i√3 (already `z3`, RSh:795, `isCMPoint_q3`, RSh:804);
     * β = 2j+k (β² = −6): τ = i(√3+√6).
     
     These are hand computations with ι(i) = diag(√2,−√2) and ι(j) = [[0,−3],[1,0]] (`qmMat_oI`/`qmMat_oJ`, RSh:2291/2295). I have not checked them in Lean.
   * Multiplication by λ preserves Λ_τ, because λ·ι(a)(τ,1)ᵀ = ι(aβ)(τ,1)ᵀ.
   * `HomLatticeCorr.2` (Contrib/HomUnify/Corr.lean:77-93) gives a unique f ∈ End P'.A lifting λ. HomLatticeCorr itself comes from
     `AvSplit.Final.h69` (TailQ:2380), built from the textbook fields `uniformizationLeafAll` and `gagaMorphism`, which
     the chain already uses at TailZ34:106.
   * Uniqueness gives f ∈ com and f² = −1 (resp. f²−f+1 = 0, f² = −6). This mirrors `liftM_*` and `liftM_comm` (RSh:2234-2300) in the
     reverse direction.
   
   Tier T2.
2. Descend to ℚ̄. `cmDescends_of` / `descend_main` (TailO:1303 / 1176) need STQM (= `stQM_lf7 l.shimuraTaniyamaQbar`,
   TailX:261, an open field already on the path), T11b (`t11bExists_lf8`, TailZ4:60, proved) and T5.
   They read their `R1R2fpRep` argument only for its `R1fpProps` witness (TailO:1245, `obtain ⟨..., hR1, -⟩`). So a
   verbatim copy that takes `(h1 : R1fpProps Y Φ)` avoids the circularity. Use the witness of
   shimuraMainThmIDeligneY3AbU, or any witness, together with rigidity. Tier T1.
3. The fold: the converter at the top level must take `l` (for shimuraTaniyamaQbar) and `t` (for uniformizationLeafAll,
   gagaMorphism and T5). sixContactMin_of_open28 (TailZ34:171) has all of them.

**Result.** `babaGranathRationalAb` is removed with no new leaf. Overall T2–T3. The fallback (T1) is to replace it by the
much weaker leaf `CMPairsExist` (Shimura 1967 / Shimura–Taniyama). Either way the UNVERIFIED BG "§3.1 CM assignment"
reading disappears. The CM assignment then rests on Elkies' 0/∞ orientation, which is already flagged on elkiesX6StarPrinted.

## 3. Interactions

* Do Deligne P1 and BG in either order. After both, `r1r2_of_published` needs only BG' (from Elkies plus CMPairsExist),
  RayClassCM, GonzalezRotgerX6 and T5.
* Neither field depends on `gonzalezRotgerX6Ab`. That field is still needed for `R5ptProps` and as the witness in
  gonzalezRotgerCountX6Ab_of_printed (TailZ27:110).

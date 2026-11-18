# c8-conrad: step C8 by local algebraicity (Conrad, App. B) — no defect, but the Picard rows cannot leave the route through C8

Task c8-conrad, 2026-11-17. Base: wip/c8-conrad `d67ea55f6` (wip/leaf-fold33b; origin/main is an ancestor). Results
log: `scratch/c8-conrad/log.md`. This is model work; nothing here has been reviewed by a person.

**VERIFIED** means read in a named file on this host, computed, or compiled. **STANDARD** means published, with the
reference given. **SPECULATIVE** means not checked. Theorem numbers given from memory are marked UNVERIFIED.

## 0. Verdict

1. **Why the appeal to Conrad was replaced: not because of a defect.** No review records a defect in the manuscript's
   use of Conrad's Appendix B (§1). The replacement was a shortening. Version 14/16 had used the determinant argument,
   up-h §4 item 1 recommended adopting it, and task h-v16-adopt did so. The project's notes also record that Conrad's
   paper is an unrefereed preprint. So there is **no Known issue** about Conrad App. B, and the task's main branch
   applies.
2. **The target is out of reach through C8 (VERIFIED: source reading and a field-taint run on the built top, §2).**
   `picRepresentableAbVar` and `kleimanPicZeroProper954SiteQ` have **three** live consumers. C8 is only one of them:
   * (i) C8: `DetTate` (`det V₅(A) = χ²`, from the Weil pairing) in `G12DetPZ`;
   * (ii) step E1-E2: Poincaré reducibility, field `t8`/`poincareComplement`, at manuscript L865;
   * (iii) step C3/G9: the field `hodgeTateDecompAbVar`, where the Hodge–Tate multiplicities `a = b` come from the
     Weil pairing (hodgetate-from-dr). It feeds R10 (`r10`), which G9 and G11 read.

   Rerouting C8 to Conrad removes consumer (i) only. Both rows stay hypotheses of `frozenTarget`, and the reroute
   would add a leaf and three glue Props without removing a field. So **no fold is proposed** (§5).
3. **Lean (VERIFIED compiled, standard axioms; §3-§4).** `scratch/c8-conrad/C8Conrad.lean`, copied to
   `ZInQKernel/Contrib/OneProof/C8Conrad.lean`, contains:
   * the printed-form statement of Conrad's App. B for base field `ℚ_p`, written over Tau Ceti's local Artin map
     (`ConradAppBQp`);
   * three named glue Props;
   * a proof of C8's consumer `HDec.G0Galois.G12DetPZ` from these, with neither `DetTate` nor the Weil pairing
     (`g12DetPZ_of_conrad`).

   `G12DetPZ` turns out to be equivalent to "the twist has finite image" (§4). `#discharges`: no open hypothesis is
   discharged, as expected.

   This is ready for the day consumers (ii) and (iii) are rerouted too. At the call site
   (`g8_g12_of_leaves3_hf_pz_eb`) it is a one-term replacement (§5).
4. **Conrad App. B is unread on this host (Known limitation, not a Known issue).** WebFetch of
   `math.stanford.edu/~conrad/papers/locchar.pdf` was refused by the sandbox's domain check, and no copy was found. The statement used here is the one reported by Glazer's theorem-application audit
   (`docs/theorem-application-audit/evidence/parallel-galois-height-report.md` L94-104; §1.2). It keeps the flag
   **unread**.

## 1. Why the appeal to Conrad was replaced (VERIFIED, read in the named files)

### 1.1 The record

| source | what it says about C8's local-algebraicity sentence |
|---|---|
| h-trust.md C8, "Finiteness of ψ: the determinant argument" (L637-639) | the determinant argument "replaces N5's appeal to local algebraicity of Hodge–Tate characters at L760-761. This is Version 14's argument, kept in Version 16 at V16 L660-667". It was adopted by task h-v16-adopt "after up-h §4 item 1". |
| h-trust.md C8, "Suppliers" (L697-699) and §2.4 (L1034-1036) | "No longer used: local algebraicity … The determinant argument makes it unnecessary." The row `conrad-local-characters` "is gone". No defect is given as the reason. |
| up-h.md §4 item 1 (L307-312), under "Shortening h-trust.md: marginal (SPECULATIVE recommendations)" | replace local algebraicity by V14's determinant argument; "This removes the conrad-local-characters row … and the class-field-theory step of C8". |
| rv-h-c8.md §4 (L172-192), the focused review of C8 on the N5 text | N5's chain (Hodge–Tate character ⇒ Tate/Sen local algebraicity ⇒ class field theory ⇒ finite order) is "VERIFIED as an argument; the cited theorems STANDARD". Its one remark (item 3): the finiteness of `ψ` on inertia at `ℓ ≠ 5` is asserted "without argument … it is elementary". §3.1: Hodge–Tate suffices; de Rham is not needed. |
| rv-h-trust.md §1.2 item 1 | the input missing from C8 is (HT) for eigenforms. Both routes need it. It is not Conrad's appendix. |
| rv-up.md row 2d and §2.3 | the determinant argument is sound and "removes the local-algebraicity leaf but not the (HT) supplier and not Kronecker–Weber". |
| h-leaves.md L581, L638; h-v14.md L83, L567; nt-h.md L62, L408 | Conrad's paper is an "unrefereed … preprint". Upstream Version 14 dropped it (citation count 0; v14-routes.md L239-258). The refereed replacements named are Serre 1968 Ch. III and Tate 1967 §3.3. |
| Glazer's theorem-application audit, A011 (`docs/theorem-application-audit/evidence/parallel-galois-height-report.md` L94-118) | accepts A011. It **added** the Conrad citation to the manuscript (`MANUSCRIPT_EDITS.json` L135-136: the old text said only "By class field theory over ℚ"). Its conclusion: "There are no newly detected mathematical gaps in these five interfaces". |

**Conclusion.** No defect in the manuscript's use of Conrad App. B is recorded. The caveats on record are:
* the source is an unrefereed author preprint, which affects the LEAF rating (§3.2) but is not a gap;
* N5 states the elementary finiteness at `ℓ ≠ 5` without argument, which is on-the-spot glue inside
  `FiniteOfLocAlgTrivialQ` (§3.3).

### 1.2 The cited statement

The manuscript (diophantine_zq.tex L758-764) says, paraphrased: the twisting character is a de Rham subrepresentation
of the Hom representation and is unramified outside finitely many primes. Local algebraicity
[conrad-local-characters, App. B, pp. 32-33] and class field theory over ℚ make it a finite character times an
integral power of the cyclotomic character. The weight comparison then forces `k = 2` and power zero. The bibliography
entry is at L11046-11049 (author preprint, December 11, 2011).

**Not read on this host.** WebFetch of the PDF was refused by the sandbox ("Unable to verify if domain
math.stanford.edu is safe to fetch"). The audit's pinned copy (`work/theorem-application-audit-20261105/…/conrad-locchar.pdf`, SHA256 `782fe71a…`) is not in
this repository, and no `*locchar*` file was found in the worktree (a host-wide search was blocked by the sandbox). The statement below is **as reported by the theorem-application
audit** (report L102; the report does not say whether its reader was a person or a model):

> "The paragraph after Definition B.1 states that a continuous character with values in a finite extension of Q_p is
> locally algebraic exactly when its underlying Q_p-representation is Hodge-Tate. It explicitly covers coefficient
> fields larger than Q_p. The arithmetic-Artin normalization and the local product formula are given immediately
> after it."

The audit applies it with base field `L = ℚ₅`: "a locally algebraic character on a neighborhood of 1 in Q_5^* is x
mapped to x^n for a single integer n" (L104). Definition B.1's exact wording, and whether the paragraph also ties the
exponent to the Hodge–Tate weight, remain **unread** (UNVERIFIED). This is why the weight dictionary is a separate glue
Prop below.

## 2. The consumers of the two Picard rows

### 2.1 By reading the source (VERIFIED by grep on the base)

| # | path from `OpenAddedLeaves27` | consumer | manuscript step |
|---|---|---|---|
| 0 | TailZ72 `openAddedLeaves26_of_OpenAddedLeaves27`: `kleimanPicZeroProper954 := KleimanSite.kleimanPicZeroProper954_of_siteQ …` | (bundle map) | — |
| 1 | TailZ69 `openAddedLeaves22PZ_of_OpenAddedLeaves26` (both rows ↦ `PicZeroAbVar0`) → EichlerBoundCopy `sixContactMin_of_open45_pz_eb` → PicZeroCharZeroCopy `openAddedLeaves18_of_OpenAddedLeaves22_pz` (`phiAmpleIsogeny`, `weilPairingMumford`) → `t09SymmIsogenyExists` → `detTate_of_leaves4_pz` (EichlerBoundCopy L2703, in `gluePieces_of_open4_hf_pz_eb`) → `GaloisPieces.detTate` → `g12Det_of_pz` (L2485) → `G12DetPZ` | (i) **C8**, the twist's finiteness | L758-766 |
| 2 | same entry → PicZeroCharZeroCopy `openTextbookLeaves13HF_of_open16_22_pz`: `poincareComplement := PicZeroChar0.Poincare.poincareComplement_of_open0 l.picRepresentableAbVar l.picZeroAbVar …` → `t8` → EichlerBoundCopy L2602 `obtain ⟨Z, g, hisoZ⟩ := t.t8 …` (in `glueOutputs_of_leaves3_hf_pz_eb`) | (ii) **E1-E2**, Poincaré reducibility | L865 ("Absolute simplicity and Poincaré reducibility give an L'-isogeny A×Z→J") |
| 3 | TailZ74 L381 (the current top's research map): `hodgeTateDecompAbVar := hodgeTateDecompAbVar_of_open_k954 n.hodgeTateDecompExists t.mumfordTorsionAlgClosed l.picRepresentableAbVar l.kleimanPicZeroProper954` (TailZ69: through `t09SymmIsogenyExists0_of_open_k954`) | (iii) **C3/G9**, Hodge–Tate multiplicities `a = b` by the Weil pairing | L734-738 and lemma `lem:de-rham-descent` (L10940-11003) |

Consumers (ii) and (iii) are not at C8, and the manuscript does not use a Picard scheme at either step:
* at (ii) it says "Poincaré reducibility" with no citation;
* at (iii) it cites Scholze Cor. 1.8 and Faltings 1988 Ch. III Thm 4.1.

The Picard rows reach (ii) and (iii) because of how the project proved those steps (piczero-char0, homfree,
hodgetate-from-dr), not because of anything in the manuscript. Rerouting them is outside this task's scope (step C8),
and §5 lists them as recommendations.

### 2.2 By a field-taint run on the built top (VERIFIED)

`scratch/c8-conrad/FieldTaint.lean` is fold33-pic's script with the seeds `picRepresentableAbVar` and
`kleimanPicZeroProper954SiteQ`. It was run on this branch after `lake build ZInQKernel.OneProof.Main` (16214 jobs, ok;
`frozenTarget` uses the standard axioms). Output: `scratch/c8-conrad/fieldtaint_out.txt`, closure 304845, 16 iterations.
* Tainted fields: `kleimanPicZeroProper954SiteQ`, `kleimanPicZeroProper954`, `picRepresentableAbVar`, `picZeroAbVar`,
  `phiAmpleIsogeny`, `weilPairingMumford`, `t09SymmIsogenyExists`, `poincareComplement`, `t8`,
  `hodgeTateDecompAbVar`, `r10`.
* Terminal consumers (not bundle maps):
  * `HDec.HSyn.gluePieces_of_open4_hf_pz_eb` uses `OpenAddedLeaves4PZ.t09SymmIsogenyExists`. Its only occurrence is
    `detTate_of_leaves4_pz l.t09SymmIsogenyExists …` (EichlerBoundCopy L2704). This is **(i) C8**.
  * `HDec.HSyn.glueOutputs_of_leaves3_hf_pz_eb` uses `TextbookLeavesHFPZ.t8`. This is **(ii) Poincaré**.
  * `HDec.G0Galois.g8_g12_of_leaves3_hf_pz_eb`, `G0AssembleMod.afterG7_of3_hf_pz_eb` and `gluePieces_of_open4_hf_pz_eb`
    use `r10`, which the edge `researchLeaves5_of_open7_pz_eb : r10 ← hodgeTateDecompAbVar` fills (EichlerBoundCopy
    L2423: `r10 := HodgeLF7.r10 (deRhamComparisonHT_of_leavesT r.hodgeTateDecompAbVar …)`). This is **(iii)**:
    R10, the de Rham comparison with its weights `0, −1` of multiplicity `g`, feeding G9 (C3) and G11.

So the three consumers are confirmed in the built tree. Removing (i) leaves the two rows tainted through (ii) and (iii).
The Conrad route itself reads `r.r10` (to get the weights `{0, −1}` of `r`, exactly as the existing G9 step does). It
therefore still depends on (iii), like every route through C3.

## 3. The Lean statements (`ZInQKernel/Contrib/OneProof/C8Conrad.lean`, namespace `HDec.G0Galois.C8Conrad`)

### 3.1 Objects

All objects are genuine definitions already in the tree; none is invented for the leaf:
* `G_{ℚ_p}` is `PkgI4.GQp p`;
* the Hodge–Tate multiplicities are `PkgI4.htMult` and `PkgI4.HasHTWeights` (the consumer's own definitions; the
  cyclotomic character has weight `−1`);
* `G_ℚ`, `decomp`, `GaloisChar` are `PkgI4`'s;
* the local Artin map is Tau Ceti's absolute local Artin map
  `TauCeti.ClassFieldTheory.artinMap ℚ_[p] : ℚ_[p]ˣ →* Field.absoluteGaloisGroupAbelianization ℚ_[p]`
  (vendored, `ZInQKernel/Contrib/TauCeti/NumberTheory/ClassFieldTheory/Local/ArtinMap.lean`). It is arithmetically
  normalized: `χ_cyc(Art(pᵏu)) = u⁻¹` (`abelianizedLocalCyclotomicCharacter_artinMap_padic`), which matches the
  "arithmetic-Artin normalization" the audit reports right after Conrad's Def. B.1. It is already used by
  `ZInQ.Contrib.localKroneckerWeber` (leaf T16, proved).

New definitions:
* `IsArtinLift p σ x`: the class of `σ` in `G_{ℚ_p}^{ab}` is `artinMap ℚ_[p] x`;
* `IsLocallyAlgebraic p ψ n`: for some `k`, `ψ(σ) = u^n` for every unit `u ≡ 1 mod pᵏ` and every Artin lift `σ` of
  `u`. This is Conrad's Def. B.1 for base field `ℚ_p`, where the algebraic characters of `𝔾_m` are `x ↦ xⁿ` (the
  audit's reading). The open subgroups `1 + pᵏℤ_p` are cofinal among open subgroups of `ℤ_p^×`.

### 3.2 The new leaf

| name | statement (Lean) | source | rating |
|---|---|---|---|
| `ConradAppBQp` | for every prime `p`, every finite `E/ℚ_p` inside `ℚ̄_p` and every `ψ : G_{ℚ_p} →* Eˣ` that is continuous (into `ℚ̄_p`) and has `HasHTWeights p (charRep ψ) {w}` for some `w`: `∃ n, IsLocallyAlgebraic p ψ n` | Conrad, *Lifting global representations with local properties*, author preprint Dec. 11, 2011, App. B, pp. 32-33, paragraph after Def. B.1 (as reported by the audit; **unread here**), base field `L = ℚ_p` | **printed form for `L = ℚ_p` (a direct instance), flagged unread; not a LEAF by the strict definition because the source is an unrefereed preprint.** One dictionary step separates it from the print: the hypothesis `HasHTWeights … {w}` says `dim_{ℚ_p} H_{−w} ≥ [E:ℚ_p]`, which implies that the underlying `ℚ_p`-representation is Hodge–Tate by the Serre–Tate bound `Σᵢ dim Hᵢ ≤ [E:ℚ_p]` (Tate 1967 §3.3, STANDARD). So read strictly it is a consequence of the print (GLUE). The refereed sources the project's notes name for the same content are Serre 1968 Ch. III App. and Tate 1967 §3.3 (h-trust §2.4, rv-h-c8 §4); the rule against swapping in a different source applies only to a known defect, and none exists. |

### 3.3 The glue (each a `def … : Prop` with a docstring naming its step)

| name | content | step / source | status |
|---|---|---|---|
| `TwistCharHT0` | if `r` has weights `{0, −1}` at 5 and is attached up to `ψ` to a weight-2 normalized eigenform, then `ψ` is unramified outside a finite set, and `ψ|G_{ℚ₅}` takes values in a finite `E/ℚ₅` and has `HasHTWeights {0}` (inputs R14 `EigenformRepExists` and R13 `EigenformHT` as hypotheses) | N5 L758-760 and the weight comparison L765-766. Plan (A), for semisimple `r`: `AttachedConj` (proved, TailS §13) gives `r ≅ ψ ⊗ ρ_g`; then `HTCharOfTwist` (TailS GLUE S1, unproved), `HTTwistShift`, `HTWeightsUnique` (proved). Plan (B), with no semisimplicity, so true as stated: `det r = ε_g χ ψ²` (R14's determinant clause and Chebotarev, as in `g12Det_of`), so `ψ²` and hence `ψ` have Sen weight 0, and a character with Sen operator 0 is Hodge–Tate of weight 0 (Sen 1980). Both plans use Baire for the finite coefficient field. | GLUE, unproved. Plan (B)'s unramifiedness step is **on-the-spot**: `ψ²` is unramified almost everywhere, and `ψ` modulo an open torsion-free pro-5 `U ⊂ O_E^×` has open kernel, so `ψ(I_q) ⊂ {±1}` is trivial for almost all `q`. |
| `LocAlgExponentEqWeight` | the exponent of a locally algebraic character of `G_{ℚ_p}` is its Hodge–Tate weight | N5 L763-764 ("removing its integral local Hodge–Tate weight"); STANDARD (Serre 1968 Ch. III App.; Tate 1967 §3.3) | GLUE, unproved. **On-the-spot sketch:** if `ψ(Art u) = uⁿ` on `1 + pᵏℤ_p`, then `φ = ψ·χ_cycⁿ` is trivial on an open subgroup of the inertia of `G_{ℚ_p}^{ab}` (the closure of `Art(ℤ_p^×)`, local class field theory), so `φ` is a finite character times an unramified one, and both have Hodge–Tate weight `0` (Ax–Sen–Tate with Hilbert 90). So `ψ = φ·χ^{−n}` has weight `n`, and a Hodge–Tate character has one weight. |
| `FiniteOfLocAlgTrivialQ` | a continuous `ψ : G_ℚ → ℚ̄_p^×`, unramified outside a finite set and trivial on the Artin lifts (through `decomp`) of the units `1 + pᵏℤ_p`, has finite image | N5 L761-765 ("class field theory over ℚ … finite inertia at five and at every other prime, hence a finite ray-class character") | GLUE, unproved. Plan: Kronecker–Weber (proved, `ZInQKernel/Contrib/KroneckerWeber`) gives `G_ℚ^{ab} ≅ ℤ̂^×`; Tau Ceti's `localArtinMap_cyclotomic_padic_primePow` handles `q = p`; at `q ≠ p`, the image of the virtually pro-`q` group `ℤ_q^×` in the virtually pro-`p` group `O_E^×` is finite (rv-h-c8 §4 item 3; **on-the-spot**, elementary, not stated in N5). |
| `C8TwistFinite` | C8's conclusion: the twist `ψ` has finite image | N5 L758-766 | proved from the above (§4) |

## 4. Lean results (VERIFIED)

`ZInQKernel/Contrib/OneProof/C8Conrad.lean` (= `scratch/c8-conrad/C8Conrad.lean`) imports
`ZInQKernel.OneProof.H.PicZeroCharZeroCopy`, the module that declares the consumer `G12DetPZ`. It does not import
`OneProof.Main`.
* `lake build ZInQKernel.Contrib.OneProof.C8Conrad`: ok, no errors or warnings in the file.
* `#print axioms` (`scratch/c8-conrad/axioms_out.txt`): `c8TwistFinite_of_conrad`, `g12DetPZ_of_twistFinite`,
  `g12DetPZ_of_conrad` use only `[propext, Classical.choice, Quot.sound]`.

| theorem | statement |
|---|---|
| `c8TwistFinite_of_conrad` | `EigenformRepExists → PkgI4.EigenformHT → ConradAppBQp → TwistCharHT0 → LocAlgExponentEqWeight → FiniteOfLocAlgTrivialQ → C8TwistFinite` |
| `g12DetPZ_of_twistFinite` | `C8TwistFinite → G9GlueNoT23 → PkgI4.DeRhamComparison → HDec.G0Galois.G12DetPZ` |
| `g12DetPZ_of_conrad` | the composite: `G12DetPZ` from Conrad App. B, the three glue Props and the chain's R13, R14, R10, G9 |

**Observation (VERIFIED by the proof of `g12DetPZ_of_twistFinite`).** `G12DetPZ` asserts only the existence of `H`,
`det r`, `ε`, `χ_cyc` with the determinant identities. Once `ψ` has finite image, `H = ker ψ`, `det r := ψ²` and
`ε = χ_cyc := 1` satisfy it. So the consumer is equivalent, under its hypotheses, to the finiteness of the twist, and
the Weil pairing enters C8 only to prove that finiteness.

`#discharges` (`scratch/c8-conrad/Discharges.lean`, output `discharges_out.txt`): 36 open hypotheses, 15748 theorems
checked, 19 discharge one. **None of them is in `C8Conrad`**: as expected, no open hypothesis is discharged (§5).

## 5. Fold: none proposed (dry-run reasoning; SPECULATIVE counts, VERIFIED premises)

* **No bundle field is discharged.** `G12DetPZ` and `DetTate` are not hypotheses of `frozenTarget`. They are proved
  inside the chain from `t09SymmIsogenyExists`, which comes from the two Picard rows. `#discharges` on the new file
  lists none of the open hypotheses (§4), so `autofold.py` has no field to remove, and `scratch/c8-conrad/autofold.json`
  records this (`"fields": []`, with the would-be new leaf and glue for reference).
* **What a reroute would do.** It would be a copy reroute, not an autofold:
  * in a copy of `HDec.G0Galois.g8_g12_of_leaves3_hf_pz_eb` (EichlerBoundCopy L2473-2486), replace
    `(g12Det_of_pz m.r14det m.detTate m.finIndex (frobeniusDenseQ_of t.frobeniusDense))` by
    `(C8Conrad.g12DetPZ_of_conrad r.r14 r.r13 hC hT hW hF h9 r.r10)`. Every input is already at that call site
    (`r.r14 : EigenformRepExists`, `r.r13 : PkgI4.EigenformHT`, `r.r10 : PkgI4.DeRhamComparison`, `h9`);
  * use a copy of `GaloisPieces` without `detTate`;
  * re-copy the generations up to the top, as fold-kleiman2's generator does.
* **Effect on the counts.** Both Picard rows stay, because consumers (ii) and (iii) still read them. So the reroute
  would **add** `ConradAppBQp` (unrefereed, GLUE by the strict reading) and the three glue Props, and remove nothing:
  H would go from 31 to at most 35 hypotheses. The reroute pays only together with reroutes of (ii) and (iii).
* **What would take the rows off the route** (recommendations, SPECULATIVE; outside this task's scope):
  1. **C8:** this file;
  2. **E1-E2 (Poincaré reducibility, manuscript L865):** restore `AVB1.PoincareComplement` as a printed textbook leaf
     (Mumford, *Abelian varieties*, §19 Thm 1, p. 173, UNVERIFIED), instead of proving it from `PicZeroAbVar0`
     (piczero-char0's `poincareComplement_of_open0`). The manuscript names the theorem without a citation;
  3. **C3/G9 (multiplicities, lemma `lem:de-rham-descent`, L10940-11006):** state the multiplicities `g`, `g` in the
     printed Hodge–Tate decomposition (Faltings 1988 Ch. III Thm 4.1, cited at L11003; or Tate 1967 for good
     reduction) as a leaf over `Lie A` and `Lie A^∨`, instead of getting `a = b` from the Weil pairing
     (hodgetate-from-dr). This needs `dim A^∨ = g`, which is the Picard theory again unless the leaf states it.

  Only if all three are rerouted do `picRepresentableAbVar` and `kleimanPicZeroProper954SiteQ` leave the route:
  −2 GLUE, +1 to +3 leaves, +3 glue from C8. Even then the net strict count does not improve unless the C8 glue is
  proved. This is why the task's target is not met.

## 6. Known issues and limitations

* **Known issues: none about Conrad App. B or about the manuscript's use of it** (§1.1). The task's stop condition
  ("a defect recorded in h-trust C8 or a review") does not hold.
* **The task's target is not reachable through C8** (§2). This is the main result. Both rows have two further live
  consumers outside C8: Poincaré reducibility (E1-E2) and R10/`hodgeTateDecompAbVar` (C3/G9). The manuscript does not
  use the Picard scheme at either step. Retargeting them would leave step C8 and needs separate tasks (§5
  recommendations 2-3), so this task stops there.
* **Source unread.** Conrad's App. B was not read on this host (fetch refused). The leaf's wording follows the
  theorem-application audit's report and carries the flag unread. A reader should check the paragraph after
  Def. B.1, pp. 32-33, against `ConradAppBQp` and `IsLocallyAlgebraic`:
  * the form of the definition (open subgroup of `O_L^×`, algebraic character `∏_τ τ(x)^{n_τ}`);
  * the coefficient field;
  * the Artin normalization;
  * whether the weights are tied to the exponents, which would let `LocAlgExponentEqWeight` be read off the print.
* **Unrefereed source.** Conrad's paper is an author preprint. (An earlier version of this note said the project's LEAF
  definition requires a published, refereed theorem, citing h-leaves L581 and h-v14 L567; neither line says that, and it
  is not a rule, so the claim is withdrawn, 11-17.) The strict leaf review (queue28, 11-17) rates `ConradAppBQp`
  GLUE/GLUE for two unproved bridges, not for the source's status: see the leaf's flag in scratch/c8-conrad3/autofold.json.
  The refereed statements the project's notes name for the same content are Serre 1968 Ch. III App. and Tate 1967 §3.3.
  Switching to them would leave the manuscript's citation. The rules allow that only for a known defect, so it is
  recorded here as an option, not taken.
* **On-the-spot steps** (not in the manuscript or a cited print; sketches in the docstrings and in §3.3):
  * the finiteness of `ψ` on inertia at `q ≠ 5` (inside `FiniteOfLocAlgTrivialQ`; rv-h-c8 §4 item 3, elementary);
  * the weight–exponent dictionary `LocAlgExponentEqWeight`, unless Conrad's paragraph prints it;
  * plan (B)'s unramifiedness step in `TwistCharHT0`;
  * the observation that `G12DetPZ` reduces to the finiteness of `ψ` (proved in Lean, so not a gap).
* **Unchanged.** No consumer's statement changed. No file under `ZInQKernel/` other than the new
  `Contrib/OneProof/C8Conrad.lean` was edited. No fold was run (§5).

# c8-conrad3: the three open glue Props of the C8 reroute, proved

Task c8-conrad3, 2026-11-17. Base: wip/c8-conrad2 `5938de123` with origin/main `b1615c9b1` merged (igusa-drop's fold:
`TailZ79`, `sixContactMin_of_open72`). Results log: `scratch/c8-conrad3/log.md`. This is model work; nobody has
reviewed it.

**VERIFIED** means compiled, computed, or read in a named file on this host. **STANDARD** means published, with the
reference given. **SPECULATIVE** means not checked. Theorem numbers given from memory are marked UNVERIFIED: the host
has no network, and no page read of Tate 1967, Milne 1986 or Conrad App. B was forwarded, so those flags stay
"unread".

## 0. Main result

1. **All three open glue Props of c8-conrad2's C8 reroute are proved** (VERIFIED: compiled, `#print axioms` gives
   `[propext, Classical.choice, Quot.sound]` for each). Each theorem's type is the Prop exactly as c8-conrad2 stated
   it; the files import the module that declares it, so the statement is not copied or changed.

   | Prop (file of the statement) | theorem (file) | inputs |
   |---|---|---|
   | `TwistCharHTWt0` (C8CFT) | `HDec.G0Galois.C8Conrad.twistCharHTWt0_proof` (`C8Twist.lean`) | the Prop's own hypotheses R14 and R13; Chebotarev (T18), Tate's two theorems and hodge-split's Tate–Sen coordinates, all proved in the tree |
   | `InertiaAtPDecomp` (C8LocAlg) | `…C8Conrad.inertiaAtPDecomp_proof` (`C8Dicts.lean`) | Mathlib, Tau Ceti, `GlueB3Unram` (places of `ℚ̄`), G15's lifting lemma (copied as `C8Ladic.lean`) |
   | `MinkowskiInertiaQ` (C8CFT) | `…C8Conrad.minkowskiInertiaQ_proof` (`C8Dicts.lean`) | Mathlib's Minkowski theorem (`NumberField.exists_not_isUnramifiedAt_int_of_isGalois`), `GlueB3Unram` |

   No new cited input was needed for any of them, so no leaf was added.
2. **Step C8 now rests on two printed leaves** (VERIFIED, compiled). They are packaged as `C8Leaves`
   (`C8Printed.lean`), and `g12DetPZ_of_printed` derives C8's consumer `G12DetPZ` from them, with R13, R14, G9 and
   R10:
   * `conradAppBQp`, tagged **CITED**: the manuscript cites Conrad App. B at this step;
   * `tateTwistInvariantsInertia`, tagged **DEPARTURE**: the manuscript does not cite Tate 1967.
3. **Provenance (task part 4, VERIFIED by reading `diophantine_zq.tex`; §5):**
   * `conradAppBQp` is CITED (L760-762);
   * `tateTwistInvariantsInertia` is a DEPARTURE: Tate 1967 is not in the bibliography;
   * `poincareComplement` is ELLIOT: L864-865 name "Poincaré reducibility" and cite nothing.

   PR #86's `ZInQ.Contrib.CloudR2Poincare.poincareComplement_proof` has type `ZInQ.Contrib.AVB1.PoincareComplement`.
   That is the same constant `t8_of_poincareComplement` consumes, so it can replace the Poincaré leaf at fold time.
   Checked by reading the branch, not merged and not compiled.
4. **Hand-fold dry run over the merged top** (VERIFIED: standard axioms; `scratch/c8-conrad3/C8FoldDryRun.lean`).
   * `frozenTarget_c8` takes `hP, hC, hTT` in place of c8-conrad2's five-field `c8 : C8Inputs`.
   * The fold shape is `sixContactMin_of_open73C8 (r : OpenResearchLeaves53) (t : OpenTextbookLeaves19C8)
     (l : OpenAddedLeaves28C8)`, where `OpenAddedLeaves28C8 = OpenAddedLeaves27 + {conradAppBQp,
     tateTwistInvariantsInertia}`.
   * `#discharges`: 34 open hypotheses, 19 discharge one, none of them from the C8 files. This is expected: no
     bundle field is discharged until consumer (iii) is rerouted.
5. **Net change of the C8 part (§6).**
   * Alone, C8 adds 2 rows and 0 glue Props. c8-conrad2's version added 5 rows, 3 of them glue.
   * At the joint fold with the Hodge–Tate reroute, the two Picard rows (GLUE/GLUE) leave. With PR #86 filling
     Poincaré, the C8+Poincaré part then changes the row count by 0 and the GLUE count by **0**: the two new leaves
     count as GLUE while pending review. Once both are rated LEAF the change is **−2** (−1 if the unrefereed
     `conradAppBQp` is kept as GLUE).
   * So the target "net GLUE ≤ 0 at the joint fold" is met.

## 1. What compiles (VERIFIED)

`lake build ZInQKernel.Contrib.OneProof.C8Printed` succeeded (13413 jobs). The scratch dry run and `#discharges`
ran with `lake env lean`. No file imports `ZInQKernel.OneProof.Main`. The only edits under `ZInQKernel/` are the four
new files below in `Contrib/OneProof/`.

| file | content |
|---|---|
| `Contrib/OneProof/C8Ladic.lean` | verbatim copy of G15 `LadicBridge.lean` §1, §2, `jField`, §5 and `decomp_spec` (namespace `HDec.G0Galois.C8Conrad.Ladic`); the original cannot be imported next to the chain: `import ZInQKernel.Contrib.Different.Local failed, environment already contains 'PkgI6.TraceContainsRamificationIdx' from ZInQKernel.HDecomp.Textbook.Different` (VERIFIED) |
| `Contrib/OneProof/C8Dicts.lean` | `MinkDict.exists_place_over`, `exists_inertia_lift`, `fixed_conj`, `minkowskiInertiaQ_proof`; `DecDict.inertia_fix_root`, `exists_conj`, `inertiaAtPDecomp_proof`; provider names `minkowskiInertiaQ_proof`, `inertiaAtPDecomp_proof` |
| `Contrib/OneProof/C8Twist.lean` | `TwistHT.trace_eq_of_attached`, `det_eq_of_trace_eq`, `continuous_cpAct_orbit`, `finrank_Ysp_le`, `linIndep_two`, `exists_sqrt_twist`, `hasHTWeights_zero_of_twist`, `exists_galois_values`, `exists_det_vector`, `twistCharHTWt0_proof`; provider name `twistCharHTWt0_proof` |
| `Contrib/OneProof/C8Printed.lean` | `C8Leaves`, `c8Inputs_of_leaves : C8Leaves → C8Inputs`, `c8TwistFinite_of_printed`, `g12DetPZ_of_printed` |
| `scratch/c8-conrad3/C8FoldDryRun.lean` | c8-conrad2's generated copy (unchanged), `sixContactMin_of_open72_c8`, `ZInQ.OneProof.frozenTarget_c8`, the fold shape `sixContactMin_of_open73C8`; output `dryrun_out.txt` |
| `scratch/c8-conrad3/Discharges.lean` | `#discharges` with all eight C8 files; output `discharges_out.txt` |
| `scratch/c8-conrad3/C8DryRunTaint.lean` | field-taint run from `frozenTarget_c8` (c8-conrad2's metaprogram); output `dryrun_taint_out.txt` (§6) |
| `scratch/c8-conrad3/C8Mink.lean`, `C8Dec.lean`, `C8Twist.lean` | the scratch versions the Contrib files were assembled from (each with `#print axioms`) |

`#print axioms` gives `[propext, Classical.choice, Quot.sound]` for every one of these theorems:
* `twistCharHTWt0_proof`, `inertiaAtPDecomp_proof`, `minkowskiInertiaQ_proof`;
* `c8Inputs_of_leaves`, `c8TwistFinite_of_printed`, `g12DetPZ_of_printed`, `Ladic.exists_lift`;
* the dry-run tops `frozenTarget_c8`, `sixContactMin_of_open72_c8` and `sixContactMin_of_open73C8`.

## 2. `TwistCharHTWt0` (task part 1; on-the-spot, see §7)

The statement, unchanged from C8CFT L488:
* hypotheses: R14 and R13; a 2-dimensional `r : G_ℚ → GL₂(ℚ̄₅)` with Hodge–Tate weights `{0, −1}` at 5; `r`
  attached up to the twist `ψ` to a normalized weight-2 eigenform `g`;
* conclusion: `ψ|_{G_{ℚ₅}}` takes values in a finite `E/ℚ₅` and `HasHTWeights 5 (charRep ψE) {0}`.

**Proof (VERIFIED, compiled).**
1. **Global identities.**
   * R14 gives a semisimple `ρ_g` attached to `g`, and R13 gives it the weights `{0, −1}` (with `k = 2`).
   * Chebotarev (the kernel's T18, `ZInQ.Contrib.frobeniusDense`, through `C9Rhof.eq_of_eq_on_arithFrob`) extends
     the Frobenius-trace identity to `tr r(σ) = ψ(σ) tr ρ_g(σ)` for all `σ ∈ G_ℚ`.
   * From `2 det M = (tr M)² − tr(M²)` for `2 × 2` matrices, applied at `σ` and `σ²`: `det r = ψ² det ρ_g`.
   * **No semisimplicity of `r` is used.** This is what c8-conrad2 found missing in the tree's twist machinery,
     which needs an exact twist `r = ψ ⊗ ρ_g`.
2. **Values in a finite field, without Baire.**
   * `tr ρ_g ≠ 0` on an open normal subgroup `G_M` of `G_{ℚ₅}`; there `ψ = tr r / tr ρ_g ∈ E₀`, the field of the
     entries.
   * At the finitely many coset representatives of `G_M`, `ψ` takes finitely many algebraic values.
   * So all values of `ψ|_{G_{ℚ₅}}` lie in a finite Galois `E` (`exists_galois_values`).
3. **Determinants in Tate–Sen coordinates.**
   * Over `G_E`, with hodge-split's spaces `Y_i(ρ) = {y ∈ ℂ_p² : ρ(σ)ᵀ y = χ(σ)^i σ(y)}` and
     `htMult = dim_E Y_{−w}` (`htMult_eq_finrank_Ysp`, from Tate's two theorems, proved in the tree):
     weights `{0, −1}` give nonzero `y₀ ∈ Y_0`, `y₁ ∈ Y_1`.
   * They are `ℂ_p`-independent (`Ysp_linearIndependent`), so `d = det(y₀, y₁) ≠ 0`.
   * The four component equations give `d · det ρ(σ) = χ(σ) σ(d)` (`exists_det_vector`).
   * For `r` and `ρ_g`: `y = d_r / d_g ≠ 0` satisfies `σ(y) = ψ(σ)² y` on `G_E`.
4. **Square root.**
   * `ℂ_p` is algebraically closed (Mathlib `PadicComplex.isAlgClosed`). A square root `c` of `y` has
     `σ(c) = ±ψ(σ) c` on `G_E`.
   * The orbit map `σ ↦ σ(c)` is continuous (`continuous_cpAct_orbit`: approximate `c` by `a ∈ ℚ̄_p`, whose
     stabilizer is open; `G_{ℚ_p}` acts isometrically).
   * So `{σ ∈ G_E : σ(c) ≠ −ψ(σ) c}` is open and contains 1. It contains `G_{E'}` for a finite Galois `E' ⊇ E`, on
     which `σ(c) = ψ(σ) c`.
5. **Weight 0.**
   * `c ∈ Y_0(ψ_{E'})`, so `dim Y_0 ≥ 1`. Tate–Sen independence gives `dim Y_i ≤ 1` (`finrank_Ysp_le`), and
     `Y_i = 0` for `i ≠ 0`: a nonzero vector there and `c` would be two `ℂ_p`-independent vectors in `ℂ_p¹`.
   * Hence `htMult 0 = 1` and `htMult w = 0` for `w ≠ 0`, i.e. `HasHTWeights 5 (charRep ψE') {0}`
     (`hasHTWeights_zero_of_twist`).

**No new cited input.** The manuscript's own route, "a de Rham subrepresentation of the Hom representation", would
use the closure of de Rham representations under Hom and subquotients. That closure is in Brinon–Conrad (Thm 5.2.1,
Prop. 6.3.3, which the manuscript cites at L10975 for a different step). The proof above does not use it.

## 3. `InertiaAtPDecomp` (task part 2; dictionary glue, STANDARD)

The statement (C8LocAlg L173): every element of an inertia group of a place `v` of `ℚ̄` over `p` is conjugate in `G_ℚ`
to `decomp(σ)` with `σ` in Tau Ceti's inertia subgroup of `G_{ℚ_p}` (the fixing group of `ℚ_p^{ur}`).

**Proof (VERIFIED, compiled).**
1. `PkgI4.decomp` is restriction along an embedding `jQ : ℚ̄ → ℚ̄_p` (G15's `decomp_spec`). Let
   `v₀ = {x : ‖jQ x‖ ≤ 1}`, the valuation subring of the valuation `x ↦ ‖jQ x‖`; it lies over `p`.
2. `v = g • v₀` for some `g ∈ G_ℚ` (`exists_conj`). This is the proof of `GlueB3Unram.leafConj`:
   * `GlueB3Unram.exists_smul_eq`, Mathlib's profinite transitivity on the primes of the algebraic integers, makes
     the centers conjugate;
   * `GlueB3Unram.le_of_center` shows that the center determines the place.

   Then `τ' = g⁻¹ τ g ∈ I_{v₀}` (`GlueB3Unram.inertia_conj`).
3. **Lifting to `G_{ℚ_p}`.**
   * For every finite Galois `K ⊆ ℚ̄`, `τ'|_K` stabilizes the prime `{x ∈ 𝓞_K : ‖jQ x‖ < 1}`, since `τ'` preserves
     `v₀`.
   * So it lifts to some `σ_K ∈ G_{ℚ_p}` with `jQ ∘ τ' = σ_K ∘ jQ` on `K`. This is G15's `exists_lift`, from Tau
     Ceti's `exists_algEquiv_apply_eq_of_norm_apply_eq`.
   * The sets `{σ : decomp(σ) = τ'` on a finite set`}` are closed and have the finite intersection property. By
     compactness of `G_{ℚ_p}` (`IsCompact.inter_iInter_nonempty`) some `σ` has `decomp σ = τ'`.
4. **`σ` is inertial.**
   * By Tau Ceti's `mem_inertiaSubgroup_iff_pow_natCard_pow_eq_self` and `Padic.natCard_residueField`, it suffices
     that `σ` fixes every root of `X^{p^f} − X`.
   * Such a root is `jQ(ζ)` with `ζ^{p^f−1} = 1` (primitive roots map to primitive roots).
   * `τ'` fixes `ζ`: inertia acts trivially on the residue field, and roots of unity of order prime to `p` stay
     distinct there (`inertia_fix_root`, the core of `GlueB3Unram.cycUnram`). Hence `σ(jQ ζ) = jQ(τ' ζ) = jQ ζ`.
5. So `τ = g · decomp(σ) · g⁻¹`.

## 4. `MinkowskiInertiaQ` (task part 3; dictionary glue over Mathlib, STANDARD)

The statement (C8CFT L192): an algebraic number fixed by every inertia group of every place of `ℚ̄` over a prime is
rational.

**Proof (VERIFIED, compiled).**
1. Let `F` be the normal closure of `ℚ(x)`. Every conjugate `g x` is fixed by every inertia group, since
   `g⁻¹ I_w g = I_{g⁻¹ w}` (`fixed_conj`). Hence `F` is fixed pointwise (`normalClosure_def''`).
2. If `[F : ℚ] > 1`, Mathlib's `NumberField.exists_not_isUnramifiedAt_int_of_isGalois` gives a prime `p` at which
   every prime of `𝓞_F` above `p` is ramified. Take such a prime `P`: the center in `𝓞_F` of a place of `ℚ̄` over `p`
   (`exists_place_over`, Mathlib's `Ideal.image_subset_nonunits_valuationSubring`).
3. **Inertia lifts** (`exists_inertia_lift`). Every `σ ∈ I(P) ⊆ Gal(F/ℚ)` is the restriction of an element of the
   inertia group of some place `w` of `ℚ̄` over `p`. The proof follows `GlueB3Unram.exists_inertia_neg`:
   * lying-over gives `Q ⊂ B` over `P`, and transitivity moves a place onto `Q`;
   * a lift `g'` of `σ` is corrected by Mathlib's profinite transitivity and
     `Ideal.Quotient.stabilizerHom_surjective_of_profinite` for `G_F` acting on `B` over `A = B^{G_F}`;
   * `GlueB3Unram.mem_inertia_of_center` then puts the corrected element in `I_w`.
4. Lifted elements fix `F`, so `I(P) = 1`.
   * Then `e(P|p) = #I(P) = 1` (`Ideal.card_inertia_eq_ramificationIdxIn`).
   * So `P` is unramified (`Ideal.ramificationIdx_eq_one_iff`), a contradiction. Hence `F = ℚ` and `x ∈ ℚ`.

## 5. Provenance of the leaves (task part 4; VERIFIED by reading `diophantine_zq.tex`)

| leaf | tag | evidence |
|---|---|---|
| `conradAppBQp` (Conrad App. B, base field `ℚ_p`) | **(b) CITED** | L760-762, paraphrased: local algebraicity "[Appendix B, pp. 32-33]{conrad-local-characters}" and class field theory over `ℚ` give a finite character times a cyclotomic power. Bibitem L11046-11049: Conrad, *Lifting global representations with local properties*, author preprint, Dec. 11, 2011, App. B, pp. 32-33. Flags: unread on host; unrefereed preprint. |
| `tateTwistInvariantsInertia` (Tate 1967 §3.3 Thm 2 over `\hat{K^{ur}}`) | **(c) DEPARTURE** | No Tate "p-divisible groups" (Driebergen 1966) entry in the bibliography (grep, none). The step it proves, L763-764 ("removing its integral local Hodge–Tate weight"), cites nothing beyond the Conrad citation of the same sentence. Locator UNVERIFIED, unread. |
| `poincareComplement` (Milne 1986 Prop. 12.1 form) | **(a) ELLIOT** | L864-865, paraphrased: absolute simplicity and Poincaré reducibility give an `L'`-isogeny `A × Z → J`. The manuscript names the theorem and cites nothing. Locator UNVERIFIED, unread. |

Two remarks on the leaves:
* **Possible sources inside the bibliography** (not adopted: no page read is available).
  * Brinon–Conrad's CMI notes (bibitem `brinon-conrad`, L11019-11023, cited at L10975 and L10994 for other steps)
    prove Tate's theorem `H⁰(G_K, ℂ_K(n)) = 0` for complete discretely valued `K` of characteristic 0 with perfect
    residue field. That covers `\hat{K^{ur}}`; locator from memory, UNVERIFIED: Thm 2.2.7. With it,
    `tateTwistInvariantsInertia` would be a source the manuscript cites, though still not for this step.
  * Milne's notes v2.00 (bibitem `milne-av`, L11024-11026) are cited at L564 (Part I, Thms 2.8-2.9) and L10968
    ("Part I, Theorem 12.1(a)", the étale-cohomology duality `V_ℓ(A) ≅ H¹_et(A, ℚ_ℓ)^∨`), not for Poincaré
    reducibility. The number "12.1" means different results in the 1986 article and the v2.00 notes. The PR #86
    proof makes the Poincaré leaf unnecessary anyway.
* **PR #86** (branch `proof/poincare-complement-native-20261117`, commit `6984d6078`; read with `git show`, not
  merged).
  * `ZInQKernel/Contrib/CloudR2Poincare/FinalUnconditional.lean:24` declares
    `theorem poincareComplement_proof : ZInQ.Contrib.AVB1.PoincareComplement`.
  * `ZInQKernel/Contrib/AVB1/Poincare.lean` is unchanged on that branch (`git diff HEAD...branch --
    ZInQKernel/Contrib/AVB1/` is empty).
  * `HSyn.t8_of_poincareComplement` takes `hP : _root_.ZInQ.Contrib.AVB1.PoincareComplement`. **The statements
    match** (same constant, `k : Type`, no universe issue).

## 6. Hand-fold spec, dry run, counts (task part 5)

`scratch/c8-conrad3/autofold.json` (`"discharges": []`, section `handfold`) replaces c8-conrad2's spec.
1. **Copy.** c8-conrad2's generated copy (70 blocks) and the C8 and t8 swaps are unchanged.
2. **New top.** `sixContactMin_of_open72_c8` copies igusa-drop's new top `sixContactMin_of_open72` (TailZ79), with
   `sixContactMin_of_open48_eb_k954_c8 … hP c8`.
3. **C8 inputs from the leaves.** The field `c8 : C8Inputs` of the copied bundles is filled at the top by
   `C8Conrad.c8Inputs_of_leaves ⟨conradAppBQp, tateTwistInvariantsInertia⟩`. The three glue fields are theorems.
4. **New generations.**
   * `OpenTextbookLeaves19C8 = {poincareComplement}`, to be filled at fold time by PR #86's
     `poincareComplement_proof`, which leaves it empty.
   * `OpenAddedLeaves28C8 = OpenAddedLeaves27 + {conradAppBQp, tateTwistInvariantsInertia}`.
   * Top: `sixContactMin_of_open73C8`.
5. **Dry run** (`C8FoldDryRun.lean`, `dryrun_out.txt`): every top has standard axioms. `frozenTarget_c8` is the copy
   of `ZInQ.OneProof.frozenTarget` (origin/main `b1615c9b1`), with `hP`, `hC`, `hTT` added.
6. **`#discharges`** (`discharges_out.txt`): 34 open hypotheses, 16233 theorems checked, 19 discharge one, none
   from the C8 files (expected).
7. **Field taint** from `frozenTarget_c8` (`dryrun_taint_out.txt`; VERIFIED): closure 304467, 18 iterations.
   * Tainted fields: `picRepresentableAbVar`, `kleimanPicZeroProper954SiteQ`, `kleimanPicZeroProper954`,
     `picZeroAbVar`, `hodgeTateDecompAbVar`, `r10`. These are exactly c8-conrad2's.
   * Terminal readers: `g8_g12_of_leaves3_hf_pz_eb_c8`, `afterG7_of3_hf_pz_eb_c8`, `gluePieces_of_open4_hf_pz_eb_c8`,
     each through `r10`.
   * So the Picard rows reach only consumer (iii) over the merged top. `t09SymmIsogenyExists`, `phiAmpleIsogeny`,
     `weilPairingMumford`, `poincareComplement` and `t8` are not tainted.

**Net row and GLUE change of the C8 part** (kinds.tsv convention: a new printed leaf counts GLUE/GLUE until a reviewer
rates it; both Picard rows are GLUE/GLUE):

| | rows | GLUE (strict/strictest) |
|---|---|---|
| C8 part alone (c8-conrad2) | +5 (2 leaves + 3 glue) | +5 |
| C8 part alone (now) | **+2** (2 leaves, 0 glue) | **+2** pending review, **0** once rated |
| Poincaré part | +0 with PR #86 (+1 ELLIOT leaf without it) | +0 (+1 pending review) |
| joint fold with the Hodge–Tate reroute: Picard rows leave | −2 | −2 |
| **C8 + Poincaré at the joint fold, with PR #86** | **0** | **0** pending review; **−2** once both leaves are rated LEAF (−1 if the unrefereed `conradAppBQp` stays GLUE) |

Alone, before consumer (iii) is rerouted, the fold would add 2 rows and 2 pending GLUE, so `autofold.py` would refuse
it without `--allow-rise`. **Do not fold alone.** The remaining consumer of the Picard rows is (iii) only:
`openResearchLeaves35_of_OpenResearchLeaves36_eb_k954_cf … l26`, `hodgeTateDecompAbVar → r10`
(c8-conrad2 §2; rerun over the merged top, item 7 above).

## 7. On-the-spot steps (neither in the manuscript nor in a cited print)

* **`TwistCharHTWt0`** (N5 L758-760, "the twisting character is a de Rham subrepresentation of the Hom
  representation"; the Hodge–Tate half). Proved here; the full proof is §2.

  Sketch: Chebotarev turns the Frobenius-trace identity into `tr r = ψ tr ρ_g` on all of `G_ℚ`, hence
  `det r = ψ² det ρ_g` by `2 det = tr² − tr(·²)`. Both `r` and `ρ_g` have Hodge–Tate weights `{0, −1}`. So in Tate–Sen
  coordinates over a finite Galois `E` containing all values, the determinant of a basis of `Y_0 ⊕ Y_1` gives
  `d ≠ 0` with `d · det(σ) = χ(σ) σ(d)`, and the quotient for `r` and `ρ_g` gives `y ≠ 0` with `σ(y) = ψ(σ)² y`.
  A square root `c` of `y` in `ℂ_p` has `σ(c) = ±ψ(σ) c`. The sign is a continuous function of `σ` (orbit maps are
  continuous), so `σ(c) = ψ(σ) c` on an open subgroup `G_{E'}`. Hence `ℂ_p(ψ) ≅ ℂ_p` over `E'`, and Tate–Sen
  independence makes `0` the only weight.

  It does not follow the manuscript's wording: it uses the determinant rather than the Hom representation. It needs
  no semisimplicity and no input beyond the tree's proved Tate theorems and Chebotarev.
* **The two dictionaries** (§3, §4): standard facts on places of `ℚ̄`, proved from Mathlib and Tau Ceti.
* **The finite coefficient field of `ψ|_{G_{ℚ₅}}`** (§2 step 2): an open-subgroup argument replaces Baire.

## 8. Known issues and limitations

* **No issue found in the manuscript's use of a cited source at C8.**
  * The manuscript's "de Rham subrepresentation of the Hom representation" (L758-759) holds as stated, since `ρ_g`
    is semisimple. If `r` is reducible, `ψ ⊗ ρ_g ≅ r^{ss}`, and a sub-line `α` of `r` gives
    `ψ ↪ Hom(ψ⁻¹α, r) ⊆ Hom(ρ_g, r)` (SPECULATIVE, a one-line check, not formalized). The proof here does not
    need it.
  * The Conrad citation (L761) is an unrefereed author preprint, unread on this host (c8-conrad §6).
* **Locators unread** (no page reads arrived; flags kept): Tate 1967 §3.3 Thm 2; Milne 1986 Prop. 12.1; Conrad App. B
  pp. 32-33; Brinon–Conrad Thm 2.2.7 (mentioned only as a possible bibliography source, from memory).
* **`tateTwistInvariantsInertia` remains a DEPARTURE.** If Conrad's App. B paragraph (cited) states that the exponent
  of a locally algebraic character is its Hodge–Tate weight, then `LocAlgExponentEqWeight` can be read off the cited
  print. The Tate leaf would then go (c8-conrad §6, c8-conrad2 §8). Not checked: the page is unread.
* **PR #86 checked by reading only.** The branch was not merged (as instructed) and its theorem was not compiled
  here.
* **The dry run is not a fold.** The generated copy lives in `scratch/`. No consumer statement was changed: the swaps
  replace terms, not types.

## 9. Files

* New: `ZInQKernel/Contrib/OneProof/C8Ladic.lean`, `C8Dicts.lean`, `C8Twist.lean`, `C8Printed.lean`.
* `scratch/c8-conrad3/`:
  * `log.md`, `autofold.json`;
  * `C8FoldDryRun.lean` and `dryrun_out.txt`; `C8DryRunTaint.lean` and `dryrun_taint_out.txt`;
  * `Discharges.lean` and `discharges_out.txt`;
  * scratch proofs `C8Mink.lean`, `C8Dec.lean`, `C8Twist.lean`; probes `Test.lean`, `Test2.lean`.

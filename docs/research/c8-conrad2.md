# c8-conrad2: the Picard rows off consumers (i) C8 and (ii) Poincaré reducibility

Task c8-conrad2, 2026-11-17. Base: wip/c8-conrad `a411466b4` with origin/main `97247ce1c` merged (`cff986a75`).
Results log: `scratch/c8-conrad2/log.md`. This is model work; nothing here has been reviewed by a person.

**VERIFIED** means compiled, computed, or read in a named file on this host. **STANDARD** means published, with the
reference given. **SPECULATIVE** means not checked. Locators given from memory are marked UNVERIFIED (the host cannot
reach jmilne.org, math.stanford.edu or web.archive.org; WebFetch was refused for all three).

## 0. Main result

1. **The target is reached in a dry run (VERIFIED, compiled; §2).** In a copy reroute of the current top, the two
   Picard rows `picRepresentableAbVar` and `kleimanPicZeroProper954SiteQ` reach only consumer (iii): the field
   `hodgeTateDecompAbVar`, which fills `r10`.
   * The dry run is `scratch/c8-conrad2/C8DryRun.lean`, with the top `ZInQ.OneProof.frozenTarget_c8` (standard axioms).
     The hand-fold shape is `C8FoldDryRun.lean`, top `HDec.HSyn.sixContactMin_of_open72C8` (standard axioms).
   * A field-taint run from `frozenTarget_c8` (`dryrun_taint_out.txt`) taints only these fields:
     `kleimanPicZeroProper954SiteQ`, `kleimanPicZeroProper954`, `picRepresentableAbVar`, `picZeroAbVar`,
     `hodgeTateDecompAbVar`, `r10`. Every terminal consumer reads `r10`.
   * `t09SymmIsogenyExists`, `phiAmpleIsogeny`, `weilPairingMumford`, `poincareComplement` and `t8` are no longer
     tainted.
2. **Two of c8-conrad's three glue Props are proved (VERIFIED, compiled, standard axioms; §4):**
   * `LocAlgExponentEqWeight` ("removing its integral local Hodge–Tate weight", diophantine_zq.tex L763-764) is
     proved from one new leaf, `TateTwistInvariantsInertia`. This is Tate 1967 §3.3 Thm 2 for the completion of
     `K^{ur}`, the same theorem the tree already proves for finite `K`. The rest comes from Tau Ceti's local class
     field theory of `ℚ_p` (`locAlgExponentEqWeight_of_tateInertia`).
   * `FiniteOfLocAlgTrivialQ` ("class field theory over ℚ", L761-765) is proved from two dictionary Props:
     * `InertiaAtPDecomp`: global inertia groups are conjugate to `decomp(I_{ℚ_q})`;
     * `MinkowskiInertiaQ`: Mathlib's Minkowski theorem, read on inertia groups of places of `ℚ̄`.

     The proof is `finiteOfLocAlgTrivialQ_of_dicts`. The class field theory itself is Tau Ceti's local reciprocity
     plus Mathlib's Krull correspondence, a torsion-free open subgroup of `ℚ̄_p^×`, and the pro-`q` isometry
     argument. N5's unstated step "finite inertia at every other prime" is now a proof
     (`inertiaFiniteAwayFromP_of_decomp`).
3. **The third, `TwistCharHT0`, is not proved.** Its "unramified almost everywhere" half is no longer needed: the
   proof from the dictionaries does not use it (`FiniteOfLocAlgTrivialQNoRam`). Its Hodge–Tate half is the strictly
   weaker glue `TwistCharHTWt0`, reported **on-the-spot** with a proof sketch (§4.3).
4. **`t8` from a textbook leaf (VERIFIED, compiled; §5).** Poincaré's theorem is restored as the printed textbook
   leaf `poincareComplement : ZInQ.Contrib.AVB1.PoincareComplement`, classed **ELLIOT** (manuscript L865 cites
   nothing). `HSyn.t8_of_poincareComplement` gives the consumer's `t8 : PkgI3.PoincareReducibility` from it, with
   every other input proved.
5. **No bundle field is discharged** (`#discharges`, §6), as expected: the rows stay hypotheses of `frozenTarget`
   until consumer (iii) is rerouted. That is task derham-scholze's; §7 says what it needs. So the fold is a
   **hand-fold spec plus dry run, not proposed now** (§6).

## 1. What compiles (VERIFIED: `lake build`, `lake env lean`; `scratch/c8-conrad2/discharges_out.txt`)

| file | theorem | statement |
|---|---|---|
| `Contrib/OneProof/C8LocAlg.lean` | `locAlgExponentEqWeight_of_tateInertia` | `TateTwistInvariantsInertia → LocAlgExponentEqWeight` |
| | `exists_unit_isArtinLift`, `cyc_of_isArtinLift`, `toZModPow_cyc_eq_one`, `norm_eq_one_of_valuation_eq_one` | an element of `I_{ℚ_p}` is an Artin lift of a unit `u ∈ ℤ_p^×` and has `χ_cyc = u⁻¹` (Tau Ceti); `χ_cyc ≡ 1 mod p^k` on `G_{ℚ_p(ζ_{p^k})}` |
| | `pow_card_eq_one_of_mem_inertia` | if `ψ ∘ decomp` kills the Artin lifts of `1 + p^kℤ_p`, it has values in `μ_{φ(p^k)}` on `I_{ℚ_p}` |
| | `finiteOfLocAlgTrivialQ_of_pieces` | `InertiaFiniteAwayFromP → InertiaAtPDecomp → CFTFiniteQ → FiniteOfLocAlgTrivialQ` |
| `Contrib/OneProof/C8CFT.lean` | `eq_one_of_pow_eq_one_small`, `smallUnits`, `isOpen_smallUnits` | `V = {u : ‖u − 1‖ < ‖p‖}` is an open subgroup of `ℚ̄_p^×` with no torsion |
| | `eq_one_of_inertia_trivial` | a continuous hom out of `G_ℚ` into a `T₁` group that kills every inertia group is trivial (Krull + `MinkowskiInertiaQ`) |
| | `cftFiniteQ_of_minkowski`, `cftFiniteQNoRam_of_minkowski` | a continuous `ψ : G_ℚ → ℚ̄_p^×` with finite image on every inertia group has finite image |
| | `inertiaFiniteAwayFromP_of_decomp` | `InertiaAtPDecomp → InertiaFiniteAwayFromP` (Tau Ceti local CFT at `q`; `u^{(q−1)q^n} → 1`; `x ↦ x^{q^n}` isometric on `V`) |
| | `finiteOfLocAlgTrivialQ_of_dicts`, `finiteOfLocAlgTrivialQNoRam_of_dicts` | `InertiaAtPDecomp → MinkowskiInertiaQ → FiniteOfLocAlgTrivialQ` (and without the unramified hypothesis) |
| | `twistCharHTWt0_of_twistCharHT0` | `TwistCharHT0 → TwistCharHTWt0` (the new glue is weaker) |
| | `c8TwistFinite_of_leaves` | `EigenformRepExists → EigenformHT → ConradAppBQp → TateTwistInvariantsInertia → TwistCharHTWt0 → InertiaAtPDecomp → MinkowskiInertiaQ → C8TwistFinite` |
| `Contrib/OneProof/C8Poincare.lean` | `C8Inputs`, `g12DetPZ_of_inputs` | the five C8 inputs; `G12DetPZ` from them, R13, R14, G9 and R10 (the replacement term at `g8_g12_of_leaves3_hf_pz_eb`) |
| | `HSyn.t8_of_poincareComplement` | `PoincareComplement → PkgI3.PoincareReducibility` (Cartier, Milne quasi-inverse, `geomConnOfRationalPoint`, `groupSchemeEquidim` proved) |
| | `HSyn.openTextbookLeaves13HF_of_open16_P` | `OpenTextbookLeaves13HF` with `poincareComplement := hP` (copy of `openTextbookLeaves13HF_of_open16_22_pz`, rows not read) |
| `scratch/c8-conrad2/C8DryRun.lean` | `frozenTarget_c8`, `sixContactMin_of_open71_c8` | Theorem 1.1 and H from the current bundles plus `hP` and `c8 : C8Inputs` |
| `scratch/c8-conrad2/C8FoldDryRun.lean` | `sixContactMin_of_open72C8` | H from `OpenResearchLeaves52`, `OpenTextbookLeaves19C8 = {poincareComplement}`, `OpenAddedLeaves28C8 = rows + C8 inputs` |

All files import only kernel modules and earlier contributions: C8LocAlg imports C8Conrad and Tau Ceti; C8CFT imports
C8LocAlg; C8Poincare imports C8CFT. None imports `ZInQKernel.OneProof.Main`. `#print axioms` gives
`[propext, Classical.choice, Quot.sound]` for all ten theorems listed in `Discharges.lean`, and for the dry-run tops.

## 2. The consumers, before and after (VERIFIED)

The base map was reproduced on the merged top (`log.md` §1):
* `open71 → open70 → open48_eb_k954 → open45_pz_eb`.
* **(ii)** `open45_pz_eb` builds `OpenTextbookLeaves13HF` with
  `poincareComplement := poincareComplement_of_open0 l.picRepresentableAbVar l.picZeroAbVar …`
  (PicZeroCharZeroCopy L2218).
* **(i)** The same theorem builds `OpenAddedLeaves18PZ` (`phiAmpleIsogeny`, `weilPairingMumford` from the rows).
  `t09SymmIsogenyExists` then rides down `OpenAddedLeaves17PZ … 4PZ` to `gluePieces_of_open4_hf_pz_eb`, which fills
  `GaloisPieces.detTate`. `g12Det_of_pz` reads it in `g8_g12_of_leaves3_hf_pz_eb` (EichlerBoundCopy L2473-2486).
* **(iii)** `open70` passes `l26` to `openResearchLeaves35_of_OpenResearchLeaves36_eb_k954_cf`:
  `hodgeTateDecompAbVar → r10`.

**The copy reroute** (`scratch/c8-conrad2/gen/gen.py`, adapted from fold34-eichler's generator):
* **Taint list** (`Taint.lean`, seeds `t09SymmIsogenyExists`, `phiAmpleIsogeny`, `weilPairingMumford`, `detTate`):
  70 tainted constants and 13 carrier structures (`OpenAddedLeaves4PZ … 18PZ`, `GaloisPieces`).
* **Generated copy** (70 blocks, renamed `X ↦ X_c8`):
  * in each copied structure, the first seed field becomes `c8 : C8Inputs`; the other seed fields and the
    pass-through row fields `picRepresentableAbVar`, `picZeroAbVar` are deleted;
  * the reader in `gluePieces_c8` becomes `l.c8`;
  * the reader in `g8_g12_c8` becomes `C8Conrad.g12DetPZ_of_inputs r.r14 r.r13 m.c8 h9 r.r10`.
* **Handwritten top** (`gen/top.lean`): copies of `open45_pz_eb` (with `openTextbookLeaves13HF_of_open16_P t _ hP`),
  `open48_eb_k954`, `open70`, `open71` and `frozenTarget`.

**Field taint on `frozenTarget_c8`** (`C8DryRunTaint.lean`, closure 304382, 19 iterations): the terminal consumers
are `g8_g12_of_leaves3_hf_pz_eb_c8`, `afterG7_of3_hf_pz_eb_c8` and `gluePieces_of_open4_hf_pz_eb_c8`, each through
`ResearchLeaves3EB.r10` / `OpenResearchLeaves2EB.r10`, plus their callers. This is consumer (iii) only. The C8 route
itself reads `r.r10` too, for the weights `{0, −1}` of `r`, exactly as the existing G9 step does. That read is
harmless once (iii) no longer uses the rows.

## 3. New leaves and glue, with ratings

| name | kind | printed form? | why |
|---|---|---|---|
| `poincareComplement` (`ZInQ.Contrib.AVB1.PoincareComplement`, restored) | leaf, **ELLIOT** (L865 cites nothing), consequence | **printed form, weakened**: Milne, *Abelian varieties*, in Cornell–Silverman (eds.) 1986, Prop. 12.1 (UNVERIFIED number) | Over any field, an abelian subvariety `B ⊆ J` has a complement `Z` with `B × Z → J` an isogeny. The Lean form restricts to characteristic 0 and drops "`Z → J` is a closed immersion", so it is a consequence of the print. It was LEAF/LEAF in kinds.tsv before poincare-proof (`git show e36082663^:docs/one-proof/kinds.tsv`). Mumford §19 Thm 1 is over an algebraically closed field only (§8, Known issues). Milne's notes v2.00 locator: unread (fetch refused). |
| `conradAppBQp` (c8-conrad's, unchanged) | leaf (the manuscript's citation), consequence | printed form for `L = ℚ_p`, **unread**, unrefereed | As in c8-conrad §3.2. The flag stays unread: no page read was forwarded. |
| `tateTwistInvariantsInertia` (new) | leaf, consequence | **printed form by dictionary**: Tate, *p-divisible groups* (1967) §3.3 Thm 2 (UNVERIFIED number), for `L = \hat{K^{ur}}` | Tate's theorem is printed for every complete discretely valued field of characteristic 0 with perfect residue field. Specialized to `L` the completion of `K^{ur}`, `K/ℚ_p` finite. The dictionary step: `G_L` is the inertia group `I_K = G_K ∩ I_{ℚ_p}` (Tau Ceti's `inertiaSubgroup`), acting on `ℂ_p` (STANDARD: Krasner, continuity). The manuscript does not cite Tate; it is used only to prove the manuscript's uncited step L763-764. The tree already proves the finite-`K` case (`CloudB3W11.tateTwistInvariants_proof`), whose proof does not extend to infinite-index subgroups. |
| `inertiaAtPDecomp` (new) | GLUE (dictionary) | no | Every element of an inertia group of `ℚ̄` above `q` is conjugate in `G_ℚ` to `decomp(σ)` with `σ ∈ I_{ℚ_q}`. STANDARD: places above `q` are conjugate; the decomposition group of the place cut out by `decomp`'s embedding is `decomp(G_{ℚ_q})`, with inertia `decomp(I_{ℚ_q})` (Neukirch II §9, UNVERIFIED). |
| `minkowskiInertiaQ` (new) | GLUE (dictionary over Mathlib) | no | An algebraic number fixed by every inertia group of every place of `ℚ̄` is rational. The arithmetic content is in Mathlib: `NumberField.exists_not_isUnramifiedIn` (every number field `≠ ℚ` is ramified at some prime, from `abs_discr_gt_two`). The missing step is the dictionary from inertia groups of places of `ℚ̄` to unramifiedness of the Galois closure of `ℚ(x)`. |
| `twistCharHTWt0` (new; replaces `twistCharHT0`, weaker) | GLUE, **on-the-spot** | no | §4.3. |

Two glue Props become theorems, `locAlgExponentEqWeight` and `finiteOfLocAlgTrivialQ`, and c8-conrad's `twistCharHT0`
is replaced by a weaker Prop. The other new glue are dictionaries, with no class-field-theory or Hodge-theory content
left in them.

## 4. Task part (1): c8-conrad's three glue Props

### 4.1 `LocAlgExponentEqWeight`: proved from `TateTwistInvariantsInertia` (VERIFIED, compiled)

`HasHTWeights {w}` makes `H_{−w}(ψ)` nonzero (integer division in `htMult`: `htMult w = 1` forces
`finrank > 0`), so pick `φ ≠ 0` and `v` with `x = φ(v) ≠ 0`. Let `K = ℚ_p(ζ_{p^k})`. Every
`σ ∈ G_K ∩ I_{ℚ_p}` is an Artin lift of some `u ∈ ℤ_p^×`:
* Tau Ceti's `map_artinMap_unitFiltration_zero`, with Mathlib's `ValuativeRel` valuation of `ℚ_p` converted to the
  norm;
* `χ_cyc(σ) = u⁻¹`, from Tau Ceti's `localCyclotomicCharacter_artinMap_padic`; PkgI4's `cyc` is Tau Ceti's
  `localCyclotomicCharacter` by `rfl`;
* `σ` fixes `ζ_{p^k}`, so `u ≡ 1 mod p^k`.

Local algebraicity then gives `ψ(σ) = u^n ∈ ℚ_p`, and the equivariance of `φ` gives `χ(σ)^{n−w} σ(x) = x` on
`I_K`. The leaf forces `n = w`. The finite-`K` theorem in the tree is not enough: the equation holds only on inertia,
and the unramified part of `ψ` is unknown. That is why the leaf is Tate's theorem over `\hat{K^{ur}}`.

### 4.2 `FiniteOfLocAlgTrivialQ`: proved from `InertiaAtPDecomp` and `MinkowskiInertiaQ` (VERIFIED, compiled)

* **At `p`:** an element of `I_{ℚ_p}` is an Artin lift of a unit `u`. Its `φ(p^k)`-th power is an Artin lift of
  `u^{φ(p^k)} ∈ 1 + p^kℤ_p`, so `ψ ∘ decomp` has values in `μ_{φ(p^k)}` on `I_{ℚ_p}`, and through `InertiaAtPDecomp`
  on every inertia group above `p`.
* **At `q ≠ p` (N5's unstated step; rv-h-c8 §4 item 3):**
  * `ψ^m` takes values in the torsion-free open subgroup `V`. Here `m` is the index of the open normal subgroup
    `ψ⁻¹(V)`, finite since `G_ℚ` is compact.
  * On `I_{ℚ_q}`, `ψ^m ∘ decomp` factors through Tau Ceti's topological abelianization and continuous Artin map. For
    a unit `u`, `u^{(q−1)q^n} → 1` in `ℚ_q^×` (`dvd_sub_pow_of_dvd_sub`).
  * `x ↦ x^{q^n}` is an isometry on `V`, because `‖q‖ = 1` in `ℚ̄_p`. So `‖y^{q−1} − 1‖` is constant and tends to
    0, hence `y^{q−1} = 1`, hence `y = 1` (`V` has no torsion).
* **Globally:** every inertia group has finite image, so `ψ^m` kills every inertia group (no torsion in `V`). By
  Krull and `MinkowskiInertiaQ`, `ψ^m = 1`, so `ψ` has values in `μ_m`. The hypothesis "unramified outside a finite
  set" is never used.

### 4.3 `TwistCharHT0`: not proved; reduced to `TwistCharHTWt0` (on-the-spot)

The proof of C8 uses only the Hodge–Tate half (`c8TwistFinite_of_leaves`). `TwistCharHTWt0`: under the same
hypotheses, `ψ|_{G_{ℚ_5}}` takes values in a finite `E/ℚ_5` and has `HasHTWeights 5 (charRep ψE) {0}`.

**On-the-spot sketch** (N5 L758-760: "the twisting character is a de Rham subrepresentation of the Hom
representation"):
1. With `ρ_g` from R14, Chebotarev density and continuity extend `tr r = ψ · tr ρ_g` from Frobenius elements to all
   of `G_ℚ`. Brauer–Nesbitt then gives `r^{ss} ≅ ψ ⊗ ρ_g`, so `ψ ⊆ Hom(ρ_g, r^{ss})`.
2. Hodge–Tate representations are stable under `Hom`, subquotients and semisimplification (Fontaine; Brinon–Conrad,
   CMI notes §2.4, UNVERIFIED). So `ψ|_{G_{ℚ_5}}` is Hodge–Tate of some weight `s`, with values in a finite
   extension (Baire).
3. R13 gives `ρ_g` the weights `{0, −1}`, and `r` has the weights `{0, −1}`, so `{s, s−1} = {0, −1}` and `s = 0`.
   The tree's `senTwist_of_tate` proves this shift once `ψ` is known to be Hodge–Tate.

The statement is true as written. `r` need not be assumed semisimple, since `r^{ss}` is used.

**Why it is not proved here.** The tree's Hodge–Tate machinery (`TailT` §16, `exists_twist_scalar`) needs an exact
twist `r = ψ ⊗ ρ_g`, i.e. semisimple `r`. `G12DetPZ` does not give semisimplicity, and the machinery is stated over
the G9 copy of PkgI4. The semisimplification step (Hodge–Tate is stable under subquotients and semisimplification)
and the finite coefficient field (Baire) are not in the tree.

The unramified half is not needed any more: `FiniteOfLocAlgTrivialQNoRam`.

## 5. Task part (2): Poincaré reducibility (step E1-E2, L865)

* The manuscript's sentence (L864-866, paraphrased): absolute simplicity and Poincaré reducibility give an
  `L'`-isogeny `A × Z → J`. No citation. h-trust E1 names Mumford §19 Thm 1.
* The consumer needs the theorem over the number field `L'`, in the form `AVB1.PoincareComplement` (any field of
  characteristic 0). That is the form of Milne's Prop. 12.1, which holds over any field. Mumford §19 Thm 1 is stated
  over an algebraically closed field. Both base-field claims are from memory (UNVERIFIED). So the leaf is stated as Milne's, weakened (§3).
* `t8` from it: `HSyn.t8_of_poincareComplement` is the chain's own derivation (`textbookLeaves6_of_open7_hf_pz`,
  PicZeroCharZeroCopy L1640) with its other inputs proved. In the dry run the textbook bundle is built by
  `openTextbookLeaves13HF_of_open16_P`, so the field taint no longer reaches `poincareComplement` or `t8` (§2).

## 6. Task part (4): fold, `#discharges`

**`#discharges`** (`scratch/c8-conrad2/Discharges.lean`, output `discharges_out.txt`; imports Main, Discharges,
C8Conrad, C8LocAlg, C8CFT, C8Poincare): 35 open hypotheses, 16111 theorems checked, 19 discharge one. **None of the
19 is from the new files.** That is expected: `G12DetPZ`, `DetTate`, `poincareComplement` and `t8` are not open
hypotheses of `frozenTarget`.

**Hand-fold spec** (`scratch/c8-conrad2/autofold.json`, `"discharges": []`, section `handfold`). It is a copy reroute,
not an autofold.
1. **Generate the copy.** Run `Taint.lean` on the built top, then `gen/gen.py` (excluding the four top theorems).
   This gives `OneProof/H/C8PoincareCopy.lean` (the dry run's 70 blocks).
2. **C8 swap.** At `g8_g12_of_leaves3_hf_pz_eb`, replace
   `(g12Det_of_pz m.r14det m.detTate m.finIndex (frobeniusDenseQ_of t.frobeniusDense))` by
   `(C8Conrad.g12DetPZ_of_inputs r.r14 r.r13 m.c8 h9 r.r10)`. `GaloisPieces.detTate` becomes `c8 : C8Inputs`, filled
   by `l.c8`.
3. **t8 swap.** At `sixContactMin_of_open45_pz_eb`, replace
   `openTextbookLeaves13HF_of_open16_22_pz t r.neronSchemeExtensionDedekind l` by
   `openTextbookLeaves13HF_of_open16_P t r.neronSchemeExtensionDedekind hP`.
4. **New generations** (`gen/fold.lean`):
   * `OpenTextbookLeaves19 = {poincareComplement}`;
   * `OpenAddedLeaves28 = OpenAddedLeaves27 + {conradAppBQp, tateTwistInvariantsInertia, twistCharHTWt0,
     inertiaAtPDecomp, minkowskiInertiaQ}`;
   * the top `sixContactMin_of_open72 r t l := sixContactMin_of_open71_c8 r ⟨⟩ (… l) t.poincareComplement (… l)`.
   * The dry run is `C8FoldDryRun.lean` (standard axioms).
5. **Counts.** Alone, this fold removes nothing and adds 6 rows. **Do not fold until consumer (iii) is rerouted.**
   Then `picRepresentableAbVar` and `kleimanPicZeroProper954SiteQ` (both GLUE) leave, and the 6 rows enter:
   * one ELLIOT consequence leaf (`poincareComplement`);
   * two consequence leaves (`conradAppBQp`, unread and unrefereed, so GLUE by the strict reading;
     `tateTwistInvariantsInertia`);
   * three glue (`twistCharHTWt0`, `inertiaAtPDecomp`, `minkowskiInertiaQ`).

   Net +4 rows (SPECULATIVE until rated). In exchange, the Picard scheme leaves the route, and C8 follows the
   manuscript's own argument.

**Remaining consumers of the Picard rows: only (iii)** (VERIFIED by the field-taint run, §2).

## 7. Task part (3): what consumer (iii) would need (not rerouted here)

`hodgeTateDecompAbVar_of_open_k954` (TailZ69 L55) gets the multiplicities `(g, g)` of the Hodge–Tate decomposition
of `V_p(A)` from the leaf `HodgeTateDecompExists` (some `(a, b)`) plus `a = b` from a symmetric isogeny
`A → A^∨` (`t09SymmIsogenyExists0_of_open_k954`, i.e. the Picard rows).

The manuscript gets the weights another way (lemma `lem:de-rham-descent`, L10939-11003; L10995 paraphrased): the
two Hodge numbers of `H^1_dR(A/F)` are `2, 2`, and the de Rham comparison (Scholze Cor. 1.8, cited L736-737) carries
them to the Tate module.

So (iii) would need:
* a leaf for the de Rham / Hodge–Tate comparison with filtration (Scholze 2013 Cor. 1.8 as cited; or Faltings 1988
  Ch. III Thm 4.1, cited at L11003, for Hodge–Tate only);
* the Hodge numbers `h^{1,0} = dim H^0(A, Ω¹) = g` and `h^{0,1} = dim H^1(A, 𝒪_A) = g` (the latter is Mumford §13;
  the manuscript cites nothing at L10995).

`dim A^∨ = g` and the Weil pairing would then not be used. This is the derham-scholze task's scope. Once it lands,
the hand-fold of §6 removes both rows.

## 8. Known issues and limitations

* **Known issue with h-trust's supplier at E1, not with the manuscript.** h-trust E1 names Mumford §19 Thm 1 for
  Poincaré reducibility. Mumford's book works over an algebraically closed field (from memory, UNVERIFIED), but the manuscript applies the theorem over
  the number field `L'` (L865). The consumer's form (`PoincareComplement`, over any field of characteristic 0) is
  Milne's Prop. 12.1, which is over an arbitrary field (from memory, UNVERIFIED). The leaf is therefore stated and attributed as Milne's.
  The manuscript itself cites nothing, so this is a supplier correction, not a gap.
* **Locators unread on this host.**
  * Milne 1986 Prop. 12.1 and Milne AV v2.00: the task asked for a checked locator; jmilne.org cannot be fetched.
  * Tate 1967 §3.3 Thm 2.
  * Conrad App. B: the flag stays **unread**; no page read was forwarded.
* **Conrad App. B is an unrefereed preprint** (c8-conrad §6). It is the manuscript's citation, so it is kept. By the
  strict LEAF definition it counts as GLUE.
* **`tateTwistInvariantsInertia` is not a manuscript citation.** It proves the manuscript's uncited step
  "removing its integral local Hodge–Tate weight" (L763-764). It is the same printed theorem the tree uses at
  finite level, applied to a different complete field. If Conrad's paragraph is read and it ties the weights to the
  exponents, `LocAlgExponentEqWeight` could be read off the print instead (c8-conrad §6).
* **`htMult` uses integer division** (`finrank H_{−w} / [E : ℚ_p]`). This is harmless here (`H_i` is an
  `E`-module), but `HasHTWeights {w}` literally says `[E:ℚ_p] ≤ dim H_{−w} < 2[E:ℚ_p]`.
* **The dry run is not a fold.** The generated copy lives in `scratch/`, and no file under `ZInQKernel/` other than
  the four `Contrib/OneProof/C8*.lean` files was edited. No consumer statement was changed: the copies keep every
  statement up to renaming, and the C8 swap replaces a term, not a type.

## 9. On-the-spot steps (neither in the manuscript nor in a cited print)

* **`twistCharHTWt0`** (§4.3): unproved, with the sketch there.
* **N5's "finite inertia at every other prime"** (L764): now a proof (`inertiaFiniteAwayFromP_of_decomp`), from the
  dictionary and Tau Ceti.
* **The two dictionaries.**
  * `InertiaAtPDecomp`: conjugacy of places above `q`, and decomposition group = `decomp(G_{ℚ_q})` by Krasner.
  * `MinkowskiInertiaQ`: if all inertia groups fix `x`, the Galois closure of `ℚ(x)` has trivial inertia at every
    prime, so it is unramified, so it is `ℚ` by Minkowski (in Mathlib).
* **The weight–exponent proof (§4.1)** and the torsion-free subgroup `V` (§4.2): proved in Lean.

## 10. Files

* `ZInQKernel/Contrib/OneProof/C8LocAlg.lean`, `C8CFT.lean`, `C8Poincare.lean` (new);
  `C8Conrad.lean` (c8-conrad's, unchanged).
* `scratch/c8-conrad2/`: `log.md`; `Taint.lean` and `taint_out.txt`; `gen/` (`gen.py`, `copylib.py`, `header.lean`,
  `top.lean`, `fold.lean`); `C8DryRunGen.lean`, `C8DryRun.lean` and `dryrun_out.txt`; `C8FoldDryRun.lean`;
  `C8DryRunTaint.lean` and `dryrun_taint_out.txt`; `Discharges.lean` and `discharges_out.txt`; `autofold.json`;
  scratch copies of the contribution files.
* Proposed `kinds.tsv` rows and `locators.md` rows: the `new_leaves` list in `autofold.json` (not written to the
  shared files).

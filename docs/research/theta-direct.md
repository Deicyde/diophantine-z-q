# theta-direct: `ThetaRatiosAtQM` proved with no hypotheses (no Lin–Yang, no new leaf)

Task theta-direct, 2026-11-16. Base a40d5c4d (wip/theta-direct: fork main 862bd440 + STATUS w76). The merge of
origin/wip/theta-fold (8e3dbdea) conflicted (STATUS.md, Main.lean, docs/one-proof/*,
scratch/contrib-kit/DischargesTest-output.txt) and was aborted; the definitions needed from theta-fold were copied
verbatim into helper modules (each names its source and line range). Results log: scratch/theta-direct/log.md.
This is model work with no human review.

Marks: **VERIFIED** = compiled, computed, or read in a named file on this host. **STANDARD** = published, exact
reference. **SPECULATIVE** = a judgement. Locators recalled from memory are **UNVERIFIED** (no network).

## 1. Result

The use form of the added composite field `thetaRatiosAlgebraic` (GLUE) is a **theorem with no hypotheses**
(VERIFIED: `lake build ZInQKernel.Contrib.OneProof.ThetaDirect` succeeds, 12138 jobs; `#print axioms` below):

```lean
-- ZInQKernel/Contrib/OneProof/ThetaDirect.lean, namespace HDec.ThetaDirect
theorem thetaRatiosAtQM_proof : HDec.HSyn.G0Split.ThetaPt.ThetaSplit.ThetaRatiosAtQM
theorem thetaRatiosAtQM_of_qmHauptmodul : HDec.PkgI1.QMHauptmodul →
    HDec.HSyn.G0Split.ThetaPt.ThetaSplit.ThetaRatiosAtQM          -- theta-fold's consumer binder `hθ`
theorem thetaPointOfFibre_of_qmPeriod : HDec.HSyn.G0Split.ThetaPt.FibreQMPeriod →
    HDec.HSyn.G0Split.ThetaPointOfFibre                            -- drop-in for thetaPointOfFibre_of_qm_ratios _ l.thetaRatiosAlgebraic
```

`ThetaRatiosAtQM` is theta-split's statement, copied verbatim from theta-fold's TailK.lean l.281-346 into
`ThetaDirect/UseForm.lean` (`#print`, VERIFIED, scratch/theta-direct/axioms.txt):

```lean
def HDec.HSyn.G0Split.ThetaPt.ThetaSplit.ThetaRatiosAtQM : Prop :=
∀ (τ : ℂ), 0 < τ.im → ∀ (q : ℚ), q ≠ 0 →
  HDec.PkgI1.jNum (HDec.PkgI1.Omega τ) / HDec.PkgI1.jDen (HDec.PkgI1.Omega τ) = ↑q →
  ∃ m₀, ZInQ.LeafPush2.thetaConst (BPAnalytic.QM.Omega τ) m₀ ≠ 0 ∧
    ∀ (m : ZInQ.LeafPush2.Char2), IsAlgebraic ℚ
      (ZInQ.LeafPush2.thetaConst (BPAnalytic.QM.Omega τ) m / ZInQ.LeafPush2.thetaConst (BPAnalytic.QM.Omega τ) m₀)
```

`#print axioms` (scratch/theta-direct/Axioms.lean → axioms.txt, VERIFIED): `thetaRatiosAtQM_proof`,
`thetaRatiosAtQM_of_qmHauptmodul`, `thetaPointOfFibre_of_qmPeriod`, and the intermediate theorems
`qmThetaSymmetricAlg_proof`, `thetaRatiosAtQM_of_symAlg`, `rel1`, `rel2`, `psi6Th_M4`, `psi6Th_M6`, `chi12Th_M4`,
`chi12Th_M6`, `nodeAlg_om24`, `nodeAlg_cm4`, `eq_zero_of_nodes`, `autoGS` all depend on axioms
`[propext, Classical.choice, Quot.sound]`.

**Consequence for the frozen target.** `thetaRatiosAlgebraic` can be removed from `frozenTarget` with **no new
hypothesis**: −1 GLUE, −1 field, no leaf added. (The task's expected outcome was "replaced by
`IgusaThetaExpressions` alone"; that leaf turned out to be unnecessary, see §4.2. theta-fold's fold was −1 GLUE
+2 leaves, one of them false.)

**New leaves: none.** Nothing to rate. The contributor files contain no `sorry`, no macro, notation, `#eval` or other
build-time code (CONTRIBUTING.md).

**Intermediate statements** (all proved; they are GLUE-level statements of this file, not hypotheses):

| name | statement (informal; exact Lean in the files) |
|---|---|
| `psi6Th_M4/M6`, `chi12Th_M4/M6` | Igusa's theta expressions `ψ₆`, `χ₁₂` (theta-glue's `psi6Th`, `chi12Th`) satisfy `S(MΩ) = det(CΩ+D)^w S(Ω)`, `w = 6, 12`, for `M = M4, M6`, `Ω ∈ 𝔥₂` |
| `auto6`, `auto12` | `ψ₆(Ω(z))/((z−3)(z+1))⁶` and `χ₁₂(Ω(z))/((z−3)(z+1))¹²` are automorphic forms of weight 12, 24 for `Γ*` |
| `eq_zero_of_nodes` | a weight-`2m` form for `Γ*` vanishing at `r` pairwise inequivalent points where another weight-`2m` form is nonzero vanishes on `ℍ` if `m < 12r` |
| `nodeAlg_om24`, `nodeAlg_cm4` | all `θ_m/θ_{(0,0)}` are algebraic at `Ω(τ₂₄) = Ω₂₄` and at `Ω(√2+i) = Ω₀` |
| `rel1` | `∀ z, 0 < Im z → ψ₆(Ω(z))·Σθ⁸(Ω(z)) = c₁·∏θ²(Ω(z))`, with `c1_mem : c₁ ∈ algebraicClosure ℚ ℂ` |
| `rel2` | `∀ z, 0 < Im z → Σθ⁸(Ω(z))²·χ₁₂(Ω(z)) = c₂·Σθ⁸(Ω(z))⁵ + c₃·∏θ²(Ω(z))²`, `c2_mem`, `c3_mem` |
| `QMThetaSymmetricAlg` (def), `qmThetaSymmetricAlg_proof` | where `j_θ(Ω(τ)) = q ∈ ℚ∖0`, every `e_k(θ_m⁸)/(Σθ⁸)^k`, `k ≤ 10`, is algebraic |
| `thetaRatiosAtQM_of_symAlg` | `QMThetaSymmetricAlg → ThetaRatiosAtQM` |

## 2. `#discharges`

scratch/theta-direct/Discharges.lean (imports `ZInQKernel.OneProof.Main`, `ZInQKernel.OneProof.Discharges`,
`ZInQKernel.Contrib.OneProof.ThetaDirect`); output saved as scratch/theta-direct/discharges.txt (VERIFIED, after
`lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.ThetaDirect`,
13007 jobs):

```
DISCHARGES [OpenResearchLeaves22.gonzalezRotgerProp56X6] by GRCountX6.prop56X6_of_r5fpCount ...
... (the base's seven contribution discharges, unchanged)
#discharges: 62 open hypotheses, 2804 theorems checked, 7 discharge one
```

As expected, no line for `thetaRatiosAlgebraic`: the theorem proves the **use form** `ThetaRatiosAtQM`, not the
universal field `ThetaRatiosAlgebraic` (every abelian surface over every number field). The universal statement is
not proved here (theta-split §8: it is true by the model argument but stronger than its only use). So the fold is a
manual fold (consumer rerouted), not an autofold; no autofold.json is written (autofold.py only handles discharged
fields).

## 3. The manual fold

Only reader of the field (VERIFIED by grep at a40d5c4d; theta-fold's PruneScan found the same):
`ZInQKernel/OneProof/H/TailK.lean` l.285 `gluePieces_of_open4`, field `thetaPoint` (l.305-314):
`G0Split.ThetaPt.thetaPointOfFibre_of_qm_ratios (G0Split.FibreQM.fibreQMPeriod_main_rep …) l.thetaRatiosAlgebraic`.
TailK cannot import the contributor module (it imports TailZ19), so the proof enters at the top, exactly as in
theta-fold's plumbing. The fold is generated, as a patch against a40d5c4d, by
`python3 scratch/theta-direct/fold/make_fold.py` → `scratch/theta-direct/fold/fold.patch` (905 lines, 30 files).
**The patched tree builds** (VERIFIED, §3.1).

1. **Plumbing** (theta-fold's `plumb.py`, copied unchanged as scratch/theta-direct/fold/plumb_theta_fold.py):
   * move theta-split's `ThetaRatiosAtQM`, `Jmap_ne_zero`, `thetaPointOfFibre_of_qm_atQM` into TailK just before
     `gluePieces_of_open4` (l.282), namespace `HDec.HSyn.G0Split.ThetaPt.ThetaSplit`;
   * TailK l.285 `gluePieces_of_open4`: new binder `(hθ : PkgI1.QMHauptmodul → G0Split.ThetaPt.ThetaSplit.ThetaRatiosAtQM)`;
     replacement term for `thetaPoint`:
     `G0Split.ThetaPt.ThetaSplit.thetaPointOfFibre_of_qm_atQM (G0Split.FibreQM.fibreQMPeriod_main_rep …) (hθ l.qmHauptmodul)`;
   * thread `hθ` (new last binder, passed down): TailK l.351 `sixContactMin_of_open4` (passes it to
     `gluePieces_of_open4`), TailO l.2920 `_open6` (and the `example` after it), TailX l.277 `_open7`, TailZ4 l.257
     `_open8`, TailZ9 l.143 `_open9`, TailZ11 l.55 `_open10`, TailZ13 l.68 `_open11`, TailZ15 l.132 `_open12`, TailZ17
     l.277 `_open13`, TailZ18 l.1250 `_open14`, TailZ19 l.1913 `_open15`, TailZ22 l.335 `_open16`, TailZ23 l.812
     `_open17`, TailZ24 l.835 `_open18`, TailZ25 l.137 `_open19`, TailZ26 l.193 `_open20`, TailZ27 l.125 `_open21`,
     TailZ28 l.124 `_open22`, TailZ29 l.121 `_open23`, TailZ30 l.73 `_open24`, TailZ31 l.69 `_open25`, TailZ32 l.45
     `_open26`, TailZ33 l.122 `_open27`, TailZ34 l.172 `_open28`, and (new on this base) TailZ35 l.116 `_open29`.
2. **Top** (ZInQKernel/OneProof/Main.lean): add `import ZInQKernel.Contrib.OneProof.ThetaDirect`; l.70
   `(HDec.HSyn.sixContactMin_of_open29 r t l g)` → `(HDec.HSyn.sixContactMin_of_open29 r t l g
   HDec.ThetaDirect.thetaRatiosAtQM_of_qmHauptmodul)`. No new bundle field, no new generation.
3. **Prune** (theta-fold's `prune_edit.py` without its TailZ41 rows; every deleted line in
   scratch/theta-direct/fold/fold-deleted.txt): delete the fields `thetaRatiosAlgebraic` of `OpenAddedLeaves4` (TailK
   l.191), `6` (TailO l.2815), `7` (TailX l.153), `8` (TailZ4 l.129), `9` (TailZ13 l.20), `12` (TailZ22 l.233), `13`
   (TailZ24 l.770), `14` (TailZ26 l.133), `15` (TailZ30 l.15), `16` (TailZ31 l.15), `17` (TailZ34 l.118); the
   assignments into them (TailN l.232, TailO l.2886, TailX l.248, TailZ4 l.233, TailZ13 l.48, TailZ17 l.256, TailZ23
   l.741, TailZ24 l.816, TailZ26 l.174, TailZ30 l.55, TailZ31 l.52, TailZ34 l.156); the element
   `l.thetaRatiosAlgebraic` of the anonymous constructor in TailO l.2595 (`openAddedLeaves4_of_Q5`); the dead readers
   `addedLeaves5_of_open6` (TailO l.2927), `addedLeaves11_of_open12` (TailZ22 l.316), `sixContactMin_of_open16`
   (TailZ22 l.335) with their `#print axioms` lines.
4. **ZInQKernel/Contrib/OneProof/X0ModuliUsed.lean** (hX-fold's alternative tops `frozenTarget_of_used`,
   `frozenTarget_of_eta`, `frozenTarget_of_theta`; found by the fold-check build): l.334, l.363, l.387
   `(HDec.HSyn.sixContactMin_of_open29 r t l g)` → `(… r t l g HDec.ThetaDirect.thetaRatiosAtQM_of_qmHauptmodul)`, and
   `import ZInQKernel.Contrib.OneProof.ThetaDirect`.
5. **Contributor modules**: delete `ThetaDirect/UseForm.lean` (its block is then in TailK); in `ThetaDirect/Split.lean`
   replace `import ZInQKernel.Contrib.OneProof.ThetaDirect.UseForm` by `import ZInQKernel.OneProof.H.TailZ19`.

After the fold, the H part has 55 hypotheses (OpenAddedLeaves17 loses one field); kinds.tsv/claims.tsv lose the
`thetaRatiosAlgebraic` row and gain nothing.

### 3.1 Fold check (VERIFIED)

`git archive HEAD` into /tmp/td_foldcheck, `patch -p1 -E < fold.patch`, the worktree's `.lake/build` and
`lean/.lake/build` copied, `.lake/packages` symlinked; then `lake build ZInQKernel.OneProof.Main
ZInQKernel.OneProof.Discharges`: **Build completed successfully (13006 jobs)** (first attempt failed only in
X0ModuliUsed.lean, now item 4). In the patched tree (scratch/theta-direct/fold/FoldAx.lean →
foldcheck-axioms-discharges.txt):
* `#print axioms ZInQ.OneProof.frozenTarget`: `[propext, Classical.choice, Quot.sound]`; same for
  `X0ModuliUsed.frozenTarget_of_theta`;
* `frozenTarget`'s type is unchanged in form (`OpenResearchLeaves22 → OpenTextbookLeaves11 → OpenAddedLeaves17 →
  OpenGlue7 → …`), and `OpenAddedLeaves17` no longer has `thetaRatiosAlgebraic` (grep: 0 occurrences in TailZ34);
* `#discharges: 61 open hypotheses, 2799 theorems checked, 7 discharge one` (base: 62 open hypotheses).

Not run on the patched tree: PruneScan/DumpCompact (the integration lead's tools), the docs regeneration.

## 4. Method

### 4.1 Plan (why no Lin–Yang is needed)

`ThetaRatiosAtQM` asks for algebraic theta ratios on the rational fibres of `j_θ = 3779136∏θ⁴/(Σθ⁸)⁵` along the
explicit QM curve `Ω(τ)`. igusa-alg reduced it (`IgusaAlg 3..9`, Kronecker-checked) to Igusa's generators: the
`e_k(θ⁸)` are explicit polynomials in theta-glue's theta expressions `ψ₄, ψ₆, χ₁₀, χ₁₂`. Lin–Yang's Example 29 was
used only to know `ψ₆, χ₁₂` along the curve. Here that knowledge is replaced by two dimension counts for automorphic
forms on `Γ*`, done with the kernel's proved valence formula, and by the values at two CM points:

* the space of weight-20 forms on `Γ*` (`m = 10 < 12`) is at most one-dimensional ⇒ (R1) `ψ₆Σθ⁸ ∝ ∏θ²`;
* the space of weight-40 forms (`m = 20 < 24`) is at most two-dimensional ⇒ (R2) `(Σθ⁸)²χ₁₂ ∈ span((Σθ⁸)⁵, (∏θ²)²)`;
* the proportionality constants are algebraic because theta ratios are algebraic at `√2 + i` and `τ₂₄`.

### 4.2 Modularity of `ψ₆` and `χ₁₂` without a leaf (`ThetaDirect/Modular.lean`)

The automorphy for `Γ*` needs only the transformation laws at gt-theta's two matrices `M4`, `M6` (generators of `Γ*`
up to scalars: `gammaStarGen_proof`). gt-theta proved, for every characteristic `m`,
`θ_m(MΩ)² = −D·exp(πiN_M(m)/4)·θ_{σ_M(m)}(Ω)²` (`GapTheta.sq4`, `GapTheta.sq6`) with explicit `σ_M`, `N_M` and
`D = ±det(CΩ+D)`. theta-glue's `ψ₆ = psi6T(θ²)` (60 terms) and `χ₁₂ = chi12T(θ²)` (15 terms) contain only squares of
products of the `t_m = θ_m²`, so each phase enters squared: `e² = (−1)^{N/2}`. **Finding (VERIFIED, exact sympy,
scratch/theta-direct/py/psi6_check.py): for `M4` and `M6` the signed permutation maps the terms of `psi6T` and of
`chi12T` onto themselves, formally in the ten `t_m`** (no Riemann relation is needed; also checked in the four
second-order theta constants). In Lean: `σ`- and `e²`-values on the ten even characteristics by `decide`/`norm_num`
(generated by py/gen_modular.py), then one `ring` per identity. So the LEAF `IgusaThetaExpressions` (Igusa's theta
expressions of the Eisenstein series), which the task allowed, is not used: the theta expressions are handled as
explicit polynomials only.

### 4.3 Automorphy and the valence argument (`ThetaDirect/Valence.lean`, `Relations.lean`)

* `autoGS`: for `S` with the weight-`w` law at `M4`, `M6` along `Ω(z)` (`w` even), `S(Ω(z))/((z−3)(z+1))^w` has
  exact automorphy of weight `2w` for `Γ*`. This is period-glue's proof of `s8WeightExact_of` (TailJ, for `Σθ⁸`) with
  `S` and `w` in place of `Σθ⁸` and 4: the automorphy group is a subgroup containing `ι(x₄)`, `ι(x₆)` (modular
  embedding identities `I1_g4` … `I2_g6`, reused) and the rational scalars.
* `eq_zero_of_nodes`: if `F` (weight `2m`) vanishes at pairwise inequivalent `z₁ … z_r` and some form `F₂` of the same
  weight is nonzero there, then by the kernel's `ellipticOrderDvd_proof` each `ord_{z_i}F` is a positive multiple of
  `e_{z_i}`, so each contributes `≥ 1` to `Σ ord/e`; the valence formula (`valenceFormulaGammaStar_of_leaves` with the
  proved `valenceFormulaCocompactEq_proof`, `shimizuCovolumeO1_proof`) bounds the sum by `m/12`. So `F ≡ 0` once
  `12r > m`.
* (R1): `F = ψ₆G₈ − c₁G₂₀` (weight 20; `G₈`, `G₂₀` the kernel's normalized `Σθ⁸∘Ω`, `∏θ²∘Ω`), node `τ₂₄` with
  `F₂ = G₂₀`. (R2): `F = G₈²χ₁₂ − c₂G₈⁵ − c₃G₂₀²` (weight 40), nodes `√2+i` (`G₂₀ = 0` there: `Pf_tau4`) and `τ₂₄`,
  `F₂ = G₈⁵`. The nodes are inequivalent because `G₂₀` vanishes at one and not at the other.

### 4.4 Algebraic theta ratios at the nodes (`ThetaDirect/Nodes.lean`)

* `τ₂₄`, `Ω(τ₂₄) = Ω₂₄` (`omega_tau24`): cm24-value's explicit squares `θ_m(Ω₂₄)² = E·Q_m(U)` (TailZ18
  `sqc0`…`sqc9`) with `U` products of genus-one theta constants at `i√6`, `i√6/2`; Landen and Jacobi give
  `U₀₀² = A⁴(1−k)`, `U₁₀² = A⁴(−k(1+k))`, `(U₀₁²)² = A⁸(−4k(1−k²))` (the computations of
  `CM24.thetaValueAtOmega24_of_mpoly`, repeated), and `k` is a root of `mpoly` (`CM24.mpoly_theta`).
* `√2 + i`, `Ω(√2+i) = Ω₀ = [[(−1+i)/2, 1], [1, −1+i]]` (`omega_cm4`): period-glue's factorization
  `θ_m(Ω₀) = u·Θ(τ₁)·Θ(τ₂)` (`thetaConst_factor`), the translation `τ ↦ τ+1`, Mathlib's inversion (`CM24.sA/sB/sC`),
  `θ₀₁(i) = θ₁₀(i)` and Jacobi's `θ₀₀(i)⁴ = 2θ₀₁(i)⁴`: every value is an algebraic multiple of `K·θ₀₀(i)` (at `τ₁`) or
  `θ₀₀(i)` (at `τ₂`).

### 4.5 The rational fibres (`ThetaDirect.lean`)

At `τ` with `j_θ = q ∈ ℚ∖0`: `Σθ⁸ ≠ 0`, `∏θ² ≠ 0`. Choose `ρ² = Σθ⁸`, put `ξ = ∏θ²/ρ⁵` (`ξ² = q/3779136`). By (R1),
(R2) and the definitions, `ψ₄ = ρ²/4`, `ψ₆ = ρ³c₁ξ`, `χ₁₀ = −ρ⁵ξ/2¹⁴`, `χ₁₂ = ρ⁶(c₂ + c₃ξ²)`. Weighted homogeneity of
igusa-alg's `P_k` (`igusaP_hom`) gives `e_k(θ⁸)/(Σθ⁸)^k = P_k(1/4, c₁ξ, −ξ/2¹⁴, c₂+c₃ξ²)`, algebraic, for
`3 ≤ k ≤ 9`; `k = 2` by theta-glue's `thetaEightSquare`; `k = 0, 1, 10` directly. theta-split's last step
(`mem_of_esymm_mem`, copied) gives the ratios.

## 5. Files

| file | content | origin |
|---|---|---|
| `ZInQKernel/Contrib/OneProof/ThetaDirect.lean` | node values, `c₁ c₂ c₃` algebraic, `QMThetaSymmetricAlg`, main theorems | new |
| `ThetaDirect/Relations.lean` | automorphy of `ψ₆`, `χ₁₂` on `Γ*`, nodes, (R1), (R2) | new |
| `ThetaDirect/Modular.lean` | `ψ₆`, `χ₁₂` under `M4`, `M6` | new (lemmas `σ…`, `e…` generated by py/gen_modular.py) |
| `ThetaDirect/Nodes.lean` | algebraic theta ratios at `Ω₂₄`, `Ω₀` | new |
| `ThetaDirect/Valence.lean` | `eq_zero_of_nodes`, `Auto` algebra, `autoGS` | new (generalizes period-glue's G8Auto proof) |
| `ThetaDirect/Analytic.lean` | `thetaConst_omega_analyticAt` | theta-fold LinYangPrinted.lean l.139-210 (namespace changed) |
| `ThetaDirect/UseForm.lean` | `ThetaRatiosAtQM`, `Jmap_ne_zero`, `thetaPointOfFibre_of_qm_atQM` | theta-fold TailK.lean l.281-346, verbatim |
| `ThetaDirect/Kron.lean`, `Split.lean`, `Glue.lean` | igusa-alg's Kronecker engine; theta-split §2-§4, §7; theta-glue + `IgusaAlg 3..9` | theta-fold's LinYangKron/Split/Glue, verbatim (imports changed) |
| scratch/theta-direct/Axioms.lean, axioms.txt | `#print axioms` | |
| scratch/theta-direct/Discharges.lean, discharges.txt | `#discharges` | |
| scratch/theta-direct/fold/ | make_fold.py, fold.patch, fold-deleted.txt, theta-fold's plumb/prune scripts | |
| scratch/theta-direct/py/ | psi6_check.py (exact invariance check), gen_modular.py (+ .out) | |
| scratch/theta-direct/tf_*.lean.txt | theta-fold's four contributor modules, for reference | |

Size of the contributor tree: 226 KB in ten files, each under 65 KB. Build of the new modules (Valence → Nodes →
Modular → Relations → ThetaDirect) about 2 min; the copied Kron/Glue about 3 min.

## 6. What remains

* The fold itself (integration lead): fold.patch builds (§3.1); docs/one-proof, kinds.tsv, claims.tsv, STATUS.md and
  a PruneScan are left to the lead.
* Duplicates for the lead's dedupe at fold time: `UseForm.lean` (moves into TailK); `Kron`, `Split`, `Glue` are
  theta-fold's modules (same constant names, namespaces `IgusaAlgEval`, `…ThetaPt.ThetaSplit`, `…ThetaPt.ThetaGlue`,
  `…ThetaPt.IgusaAlgFinal`): if theta-fold's modules are ever folded too, keep one copy.
* Not attempted: the universal `ThetaRatiosAlgebraic` (not needed by any consumer).

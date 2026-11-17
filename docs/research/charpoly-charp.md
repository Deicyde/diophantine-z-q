# charpoly-charp: the characteristic-`p` use of T7 needs no T7; `charPolyIndepOfEllAlgClosed` is removed (−1, no new leaf)

Task charpoly-charp, 2026-11-16. Base: wip/degpoly-proof `0a9e6698`, merged with origin/main `c1e4ed1b8`.
Scratch: `scratch/charpoly-charp/` (results log `log.md`).

Marks: VERIFIED = read in a source, computed or compiled; STANDARD = published, exact reference; SPECULATIVE =
unchecked. No network: every theorem number recalled from memory is UNVERIFIED.

## 1. Verdict

1. **What `common_trace` needs at the characteristic-`p` field (finding, VERIFIED).** `HDec.G14Trace.common_trace`
   (TailC) used T7 (`PkgI3.CharPolyIndepOfEll`) once: `trace_T_of_frobCompare hM Ab α` gives one integer `t` with
   `N·tr Tm_ℓ(τ) = t` at `ℓ = 3` and `ℓ = 5`, where `FrobTraceLink` supplies `k` (only `CharP k p`), the reduction
   `Ā` and `α' = F̄ ∘ Fr_Ā`. The `ℓ`-independence of `tr(α' | V_ℓ Ā)` is genuinely needed (it is what makes `r₃` and
   `r₅` compatible), and `α'` is not the reduction of a characteristic-0 endomorphism, so the characteristic-0 T7
   cannot be used. **But the hypotheses `common_trace` already has force it**: G8's intertwiners `h5`, `h3` give
   `ℚ̄_ℓ ⊗ V_ℓ(A) ≃ W × W` carrying `ρ_ℓ(τ) = β(τ)⁻¹a(τ)·Tm_ℓ(τ)` to `r_ℓ(τ) ⊕ r_ℓ(τ)`, so through `FrobCompare`
   `V_ℓ(α') ⊗ ℚ̄_ℓ` is conjugate to `M ⊕ M` with `M` a `2 × 2` matrix. Its minimal polynomial is that of `M`, of
   degree `≤ 2`. Mumford §19 Thm 3 (`HomFreeFinite`: `End(Ā)` free of finite rank and `ℤ_ℓ ⊗ End(Ā) → End(T_ℓ Ā)`
   injective) makes this minimal polynomial equal, for every `ℓ ≠ p`, to the minimal polynomial `m ∈ ℚ[X]` of `α'`
   in `End⁰(Ā)`. Then `tr V_ℓ(α') = −(4 / deg m)·(coefficient of X^{deg m − 1} in m)`, one rational number.

2. **`common_trace` is proved without T7 (VERIFIED, compiles, standard axioms).**
   `HDec.G14Trace.common_trace_of_homFree (hH : PkgI3.HomFreeFinite) (hT : PkgI3.TateModuleFree) …` has exactly the
   conclusion and the other hypotheses of `common_trace`. Above it, `g14TraceCompat_of_link_homFree` and
   `HDec.HSyn.G0AssembleMod.linkedTateData_of_local_homFree (hH) (hT) (h : LinkedTateLocal) : LinkedTateData` are the
   originals' proofs with the new lemma. File: `ZInQKernel/Contrib/OneProof/CommonTraceHomFree.lean`.

3. **The other consumer of the field (R16, abelian varieties over `ℚ`) reads only the characteristic-0 case**, which
   degpoly-proof proved (`CharPolyLattice.charPolyIndepOfEllC`, from `uniformizationLeafAll` and
   `mumfordTorsionAlgClosed`). `R16Split.r16_of_printedC (hC : R16CoreY) (HL : UniformizationLeafAll)
   (hM : MumfordTorsionAlgClosed) : R16_EichlerShimuraJ1'` re-proves `r16_of_printed` with T7 only at `ℚ`. File:
   `ZInQKernel/Contrib/OneProof/R16PrintedC.lean`.

4. **The fold removes the field `charPolyIndepOfEllAlgClosed` with no new leaf: open fields −1, strict LEAF −1,
   strict GLUE unchanged.** Every input of the reroute is already in the bundles (`homFreeFiniteAlgClosed` through
   `t6`, `mumfordTorsionAlgClosed` through `t5`/`TateModuleFree`, `uniformizationLeafAll`, which TailZ44 already
   discharges by `uniformizationLeafAll_proof`). autofold cannot express it (the field is not proved; its readers are
   rerouted), so it is a manual fold: `scratch/charpoly-charp/fold_edit.py` (14 files under `OneProof/H/`, §4).
   The fold compiles end to end (§5): `ZInQ.OneProof.frozenTarget` builds with `OpenTextbookLeaves13` lacking the
   field, its closure (268,676 constants) contains no constant named `CharPolyIndepOfEll` or
   `CharPolyIndepOfEllAlgClosed`, and its axioms are the standard three. Count: 37 → 36 H hypotheses, strict
   16/21 → 15/21.

So the task's step (1) succeeds; steps (2)–(3) are not needed and no new leaf is stated.

## 2. The mathematics of the reroute (VERIFIED by the Lean proof)

Setting of `common_trace` at a prime `p ∉ S ∪ {3, 5}` and an arithmetic Frobenius `τ`: `FrobTraceLink` gives a field
`k` of characteristic `p`, `Ā : AbVar k`, `α' ∈ End(Ā)`, `N ≠ 0` and, for `ℓ ∈ {3, 5}`, `Φ_ℓ : ℚ̄_ℓ ⊗ V_ℓ(A) ≃
ℚ̄_ℓ ⊗ V_ℓ(Ā)` with `Φ_ℓ ∘ (N·Tm_ℓ(τ)) ∘ Φ_ℓ⁻¹ = V_ℓ(α') ⊗ ℚ̄_ℓ` (`FrobCompare`). G8's output gives
`e_ℓ : ℚ̄_ℓ ⊗ V_ℓ(A) ≃ ℚ̄_ℓ² × ℚ̄_ℓ²` with `e_ℓ ∘ ρ_ℓ(g) = (r_ℓ(g) ⊕ r_ℓ(g)) ∘ e_ℓ`.

* If `a(τ) = 0` or `β(τ) = 0`, then `ρ_ℓ(τ) = 0`, so `r_ℓ(τ) = 0` and both traces are `j_ℓ(0)`.
* Otherwise `S_ℓ := N·Tm_ℓ(τ)` is conjugate by `e_ℓ` to `M_ℓ ⊕ M_ℓ`, `M_ℓ = N β(τ)a(τ)⁻¹ r_ℓ(τ)`.
* `exists_minpoly_endE`: let `m` be the minimal polynomial over `ℚ` of `1 ⊗ α'` in `End⁰(Ā) = ℚ ⊗ End(Ā)` (finite
  over `ℚ` since `End(Ā)` is finite free). For every `ℓ ≠ p` and every field `E ⊇ ℚ_ℓ` of characteristic `0`, the
  polynomials `G ∈ E[X]` with `G(V_ℓ(α') ⊗ E) = 0` are exactly the multiples of `m`. (⇐) clears the denominators of
  `m` and uses that `End → End⁰` is injective. (⇒) shows that `T_ℓ(α'^i)`, `i < deg m`, are `ℤ_ℓ`-independent
  (injectivity of `ℤ_ℓ ⊗ End(Ā) → End(T_ℓ)` and `ℚ`-independence of the coordinates of `α'^i` in a `ℤ`-basis of
  `End(Ā)`, extended to `ℚ_ℓ` by a left-inverse matrix), then that their matrices stay independent over `ℚ_ℓ`
  (clearing denominators) and over `E` (left inverse again).
* `trace_eq_of_minpoly`: `G(S) = 0 ⟺ G(M) = 0`, so `m = minpoly(M)` divides `charpoly(M)` (degree 2). If
  `deg m = 2`, `m = charpoly(M)` and `tr S = 2 tr M = −2·m₁`; if `deg m = 1`, `M = −m₀·1` and `tr S = −4 m₀`.
  In both cases `tr S = −(4/deg m)·nextCoeff(m)`.
* Hence `N·tr Tm_ℓ(τ) = t := −(4/deg m)·nextCoeff(m) ∈ ℚ` for `ℓ = 3, 5`, and with `2 tr r_ℓ(τ) = tr ρ_ℓ(τ)`,
  `tr r_ℓ(τ) = j_ℓ(½ β(τ)⁻¹ a(τ) t/N)` for one `x ∈ ℚ̄`, which is `common_trace`'s conclusion.

Only Mumford §19 Thm 3 and the structure of `T_ℓ` (I3.M0) are used; the polynomiality of the degree (theorem of the
cube, Riemann–Roch), which deg-det and degpoly-proof found to be the missing input for T7 in characteristic `p`, is
not needed, because the `r ⊕ r` structure bounds the degree of the minimal polynomial by 2. (For a general
endomorphism in characteristic `p` the multiplicities of the eigenvalues are not determined by `ℓ`-adic data;
deg-det §4.)

## 3. Lean

All VERIFIED (Lean 4.35.0, Mathlib v4.35.0), axioms `propext`, `Classical.choice`, `Quot.sound`.

| file | content |
| --- | --- |
| `ZInQKernel/Contrib/OneProof/CommonTraceHomFree.lean` (imports TailC) | linear algebra (`linIndep_map`, `linIndep_baseChange`, `aeval_intertwines`, `trace_eq_of_minpoly`), `endEHom`, `exists_minpoly_endE`, `HDec.G14Trace.trace_r_of_minpoly`, `common_trace_of_homFree`, `g14TraceCompat_of_link_homFree`, `HDec.HSyn.G0AssembleMod.linkedTateData_of_local_homFree` |
| `ZInQKernel/Contrib/OneProof/R16PrintedC.lean` (imports R16Split, CharPolyLattice) | `R16Split.CharPolyIndepOfEllAtQ`, `trace_endV_ratC`, `rank_two_of_dimC`, `r16_of_coreYC` (verbatim copies with the narrowed binder), `r16_of_printedC` |
| `scratch/charpoly-charp/LinAlg.lean`, `Core.lean`, `CommonTrace.lean` | the development steps (Mathlib only; + C10.Link; + TailC) |

## 4. The fold (manual; for the integrator)

`python3 scratch/charpoly-charp/fold_edit.py --tree .` (asserts every match):

1. TailK `gluePieces_of_open4`: `G0AssembleMod.linkedTateData_of_local t.t7 (…)` →
   `G0AssembleMod.linkedTateData_of_local_homFree t.t6 (tateModuleFree_of_t5' t.t5) (…)`; TailK imports
   `ZInQKernel.Contrib.OneProof.CommonTraceHomFree`.
2. Delete `t7 : PkgI3.CharPolyIndepOfEll` from `TextbookLeaves`, `OpenTextbookLeaves` (LPrefix), `OpenTextbookLeaves2`
   (TailE), `OpenTextbookLeaves3` (TailI), `OpenTextbookLeaves4` (TailK) and the pass-through lines `t7 := t.t7`;
   delete the producers `t7 := t7_of_algClosed5 t.charPolyIndepOfEllAlgClosed` (TailN, TailO). After edit 1 no
   declaration on the route reads a T7 field (`t.t7` occurred only in TailK).
3. TailZ35 `openResearchLeaves21_of_OpenResearchLeaves22`: `r16 := R16Split.r16_of_printedC n.r16CoreY
   t.uniformizationLeafAll t.mumfordTorsionAlgClosed`; TailZ35 imports `ZInQKernel.Contrib.OneProof.R16PrintedC`.
4. Delete the field `charPolyIndepOfEllAlgClosed` from `OpenTextbookLeaves5`…`13` (TailN, TailO, TailX, TailZ4,
   TailZ9, TailZ11, TailZ32, TailZ42, TailZ44) and its pass-through lines.

Also needed in the tree: degpoly-proof's `ZInQKernel/Contrib/OneProof/CharPolyLattice.lean` (imported by
`R16PrintedC`). Docs: remove the field's rows (kinds/claims, OPEN.md via render_open); Main's docstring is unchanged.
Theorems that become unused (`t7_of_algClosed5`, `linkedTateData_of_local`, `r16_of_printed`) can stay.

## 5. Fold check (VERIFIED)

* Tree: a reflink copy of this worktree (`~/cc-foldtree`, outside the repository) with
  `fold_edit.py --tree ~/cc-foldtree` applied; the resulting diff is `scratch/charpoly-charp/fold.patch` (14 files).
* `lake build ZInQKernel.OneProof.Main` there: `Build completed successfully (14103 jobs)`; Main's own check prints
  `'ZInQ.OneProof.frozenTarget' depends on axioms: [propext, Classical.choice, Quot.sound]`
  (`scratch/charpoly-charp/fold-build-tail.txt`).
* `scratch/charpoly-charp/FoldCheck.lean` run in that tree (`foldcheck-output.txt`): "OpenTextbookLeaves13 has no
  field charPolyIndepOfEllAlgClosed"; "closure size 268676; T7 / field constants in the closure: []"; the printed
  structure has five fields (`mumfordTorsionAlgClosed`, `homFreeFiniteAlgClosed`, `poincareComplement`,
  `gagaMorphism`, `neronSchemeExtensionExists`); axioms standard. FoldCheck is written for the folded tree: against
  the unfolded tree its `run_cmd` fails by design.
* `#discharges` on this branch (`scratch/charpoly-charp/discharges-output.txt`, with both new modules imported): 45
  open hypotheses, 6730 theorems checked; the new modules discharge no field directly (expected: the field is
  removed by rerouting its readers, not by a proof of its statement), and nothing in them uses `sorry`.
* Not run: the repository's hash guard, `render_open`, docs/kinds/claims updates (integrator steps).

## 6. Leaves

No new leaf. The inputs of the reroute are the open fields `homFreeFiniteAlgClosed` (Mumford §19 Thm 3, already
a field, through `t6_of_algClosed5`), `mumfordTorsionAlgClosed` (through `TateModuleFree`) and the proved
`uniformizationLeafAll_proof`. degpoly-proof's count-neutral discharges (`CharPolyIndepOfEllAlgClosedNoEmb`,
`DegHomogPolyNoEmb`) are superseded: with this fold neither the field nor any narrowing of it is needed.

# charpoly-hf: the characteristic-`p` input is one fact about one endomorphism; it needs a discreteness theorem the tree lacks, so −1 is not reached; a verified swap Thm 4 → Thm 3 (char `p`)

Task charpoly-hf, 2026-11-16. Base wip/leaf-fold33b `968b59ef8` (origin/main `c1e4ed1b8` is already an ancestor).
Scratch: `scratch/charpoly-hf/` (results log `log.md`). Model work, no human review.

Marks: **VERIFIED** = read in a named file on this host, computed, or compiled. **STANDARD** = published, with an
exact reference. **SPECULATIVE** = unchecked. There was no network: theorem numbers recalled from memory are
**UNVERIFIED**.

## 1. Verdict

1. **What charpoly-charp's argument reads at `Ā` (VERIFIED, Lean).** At FrobTraceLink's abelian variety `Ā` over a
   field `k` of characteristic `p`, it reads exactly one fact about the one endomorphism `α'`. There is a monic
   `m ∈ ℚ[X]` such that, for every prime `ℓ ≠ p`, the polynomials over `ℚ_ℓ` that kill `V_ℓ(α')` are the multiples of
   `m`. Equivalently, `ℚ_ℓ ⊗_ℚ ℚ[α'] → End(V_ℓ Ā)` is injective, with `m` the minimal polynomial of `α'` in
   `End⁰(Ā)`. It does not read the rest of Mumford §19 Thm 3: freeness of `End(Ā)`, the rank bound, or injectivity on
   all of `ℤ_ℓ ⊗ End(Ā)`. The fact is stated as `CharpolyHF.MinpolyIndepOfEllCharP`.
   `common_trace`, `g14TraceCompat_of_link` and `linkedTateData_of_local` are re-proved from it and from I3.M0
   (`PkgI3.TateModuleFree`, already on the route through `t5`). Axioms: `propext`, `Classical.choice`, `Quot.sound`.

2. **The target "−1, no new leaf" is not reachable from the listed inputs (finding).** The listed inputs are:
   - faithfulness of `T_ℓ`;
   - divisibility ("`φ` kills `Ā[ℓ]` ⇒ `φ ∈ ℓ End(Ā)`");
   - `mumfordTorsionAlgClosed` (`T_ℓ` free of rank `2g`);
   - integrality of `α'`;
   - G8's `M ⊕ M` structure at `ℓ = 3, 5`.

   Even all of them together do not imply the fact in 1. §3 gives an explicit model, built from `ℚ(ζ₈)`, in which
   every one of them holds and the traces at `ℓ = 3` and `ℓ = 5` differ. What is missing is a *discreteness* input:
   `ℚ[α'] ∩ End(Ā)` must be a finitely generated group. Mumford obtains this from the polynomiality of `deg` on
   `End(Ā)` (§19; homfree-proof §4.2 reached the same conclusion for all of Thm 3). No bundle field and no proved
   tree result gives it in characteristic `p`. So the input is isolated as the smallest named Prop
   (`MinpolyIndepOfEllCharP`, rated in §6). It is proved to follow from a printed form of Mumford §19 Thm 3 restricted
   to characteristic `p` (`HomFreeFiniteAlgClosedCharP`), together with I3.M0.

3. **A verified count-neutral fold (a swap, not a removal).** The field `charPolyIndepOfEllAlgClosed` (Mumford §19
   Thm 4 over every algebraically closed field) is replaced by `homFreeFiniteAlgClosedCharP` (Mumford §19 Thm 3 over
   algebraically closed fields of characteristic `p > 0`, printed form restricted). After the swap:
   - the characteristic-`0` reader of T7 (R16) uses degpoly-proof's characteristic-`0` proof;
   - the characteristic-`p` reader (`common_trace`) uses the reroute of 1.

   Counts (render_open): 40 open hypotheses and **33 H, strictest 13/20**, unchanged. This was checked by
   build, FoldCheck, the hash guard, a blueprint-target check, OpenStatements, `render_open --check` and the
   crosswalk check. It also composes with fold33-combine (§5). Whether to apply it is the lead's choice, because it
   does not lower the count. What it buys:
   - Thm 4 is replaced by a theorem that precedes it in Mumford, and the hypothesis is now used only in
     characteristic `p`;
   - the leaf can be narrowed further to `MinpolyIndepOfEllCharP` (one line in `fold_edit.py`) if the project prefers
     the smallest statement to a printed one.

## 2. What the reroute reads (VERIFIED by the Lean proof)

charpoly-charp (`docs/research/charpoly-charp.md` §2, on wip/charpoly-charp) proves `common_trace` as follows.
- FrobTraceLink gives `Φ_ℓ` with `Φ_ℓ ∘ (N·Tm_ℓ(τ)) ∘ Φ_ℓ⁻¹ = V_ℓ(α') ⊗ ℚ̄_ℓ` for `ℓ = 3, 5` (`FrobCompare`).
- G8's intertwiner conjugates `N·Tm_ℓ(τ)` to `M_ℓ ⊕ M_ℓ` with `M_ℓ` a `2 × 2` matrix.
- If the polynomials killing `V_ℓ(α') ⊗ ℚ̄_ℓ` are the multiples of one `m ∈ ℚ[X]`, then `m = minpoly(M_ℓ)` has
  degree `≤ 2`, and `tr V_ℓ(α') = −(4/deg m)·nextCoeff(m)`. This is one rational number for both `ℓ`
  (`trace_eq_of_minpoly`).

charpoly-charp derived that hypothesis from `PkgI3.HomFreeFinite` at `Ā` (`exists_minpoly_endE`). On this base the
Thm 3 field is gone: homfree-noemb keeps Thm 3 only over fields with a ring homomorphism to `ℂ`, which a field of
characteristic `p` does not have.

`FrobTraceLink` (TailC L8674, VERIFIED) is existential in `(k, Ā, α')`. Its only constraints are `CharP k p` and
`FrobCompare` at `3` and `5`. So no special property of `α'` (Frobenius type, reduction of something) is available
to the consumer, and the hypothesis has to hold for an arbitrary endomorphism of an arbitrary abelian variety in
characteristic `p`.

The reduction from `ℚ_ℓ` to `E = ℚ̄_ℓ` is linear algebra, proved here (`minpoly_baseChange_iff`): the minimal
polynomial of an endomorphism of a finite-dimensional space does not change under extension of scalars. That is
why the statement is over `ℚ_ℓ`, on the genuine `V_ℓ(α) = ℚ_ℓ ⊗ T_ℓ(α)`.

## 3. Why the listed inputs do not suffice (argument; the model is explicit, SPECULATIVE only in that it is not in Lean)

The task suggested proving the fact from the following inputs:
- (a) `T_ℓ` faithful (`T_ℓ(φ) = 0 ⇒ φ = 0`);
- (b) divisibility (`T_ℓ(φ) ∈ ℓ End(T_ℓ)` ⇒ `φ = ℓψ` with `ψ ∈ End`);
- (c) `T_ℓ` free of rank `2g` (`mumfordTorsionAlgClosed`, I3.M0);
- (d) `α'` integral over `ℤ`.

Add G8's structure:
- (e) `V_ℓ(α') ⊗ ℚ̄_ℓ ≅ M_ℓ ⊕ M_ℓ` at `ℓ = 3, 5`.

No proof can use only (a)–(e), because there is a model of all of them in which the traces differ.

Model. Let:
- `F = ℚ(ζ₈)` and `α' = ζ₈` (integral, `α'^4 = −1`);
- `w₃` be one of the two places of `F` over `3` (degree 2; decomposition group `{1, ζ ↦ ζ³}`), and `w₅` one of the
  two places over `5` (decomposition group `{1, ζ ↦ ζ⁵}`);
- `R = 𝓞_F[1/𝔭]`, where `𝔭` runs over the other place over `3` and the other place over `5`.

Then `R` is a subring of `F` containing `α'`, and it is not finitely generated as a group. Define the lattices:
- `T₃ = 𝓞_{F_{w₃}}²`, with `R` acting through `F ↪ F_{w₃}`;
- `T₅ = 𝓞_{F_{w₅}}²`, with `R` acting through `F ↪ F_{w₅}`;
- `T_ℓ = 𝓞_F ⊗ ℤ_ℓ` for every other `ℓ`.

Each is free of rank 4 over `ℤ_ℓ`, which gives (c) with `g = 2`.
- (a) holds because each action is induced by a field embedding.
- (b) holds because `R` is integral exactly at `w₃`, at `w₅` and at the primes `≠ 3, 5`.
- (e) holds. On `V₃ ⊗ ℚ̄₃`, `α'` has eigenvalues `ξ, ξ³` (`ξ` a primitive 8th root of unity), each twice, which is
  `M ⊕ M` with `M = diag(ξ, ξ³)`. On `V₅ ⊗ ℚ̄₅` the eigenvalues are `ξ', ξ'⁵ = −ξ'`, each twice.

The traces are `2(ξ + ξ³) = ±2√−2` at `ℓ = 3` and `2(ξ' − ξ') = 0` at `ℓ = 5`. So there is no `x ∈ ℚ̄` with
`tr r₃(τ) = j₃(x)` and `tr r₅(τ) = j₅(x)`, which is `common_trace`'s conclusion.

What the model violates is finite generation: `ℚ[α'] ∩ End = R` is not a lattice. With `End(Ā)` (or just
`ℚ[α'] ∩ End(Ā)`) finitely generated, (a)–(c) do give the injectivity, by Mumford's argument. Let `R'` be the
saturation of `ℤ[α']`. Then:
- `R'/ℓR' ↪ End(Ā[ℓ])` by (b);
- hence `ℤ_ℓ ⊗ R' ↪ End(T_ℓ)` by a Nakayama-type step.

So the essential missing input is the discreteness, which Mumford proves from "`deg` is a polynomial function on
`End(Ā)`" (Mumford §19, the lemma before Thm 3; locator UNVERIFIED). The other inputs are also absent in
characteristic `p` (not examined in detail, since the model makes them insufficient anyway):
- faithfulness needs density of `ℓ`-power torsion;
- divisibility needs the quotient `Ā/Ā[ℓ] ≅ Ā`. `milneIsogenyQuasiInverse` gives `g ∘ f = [deg f]`, not a
  factorization through `[ℓ]` (homfree-proof §4.2, VERIFIED there);
- integrality of an arbitrary endomorphism is itself Thm 4-type information.

This agrees with homfree-proof §4.2 (finite generation needs archimedean input) and with fold33-combine §2.

## 3a. A reduction that is not made

`MinpolyIndepOfEllCharP` could be split further into three named Props, all in characteristic `p` and all absent from
the tree:
- (P-fg) the saturation of `ℤ[α]` in `End(A)` is finitely generated;
- (P-div) divisibility by `ℓ`;
- (P-faith) faithfulness of `T_ℓ`.

With I3.M0 they imply the fact in 1, by the argument above. Each is a published lemma of Mumford's §19 proof
(UNVERIFIED locators). The split would raise the count by two. Only (P-fg) carries the depth (§3), so it is
recorded here and not formalized.

## 4. Lean (VERIFIED: Lean 4.35.0, Mathlib v4.35.0; axioms `propext`, `Classical.choice`, `Quot.sound`, `scratch/charpoly-hf/axioms_out.txt`)

| file | content |
| --- | --- |
| `ZInQKernel/Contrib/OneProof/MinpolyIndepCharP.lean` (imports TailC) | `ZInQ.Contrib.OneProof.CharpolyHF.MinpolyIndepOfEllCharP` (statement); charpoly-charp's linear algebra (`linIndep_map`, `linIndep_baseChange`, `aeval_intertwines`, `trace_two`, `trace_eq_of_minpoly`, copied); `powIndep_of_minpoly`, `eq_zero_of_aeval_baseChange`, `minpoly_baseChange_iff`, `exists_minpoly_endE_charP`; `HDec.G14Trace.trace_r_of_minpolyQ`, `common_trace_of_minpolyCharP`, `g14TraceCompat_of_link_minpolyCharP`; `HDec.HSyn.G0AssembleMod.linkedTateData_of_local_minpolyCharP (hM) (hT : PkgI3.TateModuleFree) : LinkedTateLocal → LinkedTateData` |
| `ZInQKernel/Contrib/OneProof/MinpolyIndepCharPThm3.lean` | `CharpolyHF.HomFreeFiniteAlgClosedCharP` (Mumford §19 Thm 3, `k` algebraically closed of characteristic `p`); `exists_minpoly_V` (charpoly-charp's `exists_minpoly_endE` at `E = ℚ_ℓ`, with the hypotheses at one abelian variety); `minpolyIndepOfEllCharP_of_homFree (hH : HomFreeFiniteAlgClosedCharP) (hT : PkgI3.TateModuleFree) : MinpolyIndepOfEllCharP` (descent `k̄ → k` as in av-b1's `homFreeFinite_of_algClosed`) |
| `ZInQKernel/Contrib/OneProof/CharPolyLattice.lean`, `R16PrintedC.lean` | copied verbatim from wip/charpoly-charp (degpoly-proof's `charPolyIndepOfEllC`; charpoly-charp's `R16Split.r16_of_printedC`, T7 only at `ℚ`), needed by the fold |
| `scratch/charpoly-hf/MinpolyCharP.lean`, `Consequence.lean` | the development copies (same proofs) |

Every module builds (`lake build`, 11765 jobs). `#discharges` on this branch (`discharges_out.txt`) reports 40 open
hypotheses, 9222 theorems checked and 49 discharge lines, and no `sorry`. The new modules discharge no field
directly, as expected for a reroute. The copied `CharPolyLattice` brings degpoly-proof's count-neutral
`charPolyIndepOfEllAlgClosed_of_noEmb`.

Pitfall found (VERIFIED): `Fintype.linearIndependent_iff.mp h` timed out (`whnf`) for a family in
`Module.End E (E ⊗[K] W)`. Giving `(R := E) (v := …)` explicitly fixed it.

## 5. The fold (manual; for the integrator)

`python3 scratch/charpoly-hf/fold_edit.py --tree .` asserts every match. On the route, the field is read only in
homfree-noemb's copies and in TailZ48. VERIFIED by `Taint.lean` → `taint_out.txt`: 65 tainted constants, 61 of them
in the reroute module, 3 in TailZ48, and `frozenTarget`.

1. `Contrib/OneProof/HomFreeFiniteAlgClosedReroute.lean`:
   - imports `MinpolyIndepCharPThm3` and `R16PrintedC`;
   - `t7` of `TextbookLeavesHF` and `OpenTextbookLeaves2HF`–`4HF` is retyped `CharpolyHF.MinpolyIndepOfEllCharP`;
   - `gluePieces_of_open4_hf` calls `linkedTateData_of_local_minpolyCharP t.t7 (tateModuleFree_of_t5' t.t5)`;
   - `textbookLeaves4_of_open6_hf` sets
     `t7 := minpolyIndepOfEllCharP_of_homFree t.homFreeFiniteAlgClosedCharP (tateModuleFree_of_t5' (torsionStructure_ofK5 t.t5))`;
   - in `OpenTextbookLeaves6HF`–`14HF`, the field `charPolyIndepOfEllAlgClosed` becomes
     `homFreeFiniteAlgClosedCharP : CharpolyHF.HomFreeFiniteAlgClosedCharP`, with its 8 pass-through lines;
   - `openResearchLeaves21_of_OpenResearchLeaves22_hf` sets
     `r16 := R16Split.r16_of_printedC n.r16CoreY uniformizationLeafAll_proof t.mumfordTorsionAlgClosed`.
2. `OneProof/H/TailZ48.lean`: the same field rename in `OpenTextbookLeaves15` and its pass-through.
3. Optional: a later generation above TailZ48 that carries the field, such as fold33-combine's TailZ49
   (`OpenTextbookLeaves16`), gets the same rename.
4. Docs (`scratch/charpoly-hf/fold-docs.patch`):
   - `kinds.tsv`: the row is renamed, with source "Mumford 19 Thm 3 (specialization: k algebraically closed of
     characteristic p > 0)", kind published, strict LEAF;
   - `claims.tsv`: the old field's claim row is dropped;
   - `open-statements.json`, `OPEN.md` and `frontier-crosswalk.tsv` are regenerated (H-71 loses its field);
   - `scratch/contrib-kit/DischargesTest.lean` is rerun, and `render_open.py` updates the worked example in
     `CONTRIBUTING.md`.

The original `OpenTextbookLeaves13.charPolyIndepOfEllAlgClosed`, which the blueprint page
`abelian-varieties/characteristic-polynomial.md` names, stays in place, off the route. No existing declaration is
deleted except the 10 renamed projections of `OpenTextbookLeaves6HF`–`14HF` and `OpenTextbookLeaves15`.
The patch is `scratch/charpoly-hf/fold.patch` (`git apply --check` passes on this branch).

Checks, all VERIFIED in `~/chf-foldtree`, a reflink copy of this worktree without `.git`, outside the repository:
- `lake build ZInQKernel.OneProof.Main` succeeds (14192 jobs), and `frozenTarget` uses only the standard three
  axioms.
- `scratch/charpoly-hf/FoldCheck.lean` (`foldcheck_out.txt`):
  - `OpenTextbookLeaves15 = {mumfordTorsionAlgClosed, homFreeFiniteAlgClosedCharP, gagaMorphism,
    neronSchemeExtensionExists}`;
  - `frozenTarget`'s closure (270,888 constants) contains none of `AVB1.CharPolyIndepOfEllAlgClosed`,
    `PkgI3.CharPolyIndepOfEll`, `AVB1.HomFreeFiniteAlgClosed`, `PkgI3.HomFreeFinite`,
    `HomFreeFiniteAlgClosedNoEmb`, `t7_of_algClosed5`, `OpenTextbookLeaves13.charPolyIndepOfEllAlgClosed` or
    `sorryAx`, and no constant whose name ends in `CharPolyIndepOfEll`;
  - the blueprint target still exists.
- Hash guard (`DumpCompact.lean`, extended to the reroute module; `hashdiff.txt`): 14501 → 14501 constants.
  - Only before (10): the old projections.
  - Only after (10): the new projections.
  - Changed (86): the constructor families of the 14 carrier structures, the `t7` projections, the three readers
    and the pass-through conversions.
  - `frozenTarget`'s hash is unchanged, because constants are referenced by name.
- Blueprint targets (`BlueprintNames.lean`): 2531 `lean:` names. The same 117 are missing from Main's environment
  before and after the fold, so the fold deletes no target. This substitutes for autoform, which is not installed
  here.
- OpenStatements gives 40 open hypotheses, and `render_open.py` gives "33 H hypotheses, strictest 13/20, 7 others".
  `render_open.py --check` and `frontier_crosswalk.py --check` both report ok.
- Composition with fold33-combine (0e516baa, not yet in leaf-fold33b): `fold_edit.py` was applied to a copy of that
  tree plus the four new modules. Main builds (14178 jobs), frozenTarget uses the standard axioms, and FoldCheck
  passes (closure 270,455; `foldcheck_combine_out.txt`).
- Not run: autoform, and homfree-noemb's generator. The reroute module now carries hand edits, so after a
  regeneration `fold_edit.py` has to be rerun.

## 6. Leaves

- **New field `homFreeFiniteAlgClosedCharP`: printed form.** It is Mumford, *Abelian varieties* (1970), §19,
  Theorem 3 (locator UNVERIFIED), stated verbatim under the book's standing hypothesis that `k` is algebraically
  closed, and restricted to `char k = p > 0`. The statement is the same as av-b1's `HomFreeFiniteAlgClosed` with the
  hypotheses `p.Prime` and `CharP k p` added. It is true, and not vacuous beyond the usual absence of nonzero
  abelian varieties in Mathlib. It is weaker than homfree-proof's `HomFreeFiniteAlgClosedNoEmb`.
- **Smallest statement `MinpolyIndepOfEllCharP`: not printed form.** It is a consequence of Thm 3 together with I3.M0
  (Mumford §4; `minpolyIndepOfEllCharP_of_homFree`, compiled). Mumford states injectivity on all of
  `ℤ_ℓ ⊗ Hom(X, Y)`. This statement is its restriction to `ℤ_ℓ ⊗ ℤ[α]`, phrased by minimal polynomials, and only in
  characteristic `p`. It is true: with `m` = the minimal polynomial in `End⁰` (for the zero abelian variety,
  `m = 1`).
- **Removed: `charPolyIndepOfEllAlgClosed`** (Mumford §19 Thm 4, consequence over algebraically closed fields).
- Formalization difficulty, honestly. In Mumford, Thm 3 comes before Thm 4, and (from memory, UNVERIFIED) Thm 4's
  proof uses Thm 3. But both rest on the polynomiality of `deg` (theorem of the cube, Riemann–Roch §16) in
  characteristic `p`. So the swap removes the `det = deg` step and every characteristic-`0` use; it does not remove
  that common core.

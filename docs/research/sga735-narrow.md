# sga735-narrow: the field `sga7_IX_3_5_ForwardGeom` restricted to algebraically closed residue fields

Task sga735-narrow, 2026-11-16/17. Base `wip/leaf-fold33b` 0e3c3125 (origin/main was already merged). No human has
reviewed this; it is model work. Marks: **VERIFIED** = compiled, computed, or read in a file. **STANDARD** = published,
with an exact reference. **SPECULATIVE** = a judgement. **UNVERIFIED** = a theorem number recalled without a source
(this host has no network).

## 1. Verdict

**Partial. Reading (a) is removed, reading (b) is not, and the strict GLUE count does not change under the current
flag policy. It drops by 1 as soon as one display is read.**

* **(a) The `k(s)` definition of semistable: removed.** The field has one use in the chain. That use is r6 at number
  fields, and after strict henselization inside `K̄` its residue field is algebraically closed (§2, VERIFIED by a
  taint computation). So the field can be replaced by its restriction to strictly henselian DVRs whose residue
  field is algebraically closed: `SGA735AC.SGA7_IX_3_5_ForwardGeomAC`. That is the field word for word with
  `[IsAlgClosed (IsLocalRing.ResidueField O)]` added. With `k(s) = κ̄` the two definitions of semistable agree
  (`UnipotentForward.hasSemistableReductionRes_iff`, already proved). So the restricted leaf follows from the print
  under either definition: `forwardGeomAC_of_forwardGeom` and `forwardGeomAC_of_forwardRes` (VERIFIED, compiled).
  `SemiAbelianDescendsSepClosed` is not needed at all.
* **(b) The echelon clause: open.** The Lean conclusion `(σ - 1)² = 0` is the echelon clause at `σ = τ`. The task
  allowed three ways to handle it, and none of them works here:
  * **Prove it from the rest.** Not possible. It needs Grothendieck's orthogonality theorem (IX 2.4) and the rank
    computations of IX §2. sga7-35-proof showed these are not available. "Unipotent" alone does not bound the
    nilpotence index at 2.
  * **Drop it from the field.** Not possible, because a use reads it. The ℓ = 3 quaternion consumer
    `HDec.PkgI2.quatUnipotentTrivial` (LPrefix.lean L702-773; the A6 route `goodReduction_of_QM_rational3`) takes
    `S (S x) * (S x)⁻¹ * (S x)⁻¹ * x = 1` on `G[3^{2k}]` as a hypothesis, and its valuation step `c² = 0 ⇒ 3^k | c`
    uses the square (§5). The D2 / wild-inertia consumers (`fixed_of_unipSq_of_iterate`) would accept any nilpotence
    index, but this one would not.
  * **Split it off as an IX 2.4 leaf.** This does not keep the count down. An IX 2.4 leaf in Lean would need IX §2's
    rank glue, which makes it a consequence (sga7-35-proof's `GrothendieckOrthogonalitySS` is rated GLUE for that
    reason). Its print is also unread.
* **Count.** The fold (§4) replaces the row `sga7_IX_3_5_ForwardGeom` (published, GLUE/GLUE, two pending readings)
  with `sga7_IX_3_5_ForwardGeomAC`. The new row keeps only reading (b). The proposed flag is "pending reading: ...", so
  the row counts GLUE, and strict and strictest stay at 13/20 on 33. **No new GLUE: the glue the fold uses is proved
  in Lean.** The new leaf is a specialization of the old field (`forwardGeomAC_of_forwardGeom`), so the fold never
  makes the chain's assumptions stronger.
* **What would give −1.** A reading of the display of SGA 7 I, Exp. IX, Prop. 3.5. If it contains the echelon clause
  ("unipotent d'échelon ≤ 2", or `(σ-1)(τ-1) = 0`, as gt-unip, unipotent-b and pkg-I2 recall it), the new row
  becomes printed form (restricted) and counts LEAF: strict 13/20 → 14/19 and strictest 13/20 → 14/19. The old field
  would still be GLUE after that reading, because of reading (a). So this fold is the step that turns a reading of
  3.5 into −1. If the display has no echelon clause, the route in §6 applies.

## 2. Chain uses (step 1; VERIFIED, computed)

`scratch/sga735-narrow/Taint.lean` is homfree-noemb's taint metaprogram with these seeds: the projections
`sga7_IX_3_5_ForwardGeom` and `semistableUnipotent`, the latter being what TailZ33 converts the field into. It runs
over the closure of `HDec.HSyn.sixContactMin_of_open41` (241,701 constants), and its output is `taint_out.txt`.
58 constants are tainted. The carriers are `OpenResearchLeaves14`–`29`. Besides the pass-through `x := n.x`, the
projections are read in exactly two places, both in homfree-noemb's live reroute
(`ZInQKernel/Contrib/OneProof/HomFreeFiniteAlgClosedReroute.lean`):

| read | term | where it is applied |
| --- | --- | --- |
| `openResearchLeaves19_of_OpenResearchLeaves20_hf` (L1667) | `semistableUnipotent := UnipotentForward.semistableUnipotent_of_forwardGeom n.sga7_IX_3_5_ForwardGeom …` | the only read of the field |
| `raynaudCriterionNF_of14_hf` (L1493) | `GapNeron.raynaudCriterion_leavesNF … r.semistableUnipotent …`, proving `PkgI2.RaynaudCriterionNF` (r6 at number fields) | `hU` applied at `K` a **number field**, `O` any DVR of `K` (residue field finite, so perfect), `Ω = K̄`. Through `unipotentFromSH_of`, the field is applied at the inertia field `E` of `w`. There the residue field is algebraic over the finite `k(O)` and separably closed, so it is algebraically closed. `K` has characteristic 0. |

The TailZ originals (TailZ33 L101, TailZ26 L171) are no longer in the closure: Main goes through the `_hf` copies.

## 3. Lean (VERIFIED: compiled, standard axioms)

`ZInQKernel/Contrib/OneProof/SGA7IX35ForwardAC.lean` (namespace `SGA735AC`) imports `UnipotentForward`, which
defines the statement, and `NeronDVR`. It does not import Main.

* `SGA7_IX_3_5_ForwardGeomAC`: the new leaf.
* `forwardGeomAC_of_forwardGeom : UnipotentForward.SGA7_IX_3_5_ForwardGeom → SGA7_IX_3_5_ForwardGeomAC`
  (a specialization).
* `SGA7_IX_3_5_ForwardRes`: the `k(s)` reading over the same bases. With it,
  `forwardGeomAC_of_forwardRes : SGA7_IX_3_5_ForwardRes → SGA7_IX_3_5_ForwardGeomAC`.
* `forwardGeomAC_of_forward`: the same from gt-unip's reading-robust `SGA7_IX_3_5_Forward`.
* `SemistableUnipotentCP`: `ReductSplit.SemistableUnipotent` with `[PerfectField k(O)]` added. With it,
  `semistableUnipotentCP_of_forwardGeomAC (hP) (hE : MulEtaleAbelianScheme)
  (hN : NeronBaseChangeStrictHenselization) : SemistableUnipotentCP`. This is the old proof with the instances
  carried to the inertia field: perfect by `Algebra.IsAlgebraic.perfectField`, then algebraically closed by
  `IsSepClosed.isAlgClosed_of_perfectField`.
* `raynaudCriterion_leavesNF_cp (hR) (hU : SemistableUnipotentCP) (hN) (hM) (hE) : GapNeron.RaynaudCriterionNF`:
  neron-dvr's proof plus one `haveI` (`perfectField_residue_nf`). Also `raynaudCriterionNF_of_forwardGeomAC`
  (everything at once).

`#print axioms` gives `[propext, Classical.choice, Quot.sound]` for each of these (VERIFIED). `scratch/sga735-narrow/Statement.lean`
checks the verbatim copy of the field statement against `UnipotentForward.SGA7_IX_3_5_ForwardGeom` by `rfl`.

## 4. The fold (manual; autofold cannot express it)

The new leaf is weaker than the field, so no term of the field's type comes from it, and `autofold.py` cannot write
the fold. This is the sga33-shpre / homfree-noemb bypass pattern. `scratch/sga735-narrow/gen/gen.py` uses
homfree-noemb's `copylib.py` and reads the taint list. It writes `scratch/sga735-narrow/FoldCheck.lean`:

* 65 copied blocks: 16 carriers, 41 tainted theorems and 8 theorems whose type mentions a carrier. Each is copied
  verbatim up to the renaming `X ↦ X_sg` / `XSG`.
* In generations 20–28 the field becomes `sga7_IX_3_5_ForwardGeomAC : SGA735AC.SGA7_IX_3_5_ForwardGeomAC`. Generation
  29's copy is the new top bundle `HDec.HSyn.OpenResearchLeaves30`.
* In generations 14–19, `semistableUnipotent : SGA735AC.SemistableUnipotentCP`.
* Two lines are edited: the conversion (`semistableUnipotent := SGA735AC.semistableUnipotentCP_of_forwardGeomAC …`)
  and the consumer (`SGA735AC.raynaudCriterion_leavesNF_cp …`).
* The top theorem is `HDec.HSyn.sixContactMin_of_open42 (r : OpenResearchLeaves30) (t : OpenTextbookLeaves15)
  (l : OpenAddedLeaves20) : ZInQ.SixContactMin`. The fold adds constants only.

The fold compiles (§7).

The integrator's steps:
1. Copy FoldCheck.lean to `ZInQKernel/OneProof/H/TailZ49.lean`, or regenerate it with gen.py on the integration
   tree after re-running Taint.lean.
2. Switch Main to `sixContactMin_of_open42`.
3. Replace the kinds.tsv row with `scratch/sga735-narrow/kinds-row-proposed.tsv`.
4. Regenerate OPEN.md.

sga33-shpre's fold (also not in this base) copies an overlapping set of generations. Folding both means regenerating
one of them on top of the other, and both generators are taint-driven, so that is mechanical.

## 5. The new leaf and its rating

```lean
def SGA735AC.SGA7_IX_3_5_ForwardGeomAC : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [IsAlgClosed (IsLocalRing.ResidueField O)], IsStrictlyHenselianDVR O →
    ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (w : ValuationSubring Ω),
    w.comap (algebraMap K Ω) = O → ∀ A : PkgI3.AbVar K,
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : O) → HasSemistableReduction A O →
      ∀ σ : Ω ≃ₐ[K] Ω, IsInertia w σ → (galTΩ A ℓ σ - 1) * (galTΩ A ℓ σ - 1) = 0
```

**Rating: printed form (restricted) as far as reading (a) goes. Reading (b) is still pending, so it counts GLUE
today.**

* Base and residue field: a specialization of the print under every reading of "semistable". The `k(s)` and
  geometric definitions coincide for algebraically closed `k(s)`, and that is proved in Lean.
* `K^s`, inertia, `T_ℓ = lim A(K^s)[ℓⁿ]`, one `σ` at a time: unchanged from the field. The statement review of
  11-15 found these to be dictionary.
* Echelon clause: the conclusion `(σ-1)² = 0` is printed only if the display of 3.5 contains the echelon clause
  (UNVERIFIED; recalled by gt-unip, unipotent-b and pkg-I2, and the statement review of 11-15 said yes). If the
  display only says "I acts unipotently", the leaf is a consequence of 3.5 together with IX 2.4.

Proposed kinds row: `scratch/sga735-narrow/kinds-row-proposed.tsv`. The flag reads "pending reading: one recorded
reading makes it a consequence (no echelon clause in 3.5, through IX 2.4); the k(s) reading is removed by the
restriction to algebraically closed residue fields". The flag class is `pending-reading,restricted,unverified-locator`.
The row is GLUE/GLUE. If the display is read and contains the clause, the flag becomes "restricted: algebraically
closed residue field, a specialization of the print under both definitions of semistable; locator UNVERIFIED", and
the row becomes LEAF/LEAF.

## 6. What remains for (b) if 3.5 has no echelon clause (SPECULATIVE plan, not done)

1. Re-type r6 (`RaynaudCriterionNF`) to a nilpotent conclusion. For abelian surfaces `(σ - 1)^4 = 0` on
   `A[ℓⁿ]`. It follows from "unipotent" on `T_ℓ` because `T_ℓ` is free of rank 4 (`tateModuleFree_of_t5'`) and a
   nilpotent endomorphism of a free rank-`r` module over a domain has `N^r = 0`.
2. Re-prove `fixed_of_unipSq_of_iterate` for any nilpotence index. Write `(1+D)^q - 1 = D·(q + D w(D))`. With `q`
   prime to `ℓ`, the second factor is invertible on `ℓ`-power torsion.
3. Re-prove `quatUnipotentTrivial` with `c⁴ = 0` at torsion level `3^{4k}`. This needs a new valuation lemma
   generalizing `quat_sq_dvd`: `v_Π(3) = 2` in the maximal order at 3.
4. Thread the re-typed r6 through its 31 or so consumer theorems. Most of them only transport `UnipSq` along
   isomorphisms.

This is several days of work with one Lean process, which is why it was not attempted. It adds no leaf.

## 7. Check outputs (all VERIFIED on this host)

* `lake build ZInQKernel.Contrib.OneProof.SGA7IX35ForwardAC` completed (12,815 jobs, on the build tree of
  leaf-fold33b at the same commit). `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for
  `forwardGeomAC_of_forwardGeom`, `forwardGeomAC_of_forwardRes`, `semistableUnipotentCP_of_forwardGeomAC` and
  `raynaudCriterionNF_of_forwardGeomAC`.
* `lake env lean scratch/sga735-narrow/FoldCheck.lean`: no errors in 75 s
  (`foldcheck_out.txt`). `'HDec.HSyn.sixContactMin_of_open42' depends on axioms: [propext, Classical.choice,
  Quot.sound]`.
  * Two generator pitfalls came up along the way. First, copylib emits each block's scope commands at top level, so
    later blocks inherited `open … MonObj` / `open NumberField` (scoped instances). Two `_hf` maps then hit
    `isDefEq` heartbeat timeouts, even at 1,000,000. The fix is to wrap each block in `section … end`.
  * Second, the file-level `set_option maxHeartbeats 1000000` that was added before that fix is kept, and is
    harmless.
* `Statement.lean`: compiles with no output. It contains the verbatim copy `= UnipotentForward.SGA7_IX_3_5_ForwardGeom`
  by `rfl`, and the two derivations of the new leaf.
* `#discharges` (`Discharges.lean`, output `discharges.txt`, 48 DISCHARGES lines): **none comes from the new
  file**, as expected. The new leaf is weaker than the field, so no theorem has the field's type. The only line on
  the field is gt-unip's existing `UnipotentForward.forwardGeom_of_forward`, which still assumes
  `SGA7_IX_3_5_Forward` and `SemiAbelianDescendsSepClosed`.
* Counts on kinds.tsv (python, the counting of `autofold.py`): before, 33 fields, strict 13/20, strictest 13/20.
  * After, with `kinds-row-proposed.tsv`: 33 fields, strict 13/20, strictest 13/20. Both proposed rows pass
    `render_open.kinds_row_problems`.
  * After, with `kinds-row-if-echelon-read.tsv`: strict 14/19, strictest 14/19.

## 8. Files

* `ZInQKernel/Contrib/OneProof/SGA7IX35ForwardAC.lean`: the contribution.
* `scratch/sga735-narrow/`:
  * `Taint.lean`, `taint_out.txt`: the chain uses.
  * `gen/gen.py`, `gen/copylib.py` (homfree-noemb's), `gen/header.lean`: the generator.
  * `FoldCheck.lean`, `foldcheck_out.txt`: the fold.
  * `fold-spec.json`: the manual fold spec in autofold's format, with a BYPASS proof.
  * `kinds-row-proposed.tsv`, `kinds-row-if-echelon-read.tsv`.
  * `Statement.lean`, `Discharges.lean`, `discharges.txt`, `log.md`.

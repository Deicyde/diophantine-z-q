# sga735-finish: `sga7_IX_3_5_ForwardGeom` with neither pending reading

Task sga735-finish, 2026-11-16/17. Base: main c0f3d085 (leaf-fold33b, top `sixContactMin_of_open48`), with
sga735-narrow (a83c9b93) merged in for its `SGA7IX35ForwardAC.lean`. This is model work and no human has reviewed it.
Marks: **VERIFIED** means compiled, computed, or read in a file. **STANDARD** means published, with an exact
reference. **SPECULATIVE** means a judgement. **UNVERIFIED** means a theorem number recalled without a source (this
host has no network).

## 1. Result

**Done. Both pending readings of the field are removed, and no new GLUE is added.** The field becomes the leaf
`sga7_IX_3_5_ForwardUnipAC : SGA735Nil.SGA7_IX_3_5_ForwardUnipAC`, rated LEAF/LEAF (restricted printed form). With
the proposed row, strict and strictest both go from 11 LEAF / 18 GLUE to 12 LEAF / 17 GLUE on 29 H fields (−1 GLUE).
The count was computed on kinds.tsv with the proposed row, and that row passes `render_open.kinds_row_problems`.

* **The new leaf.** It is the field with two changes:
  * `[IsAlgClosed (IsLocalRing.ResidueField O)]` is added. This is sga735-narrow's restriction, and it removes
    reading (a), the `k(s)` reading.
  * The conclusion `(σ - 1)² = 0` is weakened to `IsNilpotent (galTΩ A ℓ σ - 1)`, i.e. inertia acts unipotently on
    `T_ℓ`. This removes reading (b), the echelon clause.

  What is left is the direction "semistable ⇒ unipotent" of SGA 7 IX 3.5, which the print states under every
  recorded reading (§4). The leaf is a specialization of the old field (`SGA735Nil.forwardUnipAC_of_forwardGeom`),
  of sga735-narrow's leaf, and of the `k(s)` reading (VERIFIED, compiled).
* **What the consumer needs (step 1, VERIFIED by reading the code).**
  * The field is read only through `semistableUnipotent`, and then through r6 at number fields
    (`RaynaudCriterionNF`, conclusion `UnipSq`).
  * The live readers of r6's square-zero conclusion are two:
    * `HDec.G15Ram.raynaudPlace_of_R6`, for a wild `σ'` that has a `p`-power period on points. It goes into
      `fixed_of_unipSq_of_iterate'`.
    * `HDec.PkgI2.goodReduction_of_QM_rational3_of_alg`, the ℓ = 3 quaternion consumer (A6). It goes into
      `quatUnipotentTrivial`.
  * Both need only that `σ - 1` is nilpotent on `A[ℓⁿ]`, with **one** exponent for all `n`. That follows from
    nilpotence on `T_ℓ`.
* **A shorter path than sga735-narrow's plan.** That plan needed `c⁴` at level `3^{4k}` and new valuation algebra.
  Neither is needed:
  * **Wild case.** The proof is a downward induction on the exponent. At each step the existing square-zero core is
    applied to `(σ - 1)^{j-1} x`, which keeps the period because `σ - 1` commutes with `σ`
    (`SGA735Nil.fixed_of_nil_of_iterate`).
  * **QM case.** Suppose `(S - 1)^{2^{i+1}} = 0` on every `G[3^k]`. Then `(S - 1)^{2^i} = 0` on every `G[3^k]`:
    apply the existing `PkgI2.quatUnipotentTrivial` to `1 + (S - 1)^{2^i}`, whose "square-zero" hypothesis is
    exactly `(S - 1)^{2^{i+1}} = 0` (`SGA735Nil.nilQuat_trivial`). Halving `⌈log₂ N⌉` times gives `S = 1`.
  * Both readers keep their conclusions. `RaynaudPlace` keeps its type, because a wild `σ'` fixes `A[ℓⁿ]` outright.
* **The fold is a bypass, because the leaf is weaker than the field.**
  * `scratch/sga735-finish/FoldCheck.lean` is generated and copies 127 declarations (`X ↦ X_nl`).
  * In the copies, r6 is re-typed to `SGA735Nil.RaynaudCriterionNFNil`.
  * It compiles with no errors.
  * `HDec.HSyn.sixContactMin_of_open49 (r : OpenResearchLeaves32) (t : OpenTextbookLeaves16)
    (l : OpenAddedLeaves25) : ZInQ.SixContactMin` uses only `[propext, Classical.choice, Quot.sound]`.
  * Its closure contains neither `UnipotentForward.SGA7_IX_3_5_ForwardGeom`, nor `ReductSplit.SemistableUnipotent`,
    nor `RaynaudCriterionNF` (VERIFIED, `ClosureCheck.lean`).
  * `OpenResearchLeaves32` differs from `OpenResearchLeaves31` in exactly one field.

## 2. Lean (VERIFIED: `lake build`, standard axioms; outputs in `scratch/sga735-finish/build_contrib.txt`)

`ZInQKernel/Contrib/OneProof/SGA7IX35Unip.lean` (namespace `SGA735Nil`) imports `SGA7IX35ForwardAC`, which in turn
imports `UnipotentForward`, the module that defines the field. It does not import Main.

* §1, group theory:
  * `diffHom f` (`x ↦ f x · x⁻¹`) and `diffPow`, `onePlus`.
  * `fixed_of_sq_of_iterate`.
  * `fixed_of_nil_of_iterate`: if `(f-1)^N x = 1`, `x^m = 1` and `f^q x = x` with `gcd(q, m) = 1`, then `f x = x`.
    Axioms `[propext, Quot.sound]`.
* §2: `isNilpotent_sub_one_of_surj`, which transports nilpotence along a surjective intertwiner.
* §3, the leaf `SGA7_IX_3_5_ForwardUnipAC`, and three ways to get it:
  * `forwardUnipAC_of_forwardGeomAC`, from sga735-narrow's leaf;
  * `forwardUnipAC_of_forwardGeom`, from the field;
  * `forwardUnipAC_of_forwardRes`, from the `k(s)` reading.
* §4, `SemistableUnipotentNilCP`. This is the chain's `ReductSplit.SemistableUnipotent` with a perfect residue field
  and a nilpotent conclusion. It is proved in `semistableUnipotentNilCP_of_forwardUnipAC (hP) (hE : MulEtaleAbelianScheme)
  (hN : NeronBaseChangeStrictHenselization)`, which is sga735-narrow's proof with nilpotence transported instead of
  the square.
* §5, `RaynaudCriterionNFNil`. This is `GapNeron.RaynaudCriterionNF` with the conclusion
  `∃ N, ∀ n, ∀ x ∈ A[ℓⁿ], (σ-1)^N x = 1`.
  * `tate_iter` gives `((σ-1)^N t)_n = (σ-1)^N t_n` on `T_ℓ`.
  * `raynaudCriterion_leavesNF_nil` proves it, with the same hypotheses as neron-dvr's
    `GapNeron.raynaudCriterion_leavesNF`.
  * `raynaudCriterionNFNil_of_sq` shows that square-zero r6 implies it.

`ZInQKernel/Contrib/OneProof/SGA7IX35UnipReaders.lean` imports `OneProof.H.TailH` and `SGA7IX35Unip`:

* `SGA735Nil.nilQuat_trivial`, the ℓ = 3 quaternion core for nilpotent `S - 1`. Axioms `[propext, Quot.sound]`.
* `HDec.G15Ram.raynaudPlace_of_R6Nil`, of type `RaynaudPlace A m`, the same as `raynaudPlace_of_R6`. It uses
  `G15Ram.wildIter` and `fixed_of_nil_of_iterate`.
* `HDec.PkgI2.goodReduction_of_QM_rational3_of_alg_nil`, and the universe-0 wrappers
  `goodReduction_of_QM_rational3_nl` and `goodReduction_of_QM_rational3'_nl`.

`#print axioms` gives `[propext, Classical.choice, Quot.sound]`, or fewer, for every one of these.

`scratch/sga735-finish/Statement.lean` checks the verbatim copy of the field statement against
`UnipotentForward.SGA7_IX_3_5_ForwardGeom` by `rfl`, together with the three derivations of the new leaf
(`statement_out.txt`).

## 3. The fold (`scratch/sga735-finish/gen/gen.py`; check outputs VERIFIED)

1. **Copy set (`R6Taint.lean`, output `r6taint_out.txt`).** It is computed on the closure of `sixContactMin_of_open48`,
   which has 242,333 constants. The candidates are of two kinds:
   * **(A)** constants whose value depends on a projection `sga7_IX_3_5_ForwardGeom` or `semistableUnipotent`
     (60 constants);
   * **(B)** constants whose type mentions `RaynaudCriterionNF`, or a structure that carries an (A) or (B) field.
     This is iterated, and it finds 25 structures: research generations 2, 5, 7, 8, 9, 14GM–29GM and 31, and
     `ResearchLeaves3`.

   The copy set is the least set that contains the top and is closed under candidate dependencies. It has 735
   constants. Without projections and constructors, that is 127 declarations.
2. **What the generator does to the copies.**
   * Every spelling of `RaynaudCriterionNF` becomes `SGA735Nil.RaynaudCriterionNFNil`.
   * The field becomes `sga7_IX_3_5_ForwardUnipAC : SGA735Nil.SGA7_IX_3_5_ForwardUnipAC`.
   * `semistableUnipotent` gets the type `SemistableUnipotentNilCP`.
   * Two lines are edited: the conversion (`semistableUnipotentNilCP_of_forwardUnipAC`) and the r6 producer
     (`raynaudCriterion_leavesNF_nil`).
   * The readers are mapped to the Readers file. `GapNeron.raynaudCriterion_(of_)leavesNF` are not copied.
3. **Generator fixes found along the way** (relevant to other copylib users).
   * `copylib.CTX` now also copies `attribute [-instance] …` context. Without it, the TailH copies hit typeclass
     timeouts (`Module.IsTorsionFree ℚ_[p] M`, even at 200000 heartbeats).
   * Blocks whose original declaration lives in `HDec` but whose emitted context lacks `namespace HDec` (the
     LPrefix `LeafQM` section) are wrapped in `namespace HDec … end HDec`.
   * `local notation` in a copied context is expanded in place, not copied.
4. **Outputs.**
   * `lake env lean scratch/sga735-finish/FoldCheck.lean`: no errors (`foldcheck_out.txt`), and the top theorem has
     the standard axioms.
   * `ClosureCheck.lean` is FoldCheck plus a closure probe (`closurecheck_out.txt`).
5. **Integrator steps.**
   1. Add the two Contrib files to the build.
   2. Copy FoldCheck.lean to `ZInQKernel/OneProof/H/TailZ56.lean`. It is 325 KB, so split it if needed. Or
      regenerate it on the integration tree: run `R6Taint.lean` with the current top, then `gen.py`.
   3. Switch Main to `sixContactMin_of_open49`.
   4. Replace the kinds.tsv row with `scratch/sga735-finish/kinds-row-proposed.tsv`.
   5. Regenerate OPEN.md.

   This fold supersedes sga735-narrow's fold, which is not on main. The spec is `scratch/sga735-finish/autofold.json`.
   It records a BYPASS discharge, because autofold cannot express a weaker leaf.
6. **`#discharges`** (`Discharges.lean`, output `discharges.txt`, 33 DISCHARGES lines). As expected, no line comes from
   the new files: the new leaf is weaker than the field, so no theorem has the field's type. The only line on the
   field is gt-unip's existing `UnipotentForward.forwardGeom_of_forward`.

## 4. The new leaf and its rating

```lean
def SGA735Nil.SGA7_IX_3_5_ForwardUnipAC : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [IsAlgClosed (IsLocalRing.ResidueField O)],
    IsStrictlyHenselianDVR O →
    ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (w : ValuationSubring Ω),
    w.comap (algebraMap K Ω) = O → ∀ A : PkgI3.AbVar K,
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : O) → HasSemistableReduction A O →
      ∀ σ : Ω ≃ₐ[K] Ω, IsInertia w σ → IsNilpotent (galTΩ A ℓ σ - 1)
```

**Rating: printed form (restricted), LEAF/LEAF. The locator is UNVERIFIED (the display has not been read).**

* **Statement.** SGA 7 I, Exp. IX, Prop. 3.5 says "`A_K` has semistable reduction ⇔ `I` acts unipotently on `T_ℓ`"
  (UNVERIFIED number; every recorded reading by gt-unip, unipotent-b, pkg-I2 and the 11-15 statement review contains
  this equivalence). The leaf is its forward direction, one `σ` at a time. "Acts unipotently" is `σ - 1` nilpotent on
  `T_ℓ`, which is equivalent to the same on `V_ℓ`. The leaf makes no claim about the nilpotence index, so the echelon
  clause is not used. Reading (b) is gone.
* **Base.** The base is a strictly henselian DVR with algebraically closed residue field. That is a specialization of
  the print's DVR. Since `k(s) = κ̄`, semistability over `k(s)` and on the geometric special fibre coincide
  (`UnipotentForward.hasSemistableReductionRes_iff`, already proved), so reading (a) is gone too. This is
  sga735-narrow's argument, re-checked here by `forwardUnipAC_of_forwardRes`.
* **`K^s`, inertia, `T_ℓ = lim A(K^s)[ℓⁿ]`.** These are unchanged from the field, and the 11-15 statement review found
  them to be dictionary.
* **No invented structures.** The definitions are the field's own genuine ones: `HasSemistableReduction`, `galTΩ`,
  `IsInertia`, `IsStrictlyHenselianDVR`.
* **Never stronger.** It is a consequence of the old field (compiled) and of the print under either reading of
  semistable.

## 5. New statements that are not leaves (all proved, so they add no GLUE)

| statement | status |
| --- | --- |
| `SGA735Nil.SemistableUnipotentNilCP` | proved from the leaf + `MulEtaleAbelianScheme` + `NeronBaseChangeStrictHenselization` (bundle leaves the old proof used) |
| `SGA735Nil.SemistableUnipotentNilSHAC` | proved from the leaf + `MulEtaleAbelianScheme` |
| `SGA735Nil.RaynaudCriterionNFNil` | proved (`raynaudCriterion_leavesNF_nil`, same hypotheses as the old r6 proof) |

## 6. Files

* `ZInQKernel/Contrib/OneProof/SGA7IX35Unip.lean` and `ZInQKernel/Contrib/OneProof/SGA7IX35UnipReaders.lean`: the
  contribution.
* `scratch/sga735-finish/`:
  * `log.md`.
  * `R6Taint.lean`, `r6taint_out.txt`: the copy set.
  * `gen/gen.py`, `gen/copylib.py` (with the `attribute [-instance]` fix), `gen/header.lean`: the generator.
  * `FoldCheck.lean`, `foldcheck_out.txt`, `ClosureCheck.lean`, `closurecheck_out.txt`: the fold and its checks.
  * `Statement.lean`, `statement_out.txt`, `Discharges.lean`, `discharges.txt`: the statement check and
    `#discharges`.
  * `kinds-row-proposed.tsv`, `autofold.json`, `build_contrib.txt`.

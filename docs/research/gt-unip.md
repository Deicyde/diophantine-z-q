# gt-unip: the field `semistableUnipotent` from the forward half of SGA 7 IX 3.5

Task gt-unip, 2026-11-15. Base ef2f6915 (leaf-fold18; top `HDec.HSyn.sixContactMin_of_open23`, module `TailZ29`).
Contribution: `ZInQKernel/Contrib/OneProof/UnipotentForward.lean` (namespace `UnipotentForward`). Scratch files:
`scratch/gt-unip/`. Results log: `scratch/gt-unip/log.md`. Nothing else under `ZInQKernel/` or `blueprint/` was
edited. This is model work, and no human has reviewed it.

Marks:
- **VERIFIED**: compiled, or read in a file.
- **STANDARD**: published, with a reference.
- **SPECULATIVE**: a judgement.
- **UNVERIFIED**: a theorem number or wording recalled from memory. This host has no network, and SGA 7 was not
  read.

## 1. Main result

**The field `semistableUnipotent : ReductSplit.SemistableUnipotent` is discharged as stated** (VERIFIED by
`#discharges`, §4). The proof uses no glue. It needs one new printed-base leaf and two leaves already in the
bundles:

```
UnipotentForward.semistableUnipotent_of_forwardGeom
  (hP : SGA7_IX_3_5_ForwardGeom)                      -- new LEAF: SGA 7 IX 3.5, forward direction, σ = τ,
                                                      --   strictly henselian trait, K^s, T_ℓ = lim A(K^s)[ℓⁿ]
  (hE : AvSplit.T4.MulEtaleAbelianScheme)             -- bundle LEAF (t.mulEtaleAbelianScheme), BLR 7.3/2
  (hN : GapSHPair.NeronBaseChangeStrictHenselization) -- bundle LEAF (r.neronBaseChangeStrictHenselization), BLR 1.2/2
  : ReductSplit.SemistableUnipotent
```

The autofold dry run of this fold compiles. It takes the strict count from **49/12 to 50/11** on 61 fields and the
strictest count from 48/13 to 49/12. GLUE goes down by one (VERIFIED).

**Reading-robust alternative.** It closes the residue-field reading axis, but in exchange it keeps one GLUE:

```
UnipotentForward.semistableUnipotent_of_forward
  (hP : SGA7_IX_3_5_Forward)                  -- LEAF: as above, semistability assumed over k(s) AND geometrically
  (hD : SemiAbelianDescendsSepClosed)         -- GLUE (unipotent-b's), proved here for perfect residue fields
  (hE) (hN) : ReductSplit.SemistableUnipotent
```

Its dry run gives the strict count 49/12 → 50/12 on 62 fields, so it does not lower GLUE.

**Recommendation.** Fold the first form, `SGA7_IX_3_5_ForwardGeom`, flagged as a reading risk. This follows the
chain's precedent `raynaudSemistableSH`, which is SGA 7 IX 4.7 stated with no restriction on the residue field and
the same kind of flag, and counts as LEAF. If a statement check finds that SGA 7 IX Déf. 3.1 reads semistability
over `k(s)`, switch to the second form. The reroute is one line, since both theorems have the same conclusion.

## 2. Which direction and which clauses the consumers use (VERIFIED, read in source)

- **The field already is the weak clause.** `ReductSplit.SemistableUnipotent` (`TailZ7` L253) assumes semistable
  reduction and concludes `σσt − 2σt + t = 0` for each `σ` in the inertia group. That is the forward direction of
  3.5 with the echelon clause taken only at `σ = τ`, one `σ` at a time. The review's suggestion holds, and the
  field was already stated that way.
- **r6, the live consumer.** `ReductGlue.raynaudCriterion_leaves` (`TailZ14` L243, called in `TailZ15` L100 and
  `TailZ23` L780) goes through `raynaudCriterion_final` to `ReductSplit.raynaudCriterion_of_leaves` (`TailZ7` L395).
  That proof applies `hU` only in this situation:
  - `Ω = AlgebraicClosure K`;
  - `w ⊆ K̄` lying over `O`;
  - semistability from `hasSemistableReduction_of hN O B hss`, the geometric reading, through Raynaud 4.7;
  - every `t`, followed by `unipSq_of_tate`.

  It needs every field `K` and every DVR `O`, imperfect residue fields included, because r6 is stated over every
  field.
- **r8.** `grothendieckMonodromy_final'` (`TailZ9` L100) applies `hU` over `K' ⊆ K̄` with `Ω = AlgebraicClosure K`.
  unipotent-b's dependency check found r8 inert.
- **No consumer needs less than the field.** Nothing a consumer could give up removes an axis, so the field is
  discharged as stated and no consumer site has to be rerouted.

## 3. The new statements

### 3.1 LEAF `SGA7_IX_3_5_ForwardGeom` (recommended)

```lean
def SGA7_IX_3_5_ForwardGeom : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O],
    IsStrictlyHenselianDVR O →
    ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (w : ValuationSubring Ω),
    w.comap (algebraMap K Ω) = O → ∀ A : PkgI3.AbVar K,
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : O) → HasSemistableReduction A O →
      ∀ σ : Ω ≃ₐ[K] Ω, IsInertia w σ → (galTΩ A ℓ σ - 1) * (galTΩ A ℓ σ - 1) = 0
```

Source: Grothendieck, SGA 7 I, Exp. IX, Prop. 3.5. The number is UNVERIFIED. How it compares with the print, axis by
axis:

| axis | the field (`TailZ7`) | this leaf |
|---|---|---|
| base | every DVR (open: the print is over a strictly local trait) | strictly henselian DVR (the print's setting); the move to a DVR is **proved** (§3.3) |
| `K^s` vs `K̄` | algebraic closure (open) | separable closure, `T_ℓ = lim A(K^s)[ℓⁿ]` (the print); the move to `K̄` is **proved** from `MulEtaleAbelianScheme` |
| direction, echelon | forward, `σ = τ` | forward, `σ = τ`, plus `IsInertia` as an extra hypothesis (the print gives `(σ-1)(τ-1) = 0` and the converse, UNVERIFIED wording): a consequence of the print |
| `k(s)` | geometric special fibre | geometric special fibre: **the one open reading** (below) |

**Reading risk on `k(s)`.**
- If SGA 7 IX defines semistable reduction over `k(s)` itself, this leaf follows from the print only together with
  `SemiAbelianDescendsSepClosed` (§3.2).
- That descent statement is believed true and is proved here for perfect `k(s)` (`semiAbelianDescends_of_perfect`).
  So the risk concerns imperfect residue fields only, which never occur at a DVR of a number field.
- If SGA 7 IX reads semistability on the geometric fibre, or notes that it is a geometric property (SPECULATIVE
  recollection), then the leaf is a consequence of the print.

**The leaf is not vacuous.** The fraction field of the strict henselization of `ℤ_(p)` has a strictly henselian DVR.
Abelian varieties with good reduction there are semistable, and `separableClosure` gives the separable closure.

### 3.2 LEAF `SGA7_IX_3_5_Forward` (reading-robust) and GLUE `SemiAbelianDescendsSepClosed`

- **`SGA7_IX_3_5_Forward`** is the same statement with the hypothesis
  `HasSemistableReductionRes A O → HasSemistableReduction A O → …`: semistability over `k(s)` and on the geometric
  fibre. Whichever reading SGA 7 uses, the leaf follows from the print by dropping the other hypothesis.
- **`SemiAbelianDescendsSepClosed`** is unipotent-b's GLUE. For a DVR whose residue field `k` is separably closed,
  geometric semistability of a group model gives semistability over `k`. The argument is SPECULATIVE: maximal tori
  (SGA 3 XIV 1.1), descent of properness (EGA IV₂ 2.7.1) and split tori over `k^sep`; all locators UNVERIFIED.
- Relations, all proved:
  - `forward_of_forwardGeom : ForwardGeom → Forward`;
  - `forwardGeom_of_forward : Forward → SemiAbelianDescendsSepClosed → ForwardGeom`.

### 3.3 Proved here

- **`strictHenselizationInside_of_neron : GapSHPair.NeronBaseChangeStrictHenselization →
  ReductGlue.StrictHenselizationInside`.**
  - unipotent-b needed reduct-glue's leaf candidate `StrictHenselizationInside`, which is not in the chain.
  - It is now a theorem from the chain's leaf `neronBaseChangeStrictHenselization` (leaf-fold18).
  - `E` is gt-shpair's inertia field (`GapSHPair.inertiaField`). Its valuation ring satisfies `IsSHSep`
    (`GapSHPair.isSHSep_inertia`), and inertia fixes it (`GapSHPair.inertia_fixes`).
- **`semistableUnipotentSH_of_forwardGeom`** proves reduct-glue's strictly henselian form
  `ReductGlue.SemistableUnipotentSH` from the leaf and `MulEtaleAbelianScheme`. Its statement is unchanged.
  - `σ` is restricted to `K^s` (`inertiaRestrict'`).
  - `A(K^s)[ℓⁿ] = A(Ω)[ℓⁿ]` because `[ℓⁿ]` is étale (`torsion_from_sepClosure`), which gives a surjection on `T_ℓ`
    (`tateMap_surjective`).
  - `(σ-1)² = 0` is turned into the field's pointwise form by `sq_form`.
- **`semistableUnipotent_of_forwardGeom`** is reduct-glue's `unipotentFromSH_of` applied to the two results above.
- The `k(s)` fibre (`specialFibre`, `IsSemistableRes`, `HasSemistableReductionRes`, `isSemistableRes_iff`) and the
  `K^s` lemmas are unipotent-b's proofs (`origin/wip/unipotent-b`, not in the chain), copied into the contribution.
  Every chain declaration they use is imported, not copied: `unipotentFromSH_of`, `semiAbelianFieldIsoInvariant`,
  `pbCompIso`, `bcPt_galAct`, `extPt_galAct` and `comp_pow_one`.

## 4. Checks (VERIFIED)

- `lake env lean ZInQKernel/Contrib/OneProof/UnipotentForward.lean` gives no errors and no warnings, in 10 s.
- `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.UnipotentForward`
  builds all 12933 jobs successfully.
- `#discharges` (`scratch/gt-unip/DischargesCheck.lean`, full output in `scratch/gt-unip/discharges-output.txt`):

```
DISCHARGES [OpenResearchLeaves19.semistableUnipotent] by UnipotentForward.semistableUnipotent_of_forward
  still assumes: [UnipotentForward.SGA7_IX_3_5_Forward,
 UnipotentForward.SemiAbelianDescendsSepClosed,
 AvSplit.T4.MulEtaleAbelianScheme,
 GapSHPair.NeronBaseChangeStrictHenselization]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves19.semistableUnipotent] by UnipotentForward.semistableUnipotent_of_forwardGeom
  still assumes: [UnipotentForward.SGA7_IX_3_5_ForwardGeom,
 AvSplit.T4.MulEtaleAbelianScheme,
 GapSHPair.NeronBaseChangeStrictHenselization]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 68 open hypotheses, 993 theorems checked, 5 discharge one
```

  The other three discharges in the output are from contributions already in the tree.
- `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for all seven main declarations.
- Fold dry run: `python3 scripts/one_proof/autofold.py scratch/gt-unip/autofold-spec.json --dry-run`.
  - It prints `strict count: 49/12 on 61 -> 50/11 on 61; strictest 48/13 -> 49/12`.
  - The printed module (`scratch/gt-unip/FoldDryRun.lean`, with its first line removed) compiles against `TailZ29`,
    and `sixContactMin_of_open24` uses standard axioms only.
  - The spec's proof term is `_root_.UnipotentForward.semistableUnipotent_of_forwardGeom
    {n}.sga7_IX_3_5_ForwardGeom {t}.mulEtaleAbelianScheme {n}.neronBaseChangeStrictHenselization`.
- The robust spec is `scratch/gt-unip/autofold-spec-robust.json`. Its dry run prints `49/12 on 61 -> 50/12 on 62`;
  it was not compiled.

## 5. What remains

- **Read SGA 7 I, Exp. IX in print**, §3 (Déf. 3.1 and Prop. 3.5). This settles three things:
  - the number;
  - whether 3.5 is stated over a strictly local trait;
  - whether semistable reduction is read over `k(s)` or geometrically, or is noted as a geometric property.

  The third decides between the two forms in §1.
- **`SemiAbelianDescendsSepClosed` is unproved** for imperfect, separably closed residue fields. It is only needed on
  the robust route. Nothing in Mathlib 4.35 gives maximal tori or quotients of group schemes.
- **For the integrator:** use `scratch/gt-unip/autofold-spec.json` for the fold. Add a `docs/research/locators.md`
  row for SGA 7 IX 3.5 and a kinds.tsv row flagged as a reading risk. autofold writes the kinds.tsv row from the
  spec's flag.

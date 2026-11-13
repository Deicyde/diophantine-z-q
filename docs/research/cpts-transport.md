# cpts-transport: `CPtsTransport` proved, and `BaseChangeClassUnique` proved by the same argument

Task cpts-transport, 2026-11-13. Base: `wip/integrate-w44` (b7cdba8e) merged with `origin/wip/g0-assemble3`.
Lean files: `scratch/cpts-transport/`. Results log: `scratch/cpts-transport/log.md`. No file under `ZInQKernel/`,
`blueprint/` or another task's directory was edited. This is model work with no human review.

Marks used below:
- **VERIFIED**: compiled, or read in a file.
- **STANDARD**: published, with a reference.
- **SPECULATIVE**: a judgement.
- **UNVERIFIED**: a theorem number recalled from memory (there is no network access).

## 0. Main result

**Verdict.** `HSyn.G0Split.FibreQM.CPtsTransport` (field 18 of g0-assemble3's `GluePieces4`) is a theorem. It needs no
hypotheses. The statement is fibre-qm-period's definition exactly as it appears in g0-assemble3's compiled olean chain,
and it was not edited.

```lean
theorem HSyn.G0Split.FibreQM.cPtsTransport_proof : CPtsTransport
theorem HSyn.G0Split.FibreQM.PeriodMapH.baseChangeClassUnique_proof : BaseChangeClassUnique   -- field 10
structure HSyn.GluePieces5 : Prop      -- GluePieces4 without fields 10 and 18: 44 fields = 14 LEAF + 3 LEAF? + 27 GLUE
theorem HSyn.gluePieces4_of_gluePieces5 (gp : GluePieces5) : GluePieces4
theorem HSyn.sixContactMin_of_leaves5 (r : ResearchLeaves4) (t : TextbookLeaves) (gp : GluePieces5) :
    ZInQ.SixContactMin
theorem HSyn.G0Split.FibreQM.PeriodMapH.fibreQMPeriod_periodMap' …   -- fibreQMPeriod_periodMap without hBC, hCP
```

All of these are VERIFIED: they compile with no `sorry`, and every `#print axioms` gives
`[propext, Classical.choice, Quot.sound]` (§5).

- **The same argument closes `BaseChangeClassUnique`.** This is period-map's glue Prop and field 10 of `GluePieces4`;
  it is the only open Prop of the period-map/fibre-qm-period cluster that is about base change.
- **Rigidity is no longer a leaf in either proof.** Both use mul-rigidity's proof of rigidity (`G0FibreSimple.rigidityHom`,
  proved from Mathlib in part a15), not a textbook leaf. The docstrings of `CPtsTransport`, `UnifTransport` and
  `BaseChangeClassUnique` say "rigidity is not in Mathlib". That is now out of date: rigidity is proved in the project.
- **`UnifTransport` is now a theorem as well**, through fibre-qm-period's `unifTransport_of`.

**fibre-qm-period's other three glue Props** were `PeriodMapGlue`, `HauptmodulUnique` and `QMDenZeroCM3`. All three
are still open, through the smaller Props period-map reduced them to. The pullback-and-rigidity argument closes only the
base-change piece, `BaseChangeClassUnique`; §3 gives each remaining piece and why the argument does not reach it.

## 1. `CPtsTransport`: the statement and the proof

**Statement** (fibre-qm-period, `part_fqm.lean`; g0-assemble3 part a80, read in the file):
- **Data.**
  - `A : DefFaltings.AbVar K` over a number field `K`;
  - `emb : K → ℚ̄`;
  - `P : QML3 ℚ̄` with `Nonempty ((A.baseChange ℚ̄).X ≅ P.A.X)`, an isomorphism in `Over (Spec ℚ̄)`. It is not
    required to be a group isomorphism.
  - `ιe : ℚ̄ → ℂ`;
  - `Q : QML3 ℂ` with `IsBaseChangeOf ιe P Q`.
- **Conclusion.** There is a group isomorphism `ψ : CPts Q.A id ≃* CPts A (ιe ∘ emb)` that is compatible with regular
  functions: for every open `U` of `A` and every `s ∈ Γ(U)` there are `U'` and `s'` on `Q.A` such that
  - `ψ x ∈ U(ℂ) ↔ x ∈ U'(ℂ)`, and
  - `cEvalAt (ψ x) U s = cEvalAt x U' s'` whenever `x ∈ U'(ℂ)`.

**Proof** (`scratch/cpts-transport/CPtsTransport.lean`, VERIFIED):

1. **`cPts_of_isPullback`.** This is the general step. Take `A : PkgI3.AbVar K`, `σ : K → ℂ`, `Q : PkgI3.AbVar ℂ` and
   `T0 : Q.X.left ⟶ A.X.left` with `IsPullback T0 Q.X.hom A.X.hom (Spec σ)`. Then the conclusion above holds.
   - `E : Q.X ≅ (A.baseChange ℂ).X` in `Over (Spec ℂ)`. It comes from `IsPullback.isoIsPullback`, comparing with the
     pullback square of `A.baseChange ℂ`, which uses `σ.toAlgebra`.
   - `b = η ≫ E.hom` and `φ = E.hom * (toUnit ≫ b⁻¹)`, which is `E` translated by `−E(0)` in the group of morphisms into
     the group object. Its inverse is `φ' = (𝟙 * (toUnit ≫ b)) ≫ E.inv`. These are g0-fibresimple's identities from
     `endDivisionOfSchemeIso_of_rigidity`, reused.
   - `η ≫ φ = η`, so `φ` is a homomorphism by rigidity (`G0FibreSimple.rigidityHom ℂ Q (A.baseChange ℂ) φ`).
   - `ψ` is `x ↦ x ≫ φ`, a `MulEquiv` because `MonObj.mul_comp` holds for an `IsMonHom`. It is followed by unram-tate's
     `bcPt : (A_ℂ)(ℂ) ≃* A(ℂ)_σ`, the adjunction bijection of `Over.mapPullbackAdj`, already in part a45.
   - `(ψ x).left = x.left ≫ T` with `T = φ.left ≫ pullback.fst`, which holds by `rfl` after `Category.id_comp`. So take
     `U' = T⁻¹ᵁ U` and `s' = T.app U s`. The values agree by `Scheme.Hom.comp_appLE` (`appLE_of_eq`, `cEvalAt_of_eq`).
2. **`cPtsTransport_proof`.** Paste three squares with `IsPullback.paste_horiz`:
   - the square of `IsBaseChangeOf` (`Q.A → P.A` over `Spec ιe`);
   - the square of `e.inv`, an isomorphism (`IsPullback.of_horiz_isIso`);
   - the pullback square of `A.baseChange ℚ̄` over `Spec emb`.

   Then rewrite `Spec ιe ≫ 𝟙 ≫ Spec emb = Spec (ιe ∘ emb)` and apply step 1.

**Which hypotheses are used.** Only the pullback clause of `IsBaseChangeOf` is used. Its `ι` and `η` clauses are not
needed to transport complex points. The isomorphism `e` may move the identity section; the recentring by `b` absorbs
that, as fibre-qm-period's docstring planned.

**Pitfall.** Without an explicit instance, `bcPt` at `L = Ω = ℂ` picks some `Algebra ℂ ℂ` instance, and identifying
`ptObj ℂ` with `cptObj (RingHom.id ℂ)` then hit a whnf timeout. Passing `Algebra.id ℂ` explicitly
(`@UnramTate.bcPt K ℂ _ _ σ.toAlgebra A ℂ _ (Algebra.id ℂ) σ.toAlgebra IsScalarTower.right`) makes the identification
definitional and cheap.

## 2. `BaseChangeClassUnique` (period-map, field 10), proved

**Statement.** Two base changes `Q, Q'` of `P/ℚ̄` along the same `ιe : ℚ̄ → ℂ` (`IsBaseChangeOf`) satisfy
`M3.mk Q = M3.mk Q'`.

**Proof** (`scratch/cpts-transport/BCUnique.lean`, VERIFIED):
- `E0 = isoIsPullback` of the two squares, with `E0.hom ≫ g' = g` and `E0.hom ≫ Q'.hom = Q.hom`.
- `ι`-equivariance and the level clause are checked with `IsPullback.hom_ext` on the second square. Composing with `g'`
  reduces each to the `ι` and `η` clauses of the two `IsBaseChangeOf`s; composing with `Q'.hom` gives `Over.w`.
- `η[Q.A.X] ≫ E.hom = η[Q'.A.X]` is proved the same way. The input is `eta_left_comp`: the `η` clause at `a = 0` gives
  `η.left ≫ g = Spec ιe ≫ η_P.left`, because `toMul (eta 0) = 1 = toUnit ≫ η` and `(ptObj ℂ).hom = 𝟙`.
- `E.hom` and `E.inv` are homomorphisms by `G0FibreSimple.rigidityHom`.
- `Quotient.sound` then applies to the resulting `QML3.Iso`.

## 3. fibre-qm-period's four glue Props, and what remains of them

fibre-qm-period left four glue Props: `PeriodMapGlue`, `HauptmodulUnique`, `QMDenZeroCM3` and `CPtsTransport`.
period-map reduced the first three, and g0-assemble3 lists the resulting pieces as fields 10-17 of `GluePieces4`
(VERIFIED in `scratch/g0-assemble3/parts/e20_periodmap.lean` and `docs/research/g0-assemble3.md` §1-2).

| fibre-qm-period Prop | pieces after period-map (`GluePieces4` field) | status now | does the pullback/rigidity argument close it? |
|---|---|---|---|
| `CPtsTransport` | — (field 18) | **proved here** | yes (§1) |
| `PeriodMapGlue` | `BaseChangeClassUnique` (10) | **proved here** | yes (§2) |
| | `PiTwistC` (11): two `ℂ`-points of `Y` have the same `π`-value iff their QM pairs are `Aut(𝒪)`-twists | open, GLUE | no. It is R2fp's fibre clause on `ℂ`-points rather than `ℚ̄`-points. It needs the coarse-moduli property of `X₆` over `ℂ`, or algebraicity of the two relations (period-map's docstring). That is moduli theory, not base change of one object. |
| | `QMTwistLattice` (12): `Aut(𝒪)`-twists ↔ `τ' ∈ Γ*τ` | open, GLUE | no. It is analytic: the `Hom` form of T11a plus Skolem–Noether over `ℚ` (the kernel's `TSkolemKW`) and a lattice computation. |
| | `CMDescends` (13) | open, LEAF? | no. It is Shimura–Taniyama (CM abelian varieties are defined over `ℚ̄`). Its glue around the leaf (T11b for the CM, `A[3] ⊆ A(ℚ̄)` for the level) could use `IsBaseChangeOf` bookkeeping like §2, but the core is a literature input. SPECULATIVE. |
| | `PiCMC`, `CMFixedHasCM` | proved by period-map (from the above and T11a) | — |
| `HauptmodulUnique` | `S8Nonzero` (14), `SphereFactorAffine` (15) | open, GLUE | no: numerics (`Σθ⁸(Ω(√2+i)) ≠ 0`) and complex analysis on `P¹` |
| `QMDenZeroCM3` | `S8Nonzero` (14), `S8WeightExact` (16), `ValenceBoundGammaStar` (17, LEAF) | open | no: modular-form weight and the valence formula |

**Other fields checked** (SPECULATIVE). The other `GluePieces5` fields that mention base change are height-bc's
`HodgeBCInjective` and `OmegaBaseChange` (fields 4 and 5). They concern cotangent spaces and `e*Ω¹` under
`𝓞_L → 𝓞_{L'}` (commutative algebra of differentials), so the points-level argument does not apply to them.

## 4. Checks on the statements

- **Statement unchanged (VERIFIED).** The proofs elaborate against the definitions in g0-assemble3's olean chain
  (`TailF`: Leaves.lean plus every part up to y*), so `CPtsTransport` and `BaseChangeClassUnique` are the integrated
  texts. The flat check (§5) appends the proofs to a regeneration of g0-assemble3's `G0Assemble3.lean` whose md5
  matches `scratch/g0-assemble3/flat_md5.txt` (b5a4fb97…).
- **Not vacuous.** The hypotheses are satisfiable by genuine objects (fibre-qm-period §3). The proofs construct `ψ` and
  the `QML3.Iso`; neither proceeds by showing that the hypotheses are inconsistent.
- **The proofs depend on no glue or leaf.** Rigidity is mul-rigidity's theorem (part a15, proved from Mathlib's Stacks
  0BFD argument). `bcPt` is unram-tate's construction (part a45). Everything else is Mathlib.
- **The reduction goes the right way.** `GluePieces5 → GluePieces4` is a theorem, so `sixContactMin_of_leaves5` is
  `sixContactMin_of_leaves4` with two fewer hypotheses. No field was weakened or reworded: the 44 field lines are copied
  from part z95 by `mk_bundle5.py`.

## 5. Lean outcomes (all VERIFIED; outputs in `scratch/cpts-transport/*_out.txt`)

Setup. g0-assemble3's compiled oleans `LPrefix…TailF` (worktree g0-assemble3 at 357f5d9e) were copied to `~/cpts-olean`;
they are not committed. Each file starts with `import TailF` and is compiled with `scratch/cpts-transport/ct.sh <file>`.
`lake build ZInQKernel.Hypotheses.JHeight` must be run first.

| file | content | outcome |
|---|---|---|
| `CPtsTransport.lean` | §1 | exit 0, 0 errors, no sorry, 6 s; axioms of `cPts_of_isPullback` and `cPtsTransport_proof` standard |
| `BCUnique.lean` | §2 | exit 0, 0 errors, no sorry, 5 s; axioms standard |
| `Bundle5.lean` (from `mk_bundle5.py`) | g0-assemble3's `TailD.lean` body (parts z80-z95), §1, §2, `GluePieces5`, `gluePieces4_of_gluePieces5`, `sixContactMin_of_leaves5`, `fibreQMPeriod_periodMap'` | exit 0, 0 errors, no sorry, 14 s; all 30 axiom reports standard |
| `Flat5.lean` (from `mk_flat.sh`; not committed, 90 931 lines) | g0-assemble3's flat `G0Assemble3.lean` (md5-identical) plus everything of `Bundle5.lean` after the TailD body | exit 0 in 918 s, 0 errors, no sorry; 218 `#print axioms` reports (parsed by script, multi-line included), all `[propext, Classical.choice, Quot.sound]`, including `sixContactMin_of_leaves5`, `gluePieces4_of_gluePieces5`, `cPtsTransport_proof`, `baseChangeClassUnique_proof` |

## 6. Integration notes

- **Placement.** Add `CPtsTransport.lean` and `BCUnique.lean`, minus `import` and `#check`, as one part after part e20.
  - They need parts a15 (rigidity), a45 (`bcPt`), a80 (`CPtsTransport`) and e20 (`BaseChangeClassUnique`).
  - Each file opens a `noncomputable section` and must be closed by an `end`, as `mk_bundle5.py` does.
- **Bundle.** Replace `GluePieces4` by `GluePieces5`, or keep both with `gluePieces4_of_gluePieces5` (part of
  `Bundle5.lean` after `section CPtsTransportSec`).
- **Kernel port.** A port to `ZInQKernel/HDecomp/` would need kernel copies of mul-rigidity and of `bcPt` (neither is
  in the kernel). `CPts`, `cEvalAt`, `QML3` and `IsBaseChangeOf` are already there (`LeafPush2/R22.lean`,
  `QM/Structures.lean`, `QM/Pairs.lean`). The two target Props themselves exist only in scratch (fibre-qm-period,
  period-map).

## 7. What remains

- **From the fibre-qm-period/period-map cluster:**
  - `PiTwistC`, `QMTwistLattice`, `S8Nonzero`, `SphereFactorAffine` and `S8WeightExact` (GLUE);
  - `CMDescends` (LEAF?);
  - `ValenceBoundGammaStar`, `QMClassNumberOne` and `R1bFamily` (LEAF).
- **Elsewhere:** the other 22 GLUE fields of `GluePieces5` (height-bc 2, prop-ts-glue 14, kf-glue 1, linked-tate 5)
  are untouched by this task.
- **No human review** has been done. The proofs are compiled, so the only trust question is whether the two Props say
  what their docstrings claim. As stated they are weaker than, or equal to, the facts in those docstrings.

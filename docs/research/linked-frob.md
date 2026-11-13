# linked-frob: `UnramTate.LinkedFrob` reduced to N1-g1, `ProperSmoothGenConnected` and the textbook leaves

Task linked-frob, 2026-11-13. Lean: `scratch/linked-frob/` (results log `log.md`, assembly
`assemble.sh`, verbatim check `py/verbatim_check.py`).

Marks: **VERIFIED** = compiled or read in a file. **STANDARD** = published, with a reference.
**SPECULATIVE** = model judgement. **UNVERIFIED** = a locator recalled without a source (there is no
network). This is model work only; no human has reviewed it.

## 0. Main result

linked-tate's glue Prop `UnramTate.LinkedFrob` is proved from strictly smaller named Props. The
statement is unchanged: it is linked-tate's text from `scratch/linked-tate/parts/97_linkeddata.lean`,
compiled in the same file and read over the same `Leaves.lean` definitions.

The reduction runs in two steps:
1. `LinkedFrob` follows from frob-trace's `FrobTrace.AlgFrobLink`. This step is new here, and so is the
   bundle composite at the end.
2. frob-trace, alg-frob-red, afr-absfrob and frob-pieces already reduced `AlgFrobLink` to these four
   inputs:
   - neron-lg's glue N1-g1, `FrobPiecesNeron.AbVarSpreadsOut`;
   - frob-pieces' leaf candidate `FrobPiecesNeron.ProperSmoothGenConnected`;
   - the kernel leaves I2-Red and I2-NMP. In the bundle these are the textbook leaves `t.t4` and
     `t.t3`, which the fork has proved.

   Their proofs are compiled again here, over linked-tate's environment.

The declarations below are VERIFIED. The single file `scratch/linked-frob/LinkedFrob.lean` compiles
with `lake env lean`: exit 0 in 628 s, no `sorry`, and 331 axiom reports, all standard.

```lean
theorem LinkedFrobRed.tmOf_eq {L L' : IF} (hLL' : L ≤ L') (A : PkgI3.AbVar L)
    (Θ : PtQ L A ≃+ PtA (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) (h : PkgI4.GQ)
    (m : GQ → (PtQ L A →+ PtQ L A)) (ℓ : ℕ) [Fact ℓ.Prime] (τ : PkgI4.GQ) :
    tmOf hLL' A Θ h m ℓ τ =
      opV (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ (conjE Θ (m (h * τ * h⁻¹)))
theorem LinkedFrobRed.linkedFrob_of_algFrobLink (hF : FrobTrace.AlgFrobLink) : UnramTate.LinkedFrob
theorem LinkedFrobRed.linkedFrob_of_algFrobRed (hR : FrobTrace.AlgFrobRed) : UnramTate.LinkedFrob
theorem LinkedFrobRed.linkedFrob_of_gen (hG : GoodRedCofinite) (hS : SmoothGeomConnIntegral)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hE : FExtendGen) (hA : AbsFrob) :
    UnramTate.LinkedFrob
theorem LinkedFrobRed.linkedFrob_of_goodRed_nmp (hG : GoodRedCofinite)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0}) :
    UnramTate.LinkedFrob
theorem LinkedFrobRed.linkedFrob_of_neron_nmp (hsp : FrobPiecesNeron.AbVarSpreadsOut)
    (hc : FrobPiecesNeron.ProperSmoothGenConnected)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0}) :
    UnramTate.LinkedFrob
theorem LinkedFrobRed.linkedFrob_of_textbook (t : HSyn.TextbookLeaves)
    (hsp : FrobPiecesNeron.AbVarSpreadsOut) (hc : FrobPiecesNeron.ProperSmoothGenConnected) :
    UnramTate.LinkedFrob
theorem HSyn.gluePieces3_of_gluePieces4 (t : TextbookLeaves) (gp4 : GluePieces4) : GluePieces3
theorem HSyn.sixContactMin_of_leaves4 (r : ResearchLeaves) (t : TextbookLeaves)
    (gp4 : GluePieces4) : ZInQ.SixContactMin
```

(`GoodRedCofinite`, `SmoothGeomConnIntegral`, `FExtendGen` and `AbsFrob` are in namespace
`AlgFrobRedRed`.)

`#print axioms` gives `[propext, Classical.choice, Quot.sound]` for every one of these declarations
and for every other theorem in the file (VERIFIED, `scratch/linked-frob/flat_axioms.txt`):

```
'LinkedFrobRed.tmOf_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'LinkedFrobRed.linkedFrob_of_algFrobLink' depends on axioms: [propext, Classical.choice, Quot.sound]
'LinkedFrobRed.linkedFrob_of_algFrobRed' depends on axioms: [propext, Classical.choice, Quot.sound]
'LinkedFrobRed.linkedFrob_of_gen' depends on axioms: [propext, Classical.choice, Quot.sound]
'LinkedFrobRed.linkedFrob_of_goodRed_nmp' depends on axioms: [propext, Classical.choice, Quot.sound]
'LinkedFrobRed.linkedFrob_of_neron_nmp' depends on axioms: [propext, Classical.choice, Quot.sound]
'LinkedFrobRed.linkedFrob_of_textbook' depends on axioms: [propext, Classical.choice, Quot.sound]
'HSyn.gluePieces3_of_gluePieces4' depends on axioms: [propext, Classical.choice, Quot.sound]
'HSyn.sixContactMin_of_leaves4' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`HSyn.GluePieces4` is linked-tate's `GluePieces3` with one field replaced:
- The 28 other fields are copied verbatim, with their docstrings.
- The field `linkedFrob : UnramTate.LinkedFrob` gives way to two fields:
  - `abVarSpreadsOut : FrobPiecesNeron.AbVarSpreadsOut`;
  - `properSmoothGenConnected : FrobPiecesNeron.ProperSmoothGenConnected`.

So **`ZInQ.SixContactMin` no longer has `LinkedFrob` among its inputs.** In its place it needs N1-g1
and `ProperSmoothGenConnected`, and I2-NMP and I2-Red come from the bundle.

## 1. The proof of `linkedFrob_of_algFrobLink`

`LinkedFrob` asks for g14-trace's `FrobTraceLink` for `tmOf … 5` and `tmOf … 3`. Concretely, there is
a finite `S` such that for every arithmetic Frobenius `τ` at a place `v` above `p ∉ S` there are:
- a field `k` of characteristic `p`;
- an abelian variety `Ā/k`, an endomorphism `α' ∈ End(Ā)` and an integer `N ≠ 0`;
- the kernel's `FrobCompare ℓ (Tm_ℓ τ) α' N` at `ℓ = 3` and at `ℓ = 5`.

The proof (VERIFIED, compiled):
1. **Getting the data.** Three of `LinkedFrob`'s descent-datum hypotheses are, word for word, the
   hypotheses of `AlgFrobLink`:
   - `m_σ` is the Galois action for `σ ∈ G_L`;
   - the coset rule;
   - algebraicity, `m_σ(x) = F_σ ∘ x ∘ Spec σ`.

   `AlgFrobLink L A m` therefore gives `S`, and for `p ∉ S`, `v`, `τ` and `g := h` it gives
   `(k, Ā, α', N)`. For every `ℓ ≠ p` it also gives a `ℚ_ℓ`-isomorphism `Ψ` that carries
   `N·V_ℓ(m_{hτh⁻¹})` to `V_ℓ(α')`.
2. **The finite set.** It is `S ∪ {3, 5}`, so that `ℓ ≠ p` holds at `ℓ = 3` and `ℓ = 5`.
3. **The operators.** `tmOf … ℓ τ` is by definition `opV(Θ ∘ m_{hτh⁻¹} ∘ Θ⁻¹)` (`tmOf_eq`, `rfl`).
4. **The comparison.** frob-trace's `frobCompare_opV_conjE` turns `Ψ` into `FrobCompare` for
   `opV(conjE Θ (m (h τ h⁻¹)))`. The same `(k, Ā, α', N)` serves `ℓ = 3` and `ℓ = 5`.

`linkedFrob_of_algFrobRed` composes this with frob-trace's proved chain
`algFrobOne_of_red : AlgFrobRed → AlgFrobOne` and `algFrobLink_of_one : AlgFrobOne → AlgFrobLink`.
The further forms apply the theorems of the later tasks:
- `linkedFrob_of_gen` uses alg-frob-red's `algFrobRed_of_gen`;
- `linkedFrob_of_goodRed_nmp` uses afr-absfrob's `algFrobRed_of_nmp`, through frob-pieces;
- `linkedFrob_of_neron_nmp` uses frob-pieces' `algFrobRed_of_neron_nmp`.

`linkedFrob_of_textbook` takes I2-Red and I2-NMP from the bundle fields `t.t4` and `t.t3`.

Only three of `LinkedFrob`'s descent-datum hypotheses are used. The others are not needed: the
scalars `a`, `n/d` and `ε`, commutation with `End`, and surjectivity. Neither are `G7Data` or the
transport property of `(Θ, h)`, since `Θ` is any additive bijection.

## 2. The remaining named Props

| Prop | kind | owner, status |
|---|---|---|
| `FrobPiecesNeron.AbVarSpreadsOut` | glue N1-g1 (textbook spreading out; EGA IV₃ 8.8.2, 8.10.5, IV₄ 17.7.8, locators UNVERIFIED) | neron-lg / frob-pieces; open (Mathlib v4.35 has no descent of schemes, properness or smoothness) |
| `FrobPiecesNeron.ProperSmoothGenConnected` | leaf candidate, published (Zariski connectedness, EGA III₁ 4.3, UNVERIFIED) | frob-pieces; open (no Stein factorization in Mathlib) |
| `PkgI2.NeronMappingAbelianScheme` (I2-NMP) | textbook leaf T3 of the bundle | proved on the fork, as a T-leaf |
| `PkgI2.ReductionTorsionBijective` (I2-Red) | textbook leaf T4 of the bundle | proved on the fork, as a T-leaf |

No new Prop is introduced by this task.

## 3. What compiles

- **Assembly** (`assemble.sh`). The files are built from verbatim copies:
  - linked-tate's prefix: `Leaves.lean` plus the imports of `imports_extra.txt`. These are linked-tate's
    three imports plus `ZInQKernel.Contrib.FrobPieces.SmoothGeomConnIntegral`, frob-pieces' Contrib
    module.
  - linked-tate's 29 parts, unchanged.
  - The **AFR block**: the two file-level `open` lines of g0-mod-field's `ModField.lean`, then the
    following files in this order:
    - frob-trace's `part_bridge_src.lean` and `part_frob.lean`;
    - mul-rigidity's `Rigidity.lean`, without its imports and without its copy of `def RigidityHom`;
    - alg-frob-red's `part_red.lean`;
    - afr-absfrob's `AbsFrobDef.lean`, without its import and without its copy of `def AbsFrob`;
    - afr-absfrob's `part_fext.lean`;
    - frob-pieces' `part_{good,neron,final,full}.lean`.

    This is the order of frob-pieces' `FrobPiecesFull.lean`. frob-trace's own prefix is
    `TateBridge.lean`, that is, g0-mod-field's `ModField.lean` plus unram-tate's section. That prefix
    is already in the file: it is linked-tate's parts 75 and 96, which differ from it only in
    `section` wrappers. Its lines 1826 onward (`section Sup`) are not used by any copied file.
  - This task's `parts/10_linkedfrob.lean` and `parts/20_bundle4.lean`.
- **Verbatim check** (`python3 scratch/linked-frob/py/verbatim_check.py`, VERIFIED all `True`):
  - Every source file above is contained verbatim in `LinkedFrob.lean`.
  - The two deleted definitions are byte-identical to the copies that stay (linked-tate's part 40 and
    alg-frob-red's `part_red.lean`).
  - `def LinkedFrob` and `def AlgFrobRed` each occur once, verbatim from their owners.
- **Olean iteration**: `olean/LPrefix` (570 s), then `olean/LTail` (linked-tate's tail, 0 errors), then
  `olean/Mine.lean`. Result: exit 0 in 79 s, 0 errors, no `sorry`, 109 axiom reports, all standard.
  VERIFIED.
- **Single file** `scratch/linked-frob/LinkedFrob.lean` (49 085 lines), compiled with
  `lake env lean`. Result: exit 0 in 628 s, 0 errors, no `sorry`, 331 `#print axioms` reports. All
  are `[propext, Classical.choice, Quot.sound]`; three are line-wrapped. They include every
  declaration in §0, and the list is in `scratch/linked-frob/flat_axioms.txt`. VERIFIED.

**Port finding** (VERIFIED). frob-trace, alg-frob-red, afr-absfrob and frob-pieces were written
against `import ZInQKernel.HDecomp.*`. linked-tate's statements live over `Leaves.lean`, which copies
those definitions into the file. The two environments cannot be imported together. All of their
files nevertheless compile unchanged over `Leaves.lean` and full `import Mathlib`; only the two
duplicate `def`s had to be dropped. So the frob chain carries over to linked-tate's world with no
edits to any proof.

## 4. What remains

- `AbVarSpreadsOut` (N1-g1) and `ProperSmoothGenConnected`. Both are owned by neron-lg and
  frob-pieces; see frob-pieces' report.
- Integration. `GluePieces4` and `sixContactMin_of_leaves4` are in `parts/20_bundle4.lean`.
  linked-tate's `GluePieces3` itself is untouched. The `rigidityHom` field of `GluePieces3` and
  `GluePieces4` is also proved in this file (mul-rigidity's `G0FibreSimple.rigidityHom`, copied), but
  it was left as a field because it is not this task's target.

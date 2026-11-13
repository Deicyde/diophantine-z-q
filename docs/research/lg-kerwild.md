# lg-kerwild: `KerWild` and `DescentPts` (local-glue) discharged on G7's data

Task lg-kerwild, 2026-11-13.

Lean: `scratch/lg-kerwild/KerWild.lean`, assembled by `scratch/lg-kerwild/build.sh` from:
- verbatim copies of `scratch/local-glue/LocalGlue.lean` (with `KerWild`, `DescentPts`,
  `localGlue_of_unramRoots`, `descentPts_baseChange`) and `scratch/frob-trace/FrobTrace.lean`
  (which contains g0-mod-field's `G7Data` and `TateBridge`, unram-tate's proof of `TateBridge`,
  g14-trace's `TateBridge35` and frob-trace's proof of it);
- a verbatim slice of `scratch/g0-dim/Dim.lean`;
- the new parts `part_kerwild.lean` (§1-§4), `part_tbk.lean` (§5, made by `mk_tbk.py`) and
  `part_final.lean` (§6).

Log: `scratch/lg-kerwild/log.md`. Compiler output: `scratch/lg-kerwild/compile.out`.

Markers: **VERIFIED** = compiled or read here. **STANDARD** = published, with a reference.
**SPECULATIVE** = my judgement. Theorem numbers from memory are **UNVERIFIED** (no network).

## 1. Result

**Both glue Props are discharged on G7's data. Neither statement was changed. Neither is false,
vacuous or inert.** local-glue's `G15Ram.localGlue_of_unramRoots` takes `KerWild K β L` and
`p ≤ 5 → DescentPts A L`. Its other inputs are R6, I2-Tors, the textbook Prop `UnramRoots`, G7's
data `G7Out` and the clauses `G7Clauses`. Both glue Props now follow from G7Data together with the
output of the Tate bridge.

The Tate bridge's output had to be corrected, as local-glue's finding G8 asked: `KerWild` was added
to `TateBridge`'s output, giving `TateBridgeK`. The corrected bridge is proved from the leaf that
`TateBridge` already used.

**Main results (VERIFIED, compiled, standard axioms only):**

```
theorem UnramTate.tateBridgeK_of_tateModuleFree (hT : PkgI3.TateModuleFree) : LGKerWild.TateBridgeK

theorem LGKerWild.tateBridge35K_of_35 (h : G14Bridge.TateBridge35) : LGKerWild.TateBridge35K
theorem LGKerWild.tateBridge35K_of_algFrobRed (hT : PkgI3.TateModuleFree)
    (hR : FrobTrace.AlgFrobRed) : LGKerWild.TateBridge35K

theorem LGKerWild.descentPts_of_g7 (hLL' : L ≤ L') (A : PkgI3.AbVar L)
    (hdim : (A.baseChange L').dim = 2) : DescentPts (A.baseChange L') L

theorem LGKerWild.exists_localGlue_of_tateModuleFree (hT : PkgI3.TateModuleFree) (hR6) (hTors)
    (hU : ∀ p ℓ, UnramRoots p ℓ) … (hD : G7Data u P L A ε N χ β L' hLL') (hdim) (hrk) (ℓ) :
    ∃ Tm c ε' a β' uu, G7Out (A.baseChange L') ℓ Tm c ε' a β' uu ∧
      ∀ p, p.Prime → p ≠ ℓ → G7Clauses β' ε' L → LocalGlue p Tm a β' L

theorem LGKerWild.localGlue_of_tateBridge35 (hR6) (hTors) (hU) (hD : G7Data …)
    (aQ βQ j5 j3 Tm5 … u3) (h5 : G7Out … 5 …) (h3 : G7Out … 3 …) (ιC) (hC : ∀ g, ιC (βQ g) = β g)
    (hCl5 : G7Clauses (j5 ∘ βQ) ε5 L) (hCl3 : G7Clauses (j3 ∘ βQ) ε3 L) :
    (∀ p ≠ 5, LocalGlue p Tm5 (j5 ∘ aQ) (j5 ∘ βQ) L) ∧ (∀ p ≠ 3, LocalGlue p Tm3 (j3 ∘ aQ) (j3 ∘ βQ) L)
```

Here `A.baseChange L'` means `@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')`, exactly as in
`TateBridge`. `KerWild`, `DescentPts` and `LocalGlue` are local-glue's own definitions.

So on G7's data, `LocalGlue` at `p ≠ ℓ` rests on:
- the leaves R6 and I2-Tors;
- the leaf I3.M0 (`PkgI3.TateModuleFree`), through the bridge;
- the textbook Prop `UnramRoots`, used at `p = 2`;
- `G7Clauses`, the transport of G7's `ℂ^×`-valued clauses (local-data's glue, not in scope here).

No `KerWild` and no `DescentPts` is left. The linked form at `ℓ = 5, 3` (`TateBridge35`, which G14
needs) supplies the same thing: `TateBridge35` already carries the clause `ι_ℂ ∘ β_ℚ̄ = β`, and
`KerWild` follows from it.

## 2. The named Props

| Prop | kind | status |
|---|---|---|
| `G15Ram.KerWild K β L` (local-glue, verbatim) | glue | proved on the bridge's data. The general form is `kerWild_of_ker`. For `TateBridge35`'s transport it is `kerWild_of_g7Data_alg`. For unram-tate's construction it is inside `tateBridgeK_of_piecesK` |
| `G15Ram.DescentPts A L` (local-glue, verbatim) | glue | proved for `A = A_{L'}` with G7Data's model `A/L` (`descentPts_of_g7`) |
| `LGKerWild.TateBridgeK` (new) | glue, **proved** from I3.M0 | g0-mod-field's `TateBridge` with `KerWild L' β' L` added to its output |
| `LGKerWild.TateBridgeT` (new) | glue | `TateBridge` with the scalar transport added to its output: `β' = j ∘ β_ℚ̄` and `ι_ℂ ∘ β_ℚ̄ = β`. It implies `TateBridgeK` (`tateBridgeK_of_T`). `TateBridge35` gives its `ℓ = 5, 3` instances (`tateBridgeT_at_of_35`) |
| `LGKerWild.TateBridge35K` (new) | glue, **proved** from `TateBridge35` | `TateBridge35` with `KerWild` at `ℓ = 5, 3` added to its output |
| `UnramTate.ScalarTransferK` (new) | glue, **proved** (`scalarTransferK`) | unram-tate's `ScalarTransfer` plus the output `γ(σ) = 1 ⟹ β(σ) = a(σ)` |

Each new `def … : Prop` has a docstring naming its step (G7/G8, N5 L702-722) and source.

## 3. What is proved

All rows are VERIFIED: `lake env lean scratch/lg-kerwild/KerWild.lean` exits 0 with 0 errors and no
`sorry` (about 60 s). All 21 `#print axioms` lines are `[propext, Classical.choice, Quot.sound]`.

| Lean (`LGKerWild.` unless noted) | statement | proof idea |
|---|---|---|
| `kerWild_of_ker` | `G_{L'} = G_L ∩ ker β_ℂ`, `L'` finite Galois, `β_ℓ(g) = 1 ⇒ β_ℂ(g) = 1` ⟹ `KerWild L' β_ℓ L` | local-glue's copy of `resQ_range`: `resQ_{L'}(G_{L'}) = Fix(L')` |
| `transport_one`, `kerWild_of_alg` | `β_ℓ = j ∘ β_ℚ̄`, `β_ℂ = ι_ℂ ∘ β_ℚ̄` ⟹ the hypothesis above | `j` is a ring hom from a field, so injective |
| `g7Data_ker`, `kerWild_of_g7Data_alg` | G7Data's clause 9 is `hker`; `KerWild L' (j ∘ β_ℚ̄) L` from G7Data and `ι_ℂ ∘ β_ℚ̄ = β` | `GQL L = L.fixingSubgroup` holds by definition |
| `tateBridge_of_K`, `tateBridgeK_of_T` | `TateBridgeK → TateBridge`; `TateBridgeT → TateBridgeK` | the above |
| `tateBridge35K_of_35` | `TateBridge35 → TateBridge35K` | `kerWild_of_g7Data_alg` at `j₅` and at `j₃` |
| `tateBridgeT_at_of_35`, `tateBridgeK_at_of_35` | `TateBridge35` gives the `ℓ ∈ {5, 3}` conclusions of `TateBridgeT` and of `TateBridgeK` | the same |
| `UnramTate.scalarTransferK` | `ScalarTransferK` | unram-tate's proof of `scalarTransfer`, plus one step: `ψ` is injective, so `ψ(β/a) = 1 ⇒ β = a` |
| `UnramTate.tateBridgeK_of_piecesK` | `TatePoints`, `EndBaseChange`, `ScalarTransferK`, `TateCont`, `ResQEmbedding` ⟹ `TateBridgeK` | unram-tate's proof of `tateBridge_of_pieces`, copied verbatim up to its final `refine`, plus `KerWild` (below) |
| **`UnramTate.tateBridgeK_of_tateModuleFree`** | I3.M0 ⟹ `TateBridgeK` | unram-tate's proved pieces (`tatePoints`, `endBaseChange`, `tateCont_of_tateModuleFree`, `resQEmbedding`) and `scalarTransferK` |
| `tateBridge35K_of_algFrobRed` | I3.M0 + `AlgFrobRed` ⟹ `TateBridge35K` | frob-trace's `tateBridge35_of_algFrobRed`, then `tateBridge35K_of_35` |
| `dim_model_of_bc` | `dim A_{L'} = 2 ⟹ dim A = 2` | g0-dim's `pkgI3_dim_baseChange` (dimension is invariant under field base change; Stacks 00P4, UNVERIFIED locator) |
| **`descentPts_of_g7`** | `DescentPts (A_{L'}) L` for the model `A/L`, given `dim A_{L'} = 2` | local-glue's `descentPts_baseChange` (conjugate model, finding G9) and `dim_model_of_bc` |
| `localGlue_of_transport`, **`localGlue_of_tateBridge35`** | `LocalGlue` on `TateBridge35`'s data at `ℓ = 5, 3`, from R6, I2-Tors, `UnramRoots` and `G7Clauses` | `localGlue_of_unramRoots`, `kerWild_of_g7Data_alg`, `descentPts_of_g7` |
| `localGlue_of_kerWild`, `exists_localGlue_of_tateBridgeK`, **`exists_localGlue_of_tateModuleFree`** | `LocalGlue` on `TateBridgeK`'s data at every `ℓ`, given `G7Clauses` | the same, with `KerWild` taken from `TateBridgeK` |

**Why `KerWild` holds in unram-tate's construction.** That construction has `a' = 1` and
`β'(g) = γ(hgh⁻¹)` with `γ = ψ ∘ (β/a)`. Take `g ∈ G_L` with `β'(g) = 1`. Then:
- `hgh⁻¹ ∈ G_L`, because `G_L` is normal (`L/ℚ` is Galois);
- `a = 1` on `G_L` (DescentDatum), so `β(hgh⁻¹) = 1` (by `ScalarTransferK`);
- `hgh⁻¹ ∈ G_{L'}` by G7Data's clause;
- so `g ∈ G_{L'}`, because `G_{L'}` is normal;
- and `G_{L'} = resQ_{L'}(G_{L'})` (`resQ_range`).

## 4. Findings

- **K1 (VERIFIED, compiled). The correction G8 costs nothing.** `KerWild` is G7Data's clause
  `G_{L'} = G_L ∩ ker β`, carried through the bridge. On both bridges it is a theorem:
  - on `TateBridge` (all `ℓ`), as `TateBridgeK`, from I3.M0;
  - on `TateBridge35` (`ℓ = 5, 3`), as `TateBridge35K`, from `TateBridge35` itself.

  So `TateBridgeK` and `TateBridge35K` can replace `TateBridge` and `TateBridge35` with no new
  hypothesis.
- **K2 (VERIFIED, read). g0-assemble2's GLUE field 39 `LinkedTateLocal` keeps neither the
  transport nor `KerWild`.** Its statement is in `scratch/g0-assemble2/parts/a85_linked.lean`,
  l.2142-2173. It concludes `LocalData` directly, for data `(aQ, βQ, j₅, j₃, …)` that are only
  existentially quantified. Unlike `TateBridge35`, it has no clause `ι_ℂ ∘ β_ℚ̄ = β`.
  - As a glue Prop this is consistent. To prove it through local-glue, take the data from
    `TateBridge35K` (or `TateBridge35`): then `KerWild` and `DescentPts` are discharged by
    `localGlue_of_tateBridge35`.
  - Two inputs of that route are still missing, and neither is a `KerWild` or `DescentPts` issue:
    1. `G7Clauses` for the transported data. This includes local-data's finding F3: `G7Data`
       does not carry `[L:ℚ] ≤ D`.
    2. The hypotheses `dim A_{L'} = 2` and `rank End = 4` of `TateBridge35`.
    `LinkedTateLocal` assumes only `FibreCtx` and `G7Data`.
- **K3 (VERIFIED, compiled). The dimension of a base change is no longer a gap.** local-glue §5
  noted that "dim of a base change along a field extension is not proved here". g0-dim's
  `pkgI3_dim_baseChange` proves it. So `DescentPts` needs only `dim A_{L'} = 2`, which `G7Out` and
  the bridges' hypotheses already contain.
- **K4 (VERIFIED, compiled). The copies agree definitionally.** Several pairs are accepted in
  place of each other by the elaborator and kernel without any transport lemma:
  - g0-mod-field's `GaloisCopy.G7Out` and local-data's `G0Galois.G7Out`;
  - `G0ModField.incAlg` and local-glue's `incAlgL`;
  - the two `numberField_of_fd` (instances of a `Prop`).

## 5. What remains

1. Integration: replace `TateBridge35` with `TateBridge35K` (or prove `LinkedTateLocal` from
   `TateBridge35` data through `localGlue_of_tateBridge35`). `KerWild` and `DescentPts` then
   disappear from the G15 side. The `ℓ = 5, 3` data then still need `G7Clauses`, which is
   local-data's glue (with its F3 fix `[L:ℚ] ≤ D`).
2. `UnramRoots` (local-glue's textbook Prop, `p = 2`) is unchanged.

## 6. Compile record

- `lake env lean scratch/lg-kerwild/KerWild.lean`: exit 0, 0 errors, no `sorry`, about 60 s. All 21
  `#print axioms` lines are standard (`compile.out`). The file is 8.9k lines.
- Before the first compile, `lake build` of the 25 imported `ZInQKernel` modules: success.
- Verbatim copies, VERIFIED by construction (`cat`/`sed` in `build.sh`):
  - `scratch/local-glue/LocalGlue.lean`, whole body;
  - `scratch/frob-trace/FrobTrace.lean`, whole body except l.1632-1754. These lines are
    unram-tate's BCPoints block, already in LocalGlue.lean (local-glue's `bc_block.lean`
    l.11-134); `diff` shows them identical modulo blank lines;
  - `scratch/g0-dim/Dim.lean` l.107-305 and l.339-344.
- Copied proofs:
  - unram-tate's `scalarTransfer` (`TateBridge.lean` l.1501-1575), in `part_tbk_head.lean`;
  - `tateBridge_of_pieces` (l.1303-1423, by `mk_tbk.py`, with three listed edits).

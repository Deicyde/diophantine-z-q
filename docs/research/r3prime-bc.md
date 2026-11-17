# r3prime-bc: condition (ii) proved, so R3′ holds with no reading note

Task r3prime-bc, 2026-11-17. This is a follow-up to r3prime-etale, on the same branch `wip/r3prime-etale`; the two fold together.

- **Lean.** `ZInQKernel/Contrib/OneProof/HolChartBC.lean`, namespace `ZInQ.R3BC`. It imports `HolChartSerre` and `CloudB3W17Hodge.Bridge`.
- **Scratch.** `scratch/r3prime-bc/`: `log.md`; `R3BC.lean`, the development copy; `Discharges.lean` and its output; `autofold.json`.

**Result (VERIFIED: compiled, no warnings; the axioms are `propext`, `Classical.choice` and `Quot.sound`).** r3prime-etale's reading note (a) is now a theorem. That note said: the regular functions of the model `𝒢` over `𝓞_L` give the same sheaf as those of the base change `𝒢 ×_{𝓞_L,τ} Spec ℂ`.

Concretely, the `IsHolChart` atlas is the atlas of **Serre's complex space of the `ℂ`-scheme `𝒢 ×_τ ℂ`**:
- the points are `CPt` of the base change, with Bridge's `classicalTopology`;
- the structure sheaf is built from the base change's own regular functions.

The proof uses T35 only, the hypothesis every consumer already has. There is no new leaf and no new hypothesis.

```lean
theorem ZInQ.R3BC.isHolChart_iff_isBCSerreChart [NumberField K] (𝒢 : GroupModel A L) (τ : L →+* ℂ)
    (hT35 : ZInQ.LeafPush2.UniformizationExists) (g : ℕ) (hg : A.dim = (g : WithBot ℕ∞))
    (φ : @OpenPartialHomeomorph (𝒢.Pts τ) (Fin g → ℂ) (anTop 𝒢 τ) _) :
    IsHolChart 𝒢 τ φ ↔ IsBCSerreChart (bc 𝒢 τ) (pushChart 𝒢 τ φ)
```

`isBCSerreChart_iff_isHolChart` is the same equivalence for charts given on the base change.

**ON THE SPOT.** Neither this identification nor r3prime-etale's is in the manuscript or its bibliography. The manuscript uses the stable Faltings height of the literature.

## 1. The four parts of the brief

### (1) Homeomorphism

- **Base change.** `bc 𝒢 τ := Over.mk (pullback.fst (Spec τ|_{𝓞_L}) 𝒢.G.hom) : Over (Spec ℂ)`.
- **Equivalence.** `ptsEquivBC : 𝒢.Pts τ ≃ CPt (bc 𝒢 τ)` sends `p` to `(id, p)`. The inverse is `P ↦ P ≫ pr`.
- **Evaluation.** `xevalAt_toBC`: `XevalAt (pr⁻¹U) (pr^* s) (toBC p) = 𝒢.evalAt p U s`.
- **Topology.** `anTop_eq_induced`: `anTop 𝒢 τ = induced toBC (classicalTopology (bc 𝒢 τ))`.
- **Homeomorphisms.**
  - `ptsHomeomorph : (𝒢.Pts τ, anTop) ≃ₜ (CPt (bc 𝒢 τ), classicalTopology)`.
  - `ptsHomeomorphPort` composes it with Bridge's `cptHomeomorph`, giving the vendored port's `Point ℂ` with its `analyticTopology`.
  - `chartedSpacePts`: if `bc 𝒢 τ` is smooth of relative dimension `d`, the vendored atlas transports to `𝒢.Pts τ`.
- **Reused from Bridge:** `xevalAt_eq_evaluate`, `ptIn_iff`, `classicalTopology_eq` (in `isOpen_evalSet`), `cptHomeomorph` and `chartedSpace`.

`ptsEquiv` in `H5GlueMinimal.lean` was not reused. Its target is `L`-morphisms into the generic fibre over `Spec L`, not `ℂ`-points of a `ℂ`-scheme. The direct pullback over `𝓞_L` is the base change the brief asks for, and building it directly avoids a pullback-pasting step.

### (2) Sheaf comparison

**The key algebraic step is `bc_formula`.** Take a section `σ ∈ Γ(bc, W)` and a point `q` with `toBC q ∈ W(ℂ)`. Then there are
- an open `V ∋ q` of `𝒢`,
- regular functions `c_j ∈ Γ(𝒢, V)`, and
- constants `u_j, v_j ∈ ℂ` and an exponent `N`,

with `σ(x)·(Σ v_j c_j(x))^N = Σ u_j c_j(x)` near `q`, and `Σ v_j c_j(q) ≠ 0`. This holds because `Γ(Spec ℂ ×_{𝓞_L} V) = ℂ ⊗ Γ(V)`, via Mathlib's `pullbackSpecIso`. The proof is r3prime-etale's `exists_tensor_formula` with `X = Spec ℂ` and `a = id`.

**The sheaf on the base change.** `BCHolAt X h P` is Serre's sheaf (GAGA §2; UNVERIFIED numbering) of an arbitrary `ℂ`-scheme `X`:
- the topology is the classical topology of `CPt X`;
- the generators are the regular functions of `X` itself.

**The comparison.** `bcHolAt_iff : BCHolAt (bc 𝒢 τ) k (toBC q) ↔ AnHolAt 𝒢 τ (k ∘ toBC) q`, with the variant `anHolAt_iff_bcHolAt`.
- `⇐`: pull back `s_j` along `pr` and use `xevalAt_toBC`.
- `⇒`: each base-change function is `AnHolAt` (`anHolAt_bc`, from `bc_formula`). Then combine them using r3prime-etale's `anHolAt_pi` and the chain rule.

### (3) Unit-germ charts

- `bcHolAt_chartAt`: each coordinate of `HeightFix.chartAt 𝒢 τ U s q`, read on the base change, is `BCHolAt` at every point of its domain. The proof uses `translationAnHol` and `bcHolAt_iff`.
- `unitGermChart_bc`: any `IsHolChart` chart, pushed to the base change, is an `IsBCSerreChart`, and the unit-germ coordinates centred at `q` are `BCHolAt` at `toBC q`.
- `exists_bcSerreChart_at`: Serre charts of `((𝒢 ×_τ ℂ)(ℂ), 𝒪^an)` exist at every point.

### (4) Restatement

`IsBCSerreChart X φ` says that `φ` is an isomorphism of ringed spaces from an open subset of `(CPt X, classicalTopology, BCHolAt)` onto an open subset of `ℂ^g`. `pushChart` and `pullChart` move charts along `ptsHomeomorph`.

`isHolChart_iff_isBCSerreChart` is `isHolChart_iff_isSerreChart'` composed with `isSerreChart_pullChart_iff` and `pullChart_pushChart`.

## 2. Checks

- `lake env lean scratch/r3prime-bc/R3BC.lean` and `lake env lean ZInQKernel/Contrib/OneProof/HolChartBC.lean`: no errors and no warnings (VERIFIED).
- `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.HolChartBC`: "Build completed successfully (16217 jobs)" (VERIFIED). `frozenTarget` uses only the standard axioms.
- `#discharges` (`scratch/r3prime-bc/discharges-output.txt`, exit 0):
  - 19 `DISCHARGES` lines, all from contribution modules already in the tree; none is from `ZInQ.R3BC`. This is expected: R3′ is a reading step inside `IsAnMetricSq`, not a bundle field.
  - `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for `ptsHomeomorph`, `anTop_eq_induced`, `bcHolAt_iff`, `isHolChart_iff_isBCSerreChart`, `isBCSerreChart_iff_isHolChart`, `exists_bcSerreChart_at` and `unitGermChart_bc`.

## 3. Rows, autofold, leaves

- **Autofold.** There is no fold to run. `scratch/r3prime-bc/autofold.json` has an empty `discharges` list and a `flag_updates` entry. The updates supersede r3prime-etale §5: for `bostLowerBoundAn(SS)`, `gaudronRemondThm14An(SS)` and `javanpeykarThm111(An)` the R3′ caveat is dropped with **no reading note**, so it no longer reads "(ii) pending". The other per-row items are unchanged.
- **Count.** Count-neutral.
- **New leaves.** None. T35 is an existing textbook field. No printed-form rating is needed.

## Manuscript check

No manuscript step is formalized or relied on. The task identifies the project's chart and sheaf notions with each other (ON THE SPOT, as for r3prime-etale), and the manuscript only uses the stable Faltings height of the literature (diophantine_zq.tex L598, L872).

## Known issues

None found in sources. Remark: `anTop`'s docstring in `TailZ.lean` (around line 870) asserts that `anTop` is the analytic topology of `(𝒢 ×_{𝓞_L,τ} ℂ)(ℂ)`. `anTop_eq_induced` now proves this.

# r3prime-etale: R3′ proved — the `IsHolChart` atlas is the complex structure of `A_τ(ℂ)^an`

Task r3prime-etale, 2026-11-17. Base `wip/r3prime-etale` = `wip/leaf-fold33b` 74395dcf0 with `origin/wip/jp-an-retype`
21c537727 merged (115cb119b). Lean: `ZInQKernel/Contrib/OneProof/HolChartSerre.lean` (namespace `ZInQ.R3Etale`,
imports `ZInQKernel.Contrib.OneProof.AnalyticStableHeight` only). Scratch: `scratch/r3prime-etale/` (log,
development copies `R3Etale.lean` and `THGeneric.lean`, `Discharges.lean` and its output, autofold note).

**ON THE SPOT.** The identification proved here is not in the manuscript, which uses the stable Faltings height
of the literature (diophantine_zq.tex L598, L872). Serre's GAGA §2 and SGA 1 XII are not in its bibliography.
The argument is in Lean, with no new leaf.

## 1. Result

VERIFIED (compiled; axioms `propext`, `Classical.choice`, `Quot.sound` only):

```lean
theorem ZInQ.R3Etale.isHolChart_iff_isSerreChart' (hT35 : ZInQ.LeafPush2.UniformizationExists)
    (𝒢 : GroupModel A L) (g : ℕ) (hg : A.dim = (g : WithBot ℕ∞)) (τ : L →+* ℂ)
    (φ : @OpenPartialHomeomorph (𝒢.Pts τ) (Fin g → ℂ) (anTop 𝒢 τ) _) :
    IsHolChart 𝒢 τ φ ↔ IsSerreChart 𝒢 τ φ
```

`IsHolChart` is r3-residual's chart notion (`AnalyticStableHeight.lean` ~L168, unchanged).

`IsSerreChart` is the chart notion of **Serre's complex space** `(A_τ(ℂ), 𝒪^an)`. This structure is defined from
regular functions, not from étale coordinates (§2). The only hypothesis is T35, the textbook leaf that every
consumer of `IsHolChart` already assumes (`exists_holChart_at`, `isAnStableHeight_iff`, …). It is filled in the
tree by `uniformizationLeafAll_proof` and `mumfordTorsionAlgClosed`.

Consequences, also VERIFIED:

* `exists_serreChart_at`: Serre charts exist at every point.
* With r3-residual's `holChart_transition`, `(A_τ(ℂ), 𝒪^an)` is a complex manifold, and its atlas is the
  `IsHolChart` atlas.
* `isSerreMetricSq_iff (hT35) 𝒢 g hg τ eta r : IsSerreMetricSq 𝒢 τ eta r ↔ IsAnMetricSq 𝒢 τ eta r`. Here
  `IsAnMetricSq` is the archimedean metric on which r3-residual's `IsAnStableHeight`, semistab-assembly's
  `IsAnStableHeightSS` and jp-an-retype's `IsStableHeightBarAn` are built. `IsSerreMetricSq` is the same
  definition with the densities read in Serre's charts.
* Hence the height predicates of the rows `bostLowerBoundAn`, `gaudronRemondThm14An` and `javanpeykarThm111(An)`
  are, provably, the print's metric integrated over Serre's `A_τ(ℂ)^an`.

**R3′ is removed from these rows** (§5).

## 2. The definitions (in `HolChartSerre.lean` §1)

* `AnHolAt 𝒢 τ h q`: near `q` (for the analytic topology `anTop`), `h = H(s₁, …, s_m)`.
  - The `s_j ∈ Γ(U_j, 𝒪_𝒢)` are regular functions with `q ∈ U_j(ℂ)`.
  - `H` is holomorphic (complex differentiable) near `(s_j(q))_j ∈ ℂ^m`.
  - This is Serre's sheaf of the reduced analytic space (GAGA §2; SGA 1 XII 1.1; UNVERIFIED numbering, sources
    not on the host). It is the same definition as gaga-serre's `SerreHolAt`, which is on `CPt X` for `X` over
    `Spec ℂ`.
  - It uses the same generators as the project's `anTop`.
* `IsSerreChart 𝒢 τ φ`: for every `q ∈ φ.source` and every `h : 𝒢.Pts τ → ℂ`, `AnHolAt 𝒢 τ h q ↔ h ∘ φ⁻¹` is
  holomorphic near `φ q`. That is, `φ` is an isomorphism of ringed spaces from
  `(φ.source, 𝒪^an)` onto `(φ.target, 𝒪_{ℂ^g})`.

No étale coordinate, uniformization or `IsHolChart` enters these definitions. The circularity the brief warned
about, where the vendored `ComplexPoint` atlas is itself built from étale coordinates, therefore does not arise.

Reading notes:

* (a) STANDARD, not proved in Lean: `AnHolAt` uses regular functions of the model `𝒢` over `𝓞_L`, not of the
  base change `𝒢 ×_{𝓞_L,τ} ℂ`. The two sheaves agree. On the affine opens `V ×_{𝓞_L} ℂ`, which cover the base
  change, `Γ = Γ(V) ⊗_{𝓞_L} ℂ`, so a regular function of the base change is a ℂ-linear combination of
  `𝒢`-functions, and `H` absorbs the coefficients. This is the same reading as `anTop`'s own docstring, which
  calls `anTop` the analytic topology of the base change.
* (b) "holomorphic" means complex differentiable on a neighbourhood, the convention of `IsHolChart` and of the
  whole file. It is equivalent to analytic (STANDARD).
* (c) A bridge to gaga-serre's `SerreHolAt` on `CPt (𝒢 ×_τ ℂ)` would need a homeomorphism
  `𝒢.Pts τ ≃ₜ CPt(𝒢 ×_τ ℂ)` matching evaluation. The tree has none (survey fact iii), and none is needed here.

## 3. The proof

1. **§0, algebraic, no analysis** (`exists_tensor_formula`).
   - Setup: `X`, `Y` over an affine `Spec R₀`, a section `σ` of `X ×_{R₀} Y` over `W`, and complex points
     `a`, `b₀` with `(a, b₀) ∈ W(ℂ)`.
   - Conclusion: there are an open `V ∋ b₀` of `Y`, sections `c_j ∈ Γ(Y, V)` and constants `u_j`, `v_j`, `N`
     with `σ(a, b) · (Σ v_j c_j(b))^N = Σ u_j c_j(b)` for all `b ∈ V(ℂ)` with `Σ v_j c_j(b) ≠ 0`. The
     denominator is nonzero at `b₀`.
   - Proof:
     - Take affine opens `V₁ ∋ a` and `V₂ ∋ b₀`, with `V_i → Spec R₀` given by `Spec.preimage`.
     - `V₁ ×_{R₀} V₂ ≅ Spec(Γ(V₁) ⊗ Γ(V₂))` by Mathlib's `pullbackSpecIso`, and it is open in the product by
       Mathlib's open-immersion instance for `pullback.map`.
     - The complex points `(a, b)` are `Spec` of `α ⊗ β_b` (`Algebra.TensorProduct.lift`).
     - Near `(a, b₀)` the section is a fraction `t / r^N` on a basic open (`exists_fraction`, from Mathlib's
       `isLocalization_basicOpen`).
     - Finally decompose `t` and `r` into sums of pure tensors.
2. **§1b, translation** (`translationAnHol`).
   - Apply step 1 to `X = Y = 𝒢` and `σ = μ^* s`, using `p * x = lift p x ≫ μ`, which holds by `rfl`.
   - This gives `s(p x) = (Σ αₖ(p) βₖ(x)) / (Σ aⱼ(p) cⱼ(x))^N` near `x₀`, so `x ↦ s(p x)` is `AnHolAt`.
   - So left translation by a complex point is holomorphic for Serre's sheaf. The `IsHolChart` coordinates
     `F(q⁻¹ ·)` (`chartAt`) are translates, which is why this step is needed in both directions.
3. **§3, along a uniformization `Φ` from T35.**
   - `holo_of_anHolAt`: if `h` is Serre-holomorphic at `Φ z`, then `h ∘ Φ` is holomorphic near `z`.
   - `anHolAt_of_holo` gives the converse. It writes `h = (h ∘ Φ) ∘ σ ∘ H_k ∘ (regular functions)`, where:
     - `chartAt F q = H_k(t₁, …, t_m)` near `q`, by step 2;
     - `σ` is the holomorphic local inverse of `chartAt F q ∘ Φ`, whose derivative at `z` has determinant
       `jacDet ≠ 0` (r3-residual's `chart_comp_unif`, `jacDet_ne_zero`);
     - `Φ` is an open map (`TorusVolume.IsUnif.isOpenMap`).
4. **§4, the equivalence.**
   - `⇒`: `φ ∘ Φ` is a local biholomorphism (r3-residual's `unif_holChart`). Then
     `AnHolAt h q ⇔ h ∘ Φ` is holomorphic, by step 3, and this holds `⇔ h ∘ φ⁻¹` is holomorphic, by
     `holo_in_chart_of_lift` and the chain rule.
   - `⇐`, in two parts:
     - Each component of `chartAt F q` is `AnHolAt` (step 2), so `chartAt F q ∘ φ⁻¹` is holomorphic.
     - The components of `φ` are `AnHolAt`, since `φ_i ∘ φ⁻¹` is a coordinate function, so `φ ∘ Φ` is
       holomorphic. Then `D(chartAt F q ∘ Φ)(z) = D(chartAt F q ∘ φ⁻¹)(φ q) ∘ D(φ ∘ Φ)(z)` has nonzero
       determinant, hence so does the first factor.

What was not used:

* the sga1-etale leaf `SGA1_XII_3_1_Etale` (not reintroduced);
* sga1-fix's `SGA1_XII_3_3a`;
* the vendored `ComplexPoint` atlas and the Oka branch.

**Pivot (as the brief allowed).** The general statement, that étale coordinates on any smooth `ℂ`-variety are
holomorphic charts, is not proved here. For the consumers' setting, the points of a `GroupModel` at `τ` with
translated charts, T35 supplies the local biholomorphism, and the algebra of step 1 supplies translation.

The general case would need one of two inputs:

* the analytic implicit function theorem on `V(ℂ) ⊂ ℂ^n` for a standard-smooth presentation, plus a topological
  bridge from `anTop` to the subspace topology of `ℂ^n`. This is the content of sga1-fix's remaining leaf
  `SGA1_XII_3_3a`. The vendored `ComplexPoint/Etale.lean` has the IFT charts, but on `CPt` over `Spec ℂ`.
* or Osgood's theorem (an injective holomorphic map `ℂ^g → ℂ^g` has nonvanishing Jacobian), which is not in
  Mathlib.

## 4. Checks

* `lake env lean scratch/r3prime-etale/R3Etale.lean` and
  `lake env lean ZInQKernel/Contrib/OneProof/HolChartSerre.lean`: VERIFIED, no errors and no warnings.
* `#print axioms` of `exists_tensor_formula`, `translationAnHol`, `isHolChart_iff_isSerreChart'` and
  `isSerreMetricSq_iff`: `[propext, Classical.choice, Quot.sound]` (VERIFIED).
* `#discharges`: §6.

## 5. The rows after R3′ (proposed flag text; ratings are the reviewer's)

None of the three rows changes statement. Only the R3′ caveat is removed from each flag.

* **`bostLowerBoundAn`** (and `bostLowerBoundAnSS`): "R3′ closed by r3prime-etale
  (`ZInQ.R3Etale.isHolChart_iff_isSerreChart'`, `isSerreMetricSq_iff`): the IsHolChart atlas is the atlas of
  Serre's `(A_τ(ℂ), 𝒪^an)`, from T35, so the height is the print's metric over `A_τ(ℂ)^an`. Remaining: display
  UNVERIFIED; Deligne normalization `h_D = h_F + (g/2) log π`; locator UNVERIFIED; Bost row being re-routed
  (background only)."
* **`gaudronRemondThm14An`** (and `gaudronRemondThm14AnSS`): "R3′ closed by r3prime-etale (same theorems).
  Remaining: the statement check of GR Thm 1.4 and κ against the print (locator read by the audit). The row is a
  printed-form candidate once the readings land."
* **`javanpeykarThm111`** (and `javanpeykarThm111An` from jp-an-retype): "R3′ closed by r3prime-etale (same
  theorems; `IsStableHeightBarAn` is built on `IsAnMetricSq`). Remaining: the lead's ruling on the composite
  Thm 1.1.1 + §2.3 (`h_Fal(X) = h_Fal(Jac X)`), and the definition-level readings (Faltings' stable height
  independent of the field and model; `IsBelyiMap` by ramification indices)."

**Count.** The change is count-neutral by itself, as the brief said. It removes the shared reading step, so
each row's rating now depends only on its own print.

## 6. `#discharges` and autofold

`lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.HolChartSerre`
finished with "Build completed successfully (16216 jobs)" (VERIFIED). `frozenTarget` uses only the standard axioms.

`lake env lean scratch/r3prime-etale/Discharges.lean` exits 0. Its output is in
`scratch/r3prime-etale/discharges-output.txt` (VERIFIED):

* The output has 19 `DISCHARGES` lines. All of them come from contribution modules already in the tree (for
  example `CarayolPrinted`, `DeRhamPrint`) that the import pulls in. **None is by `ZInQ.R3Etale`.** This is
  expected: R3′ was a reading step inside three leaves' height predicate, not a bundle field.
* The `#print axioms` lines for `exists_tensor_formula`, `translationAnHol`, `isHolChart_iff_isSerreChart'`,
  `exists_serreChart_at` and `isSerreMetricSq_iff` all give `[propext, Classical.choice, Quot.sound]`.

So there is no fold to run. `scratch/r3prime-etale/autofold.json` records an empty `discharges` list and the
flag updates of §5 under `flag_updates`. It is not a spec for `autofold.py`; no dry run is applicable.

## 7. New leaves

None. T35 (`ZInQ.LeafPush2.UniformizationExists`) is an existing textbook field.

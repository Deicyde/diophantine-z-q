# height-dict: statements copied verbatim (base 2880fef1e)

From `ZInQKernel/OneProof/H/TailY.lean` (namespace `ZInQ.HeightSplit`):

```lean
/-- **Faltings' stable height (original normalization `(i/2)^g`), the published definition**:
`x` is the height of the Néron model of `A_L` for some number field `L ⊇ K` over which `A` has
semistable reduction everywhere (Faltings 1983 §1; Deligne, Sém. Bourbaki 616, §1; UNVERIFIED
locators). The height of a group model `𝒩.height` is the kernel's (the metrized Hodge line
`⋀^g ω_𝒩`, `‖η‖²_σ = (i/2)^g ∫ η ∧ η̄`; one value for all metrizations given the uniqueness
half of AN3, `MetrizedModel.modelHeight_eq_of_model_eq`). Independence of `L` is
`isStableFaltingsHeight_unique` below (from SGA 7 IX 3.3). -/
def IsStableFaltingsHeight {K : Type} [Field K] (A : PkgI3.AbVar K) (x : ℝ) : Prop :=
  ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (𝒩 : GroupModel A L),
    𝒩.IsNeronModel ∧ IsSemistable 𝒩 ∧ 𝒩.height = (x : EReal)

/-! ## §C. H-17, R21 (Bost) -/

/-- **Leaf R21-Bost. Bost's lower bound** (J.-B. Bost, *Périodes et isogénies des variétés abéliennes
sur les corps de nombres*, Sém. Bourbaki 795 (1994/95), Astérisque 237 (1996); the display is
UNVERIFIED: locators.md could not read it). Recalled display: `h(A) ≥ −(g/2) log(2π)` for every
abelian variety of dimension `g` over a number field, `h` the stable height in Deligne's
normalization `(i/2π)^g`, `h_D = h_F + (g/2) log π`. Stated in Deligne's normalization, the weaker of
the two readings (a Faltings-normalized display `h_F ≥ −(g/2) log 2π` implies it, as `h_D ≥ h_F`; the
Faltings-normalized reading is false for `E` with `j = 0`, `h_F ≈ −1.32`, so Deligne's is the one
meant). Residual risk: if Bost printed in a third normalization giving larger heights, e.g.
`(i/4π)^g`, this leaf would be stronger than the print; R21 itself needs only `h_F ≥ −(3/2)g`. -/
def BostLowerBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
    ∀ x : ℝ, IsStableFaltingsHeight A x →
      -((g : ℝ) / 2 * Real.log (2 * Real.pi)) ≤ x + (g : ℝ) / 2 * Real.log Real.pi


/-- **Leaf R19-GR over the published height** (Gaudron–Rémond, Duke Math. J. 163 (2014), Thm 1.4,
p. 2060; `κ` and `α(g) = 1024g³`, p. 2058; read by the locator audit): the kernel's
`R19_GaudronRemond` with `stableFaltingsHeight A = x` replaced by `IsStableFaltingsHeight A x`
(GR use the stable height in Faltings' original normalization). -/
def GaudronRemondThm14 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : PkgI3.AbVar K) (g : ℕ) (x : ℝ),
    A.dim = (g : WithBot ℕ∞) → IsStableFaltingsHeight A x →
    (∃ φ : A.X ⟶ B.X, IsIsogeny φ) →
    (∃ φ : A.X ⟶ B.X, IsIsogeny φ ∧ (isogDeg φ : ℝ) ≤ grKappa g (Module.finrank ℚ K) x) ∧
    (∃ ψ : B.X ⟶ A.X, IsIsogeny ψ ∧ (isogDeg ψ : ℝ) ≤ grKappa g (Module.finrank ℚ K) x)

```

From `ZInQKernel/HDecomp/Faltings/Height.lean` (namespace `ZInQ.DefFaltings`):

```lean
  rw [hD', HodgeData.modelHeight_recoord]

/-- **The height of a group model** `h(A_L, 𝒢)`: the infimum over its metrizations (all of which
have the same height, `MetrizedModel.modelHeight_eq_of_model_eq`, given the uniqueness half of
AN3). -/
noncomputable def GroupModel.height (𝒢 : GroupModel A L) : EReal :=
  ⨅ (g : ℕ) (M : MetrizedModel A L g) (_ : M.model = 𝒢), (M.hodge.modelHeight : EReal)

```

Bundle fields (`ZInQKernel/OneProof/H/TailZ41.lean`, `HDec.HSyn.OpenResearchLeaves26`):

```lean
25:  bostLowerBound : _root_.ZInQ.HeightSplit.BostLowerBound
32:  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14
```

The discharge theorems have exactly these types (checked by `#discharges`, scratch/height-dict/discharges.txt).

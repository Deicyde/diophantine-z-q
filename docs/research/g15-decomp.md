# g15-decomp: the decomposition-group transport for G15

Task g15-decomp, branch `wip/g15-decomp`, 2026-11-13. Six new Lean files under
`ZInQKernel/Contrib/G15/`. All of them compile at the project pins (Lean 4.35.0, Mathlib
56a00585). They contain 132 declarations. `#print axioms` on each of them gives exactly
`[propext, Classical.choice, Quot.sound]` (VERIFIED: `scratch/g15-decomp/Axioms.lean`, output in
`scratch/g15-decomp/axioms-out.txt`). No `sorry`, no `axiom`, no existing file edited.

## 1. Main results (exact types)

The statement "`D_P ≅ Gal(L_P/ℚ_p)` with the lower ramification filtrations" (marked STANDARD and
"not in Lean" in the G15 row of `h-decomposition.md`) is now proved in two readings of `L_P`.
The second reading is the one used by `G15RamG` (`scratch/g0-mod-newform/NewForm.lean`, the
`LadicCond` objects):

* **(A)** `L_P` is Mathlib's `w.adicCompletion L`, with Tau Ceti's local filtration (file
  `Transport.lean`).
* **(B)** `L_P` is the kernel's `LadicCond.Fld p` object `Lj j = ℚ_p(j L) ⊆ ℚ̄_p`, with
  `LadicCond.ramSet`, `ramCard`, `ramSetR`, `ramCardR`, `phiAt`, `upperSet` and `upperAbs` (files
  `LadicBridge.lean`, `LadicD1.lean`, `LadicUpper.lean`).

`Combined.lean` shows that (A) and (B) agree.

### (A) `ZInQ.Contrib.G15` (`Transport.lean`)

Context: `{L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 ℚ))
(w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]`. The declarations from
`decompEquiv` on also assume `[IsGalois ℚ L]`.
`LocalGal v w := w.adicCompletion L ≃ₐ[v.adicCompletion ℚ] w.adicCompletion L` and
`localRam v w i := TauCeti.LocalFieldsRamification.lowerRamificationGroup (v.adicCompletion ℚ)
(w.adicCompletion L) (i : ℤ)`.

```lean
theorem ramGroup_eq_ramificationGroup (P : Ideal (𝓞 L)) (i : ℕ) :
    GlueConductor.ramGroup L P i = P.ramificationGroup Gal(L/ℚ) i
theorem mem_ramGroup_iff_decompositionHom_mem (i : ℕ) (σ : GlueD1Local.decompGroup L w.asIdeal) :
    (σ : Gal(L/ℚ)) ∈ GlueConductor.ramGroup L w.asIdeal i ↔
      HeightOneSpectrum.decompositionHom v w σ ∈ localRam v w i
def decompEquiv : GlueD1Local.decompGroup L w.asIdeal ≃* LocalGal v w
theorem decompEquiv_algebraMap (σ : GlueD1Local.decompGroup L w.asIdeal) (x : L) :
    decompEquiv v w σ (algebraMap L (w.adicCompletion L) x) =
      algebraMap L (w.adicCompletion L) ((σ : Gal(L/ℚ)) x)
theorem map_ramGroup_decompEquiv (i : ℕ) :
    ((GlueConductor.ramGroup L w.asIdeal i).subgroupOf (GlueD1Local.decompGroup L w.asIdeal)).map
      (decompEquiv v w).toMonoidHom = localRam v w i
theorem ramCard_eq_card_localRam (i : ℕ) :
    GlueConductor.ramCard L w.asIdeal i = Nat.card (localRam v w i)
theorem ramGroup_ne_bot_iff (i : ℕ) :
    GlueConductor.ramGroup L w.asIdeal i ≠ ⊥ ↔ localRam v w i ≠ ⊥
theorem card_decompGroup_eq_finrank :
    Nat.card (GlueD1Local.decompGroup L w.asIdeal) =
      Module.finrank (v.adicCompletion ℚ) (w.adicCompletion L)
```

Intermediate fields. Extra context: `(K : IntermediateField ℚ L) (u : HeightOneSpectrum (𝓞 K))
[u.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver u.asIdeal]`, and `localField v w K u` is the
image of `K_u` in `L_w`. These lemmas turn the hypotheses of `GlueD1Local.D1_local` into
statements about completions:

```lean
theorem map_localSub_decompEquiv :
    (GlueD1Local.localSub L K w.asIdeal).map (decompEquiv v w).toMonoidHom =
      (localField v w K u).fixingSubgroup
theorem index_localSub_eq_finrank :
    (GlueD1Local.localSub L K w.asIdeal).index =
      Module.finrank (v.adicCompletion ℚ) (u.adicCompletion K)
theorem normalCore_localSub_eq_bot
    (hclos : IntermediateField.normalClosure (v.adicCompletion ℚ) (localField v w K u)
      (w.adicCompletion L) = ⊤) :
    (GlueD1Local.localSub L K w.asIdeal).normalCore = ⊥
```

`D1Completion.lean` (closed: T20 and T21 discharged by `ZInQ.Contrib.Different`):

```lean
theorem D1_completion
    (hclos : IntermediateField.normalClosure (v.adicCompletion ℚ) (localField v w K u)
      (w.adicCompletion L) = ⊤)
    (a : ℕ) (ha : 1 ≤ a) (hdeg : Module.finrank (v.adicCompletion ℚ) (u.adicCompletion K) ≤ a)
    (b : ℕ) (hb : localRam v w b ≠ ⊥) :
    GlueConductor.phi (fun i => Nat.card (localRam v w i)) b ≤ 4 * a ^ 2
```

The file also has `D1_completion_ramGroup` (the same with the kernel's `ramGroup`/`ramCard`),
`ramificationIdx_le_factorial_completion` and `exists_prime_liesOver`.

### (B) `ZInQ.Contrib.G15.Ladic` (`LadicBridge.lean`, `LadicD1.lean`, `LadicUpper.lean`)

Context: `{p : ℕ} [Fact p.Prime] {L : Type} [Field L] [NumberField L]
(j : L →+* PadicAlgCl p)`. Here `σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p` is the kernel's
`GQp p`. The declarations from `tauOf` on also assume `[IsGalois ℚ L]`.

```lean
def primeOf : HeightOneSpectrum (𝓞 L)                     -- {x ∈ 𝓞 L | ‖j x‖ < 1}
theorem mem_primeOf (x : 𝓞 L) : x ∈ (primeOf j).asIdeal ↔ ‖j (x : L)‖ < 1
theorem primeOf_liesOver : (primeOf j).asIdeal.LiesOver (Ideal.span {(p : ℤ)})
theorem isEquiv_nv : ((primeOf j).valuation L).IsEquiv (nv j)      -- nv j x = ‖j x‖₊
def Lj : LadicCond.Fld p := IntermediateField.adjoin ℚ_[p] (jField j : Set (PadicAlgCl p))
theorem isFinGal_Lj : LadicCond.IsFinGal (Lj j)
theorem mem_ramSet_iff (hστ : ∀ x, j (τ x) = σ (j x)) (i : ℕ) :
    σ ∈ LadicCond.ramSet (Lj j) i ↔ τ ∈ GlueConductor.ramGroup L (primeOf j).asIdeal i
theorem norm_j_apply_of_mem_stabilizer {τ : Gal(L/ℚ)}
    (hτ : τ ∈ MulAction.stabilizer Gal(L/ℚ) (primeOf j).asIdeal) (x : L) : ‖j (τ x)‖ = ‖j x‖
def tauOf (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) : Gal(L/ℚ)     -- σ|_{j L}
theorem tauOf_spec (σ) (x : L) : j (tauOf j σ x) = σ (j x)
theorem exists_lift {τ : Gal(L/ℚ)}
    (hτ : τ ∈ MulAction.stabilizer Gal(L/ℚ) (primeOf j).asIdeal) :
    ∃ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, ∀ x, j (τ x) = σ (j x)
theorem range_tauOf :
    Set.range (tauOf j) = (MulAction.stabilizer Gal(L/ℚ) (primeOf j).asIdeal : Set Gal(L/ℚ))
theorem ramCard_Lj_eq (i : ℕ) :
    LadicCond.ramCard (Lj j) i = GlueConductor.ramCard L (primeOf j).asIdeal i
def decompEquivLj :
    (Lj j ≃ₐ[ℚ_[p]] Lj j) ≃* MulAction.stabilizer Gal(L/ℚ) (primeOf j).asIdeal
theorem decompEquivLj_spec (ρ : Lj j ≃ₐ[ℚ_[p]] Lj j) (x : L) :
    j ((decompEquivLj j ρ : Gal(L/ℚ)) x) = (ρ ⟨j x, j_mem_Lj j x⟩ : PadicAlgCl p)
theorem decompEquivLj_mem_ramGroup_iff (ρ : Lj j ≃ₐ[ℚ_[p]] Lj j)
    (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (hσ : ∀ y : Lj j, σ y = ρ y) (i : ℕ) :
    (decompEquivLj j ρ : Gal(L/ℚ)) ∈ GlueConductor.ramGroup L (primeOf j).asIdeal i ↔
      σ ∈ LadicCond.ramSet (Lj j) i
theorem mem_ramSetR_iff (hστ : ∀ x, j (τ x) = σ (j x)) (t : ℝ) :
    σ ∈ LadicCond.ramSetR (Lj j) t ↔
      t ≤ -1 ∨ τ ∈ GlueConductor.ramGroup L (primeOf j).asIdeal ⌈t⌉.toNat
theorem ramCardR_Lj_eq (t : ℝ) :
    LadicCond.ramCardR (Lj j) t = Nat.card (TDifferent.filtR (decompFilt j) t)
theorem phiAt_Lj_eq (u : ℝ) : LadicCond.phiAt (Lj j) u = TDifferent.phiF (decompFilt j) u
theorem mem_upperSet_iff (hστ : ∀ x, j (τ x) = σ (j x)) (v : ℝ) :
    σ ∈ LadicCond.upperSet (Lj j) v ↔
      sInf {u : ℝ | -1 ≤ u ∧ v ≤ TDifferent.phiF (decompFilt j) u} ≤ -1 ∨
        τ ∈ GlueConductor.ramGroup L (primeOf j).asIdeal
          ⌈sInf {u : ℝ | -1 ≤ u ∧ v ≤ TDifferent.phiF (decompFilt j) u}⌉.toNat
theorem mem_upperSet_of_mem_upperAbs {σ} {v : ℝ} (hσ : σ ∈ LadicCond.upperAbs p v) :
    σ ∈ LadicCond.upperSet (Lj j) v
```

Here `decompFilt j i := (GlueConductor.ramGroup L (primeOf j).asIdeal i).subgroupOf D_P`.

The `ℚ̄`-form, which uses the embedding behind `PkgI4.decomp`. Context:
`(hjQ : ∀ σ x, jQ (PkgI4.decomp p σ x) = σ (jQ x)) (K : IntermediateField ℚ PkgI4.Qbar)
[NumberField K] [IsGalois ℚ K]`. Such a `jQ` exists by `decomp_spec`.

```lean
theorem decomp_spec (p : ℕ) [Fact p.Prime] : ∃ jQ : PkgI4.Qbar →+* PadicAlgCl p,
    ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) x, jQ (PkgI4.decomp p σ x) = σ (jQ x)
theorem tauOf_eq_restrictNormal (σ) :
    tauOf (jQ.comp (algebraMap K PkgI4.Qbar)) σ = (PkgI4.decomp p σ).restrictNormal K
theorem mem_ramSet_iff_decomp (σ) (i : ℕ) :
    σ ∈ LadicCond.ramSet (Lj (jQ.comp (algebraMap K PkgI4.Qbar))) i ↔
      (PkgI4.decomp p σ).restrictNormal K ∈
        GlueConductor.ramGroup K (primeOf (jQ.comp (algebraMap K PkgI4.Qbar))).asIdeal i
-- mem_upperSet_iff_decomp: the same for upperSet
```

D1 in `LadicCond`'s terms (`LadicD1.lean`, closed):

```lean
theorem phiF_natCast (Γ : ℕ → Subgroup G) (m : ℕ) :
    TDifferent.phiF Γ m = ∑ i ∈ Finset.Icc 1 m, (Nat.card (Γ i) : ℝ) / (Nat.card (Γ 0) : ℝ)
theorem phiAt_Lj_natCast (m : ℕ) :
    LadicCond.phiAt (Lj j) m =
      ((GlueConductor.phi (GlueConductor.ramCard L (primeOf j).asIdeal) m : ℚ) : ℝ)
theorem ramCard_Lj_zero : LadicCond.ramCard (Lj j) 0 = (primeOf j).asIdeal.ramificationIdx ℤ
theorem D1_Lj (a : ℕ) (ha : 1 ≤ a) (hea : LadicCond.ramCard (Lj j) 0 ≤ a.factorial)
    (b : ℕ) (hb : LadicCond.ramCard (Lj j) b ≠ 1) :
    LadicCond.phiAt (Lj j) b ≤ 4 * (a : ℝ) ^ 2
```

Clause (i) of G15 for one number field (`LadicUpper.lean`, closed):

```lean
theorem tauOf_eq_one_of_mem_upperSet (a : ℕ) (ha : 1 ≤ a)
    (hea : LadicCond.ramCard (Lj j) 0 ≤ a.factorial) {v : ℝ} (hv : 4 * (a : ℝ) ^ 2 < v)
    {σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} (hσ : σ ∈ LadicCond.upperSet (Lj j) v) :
    tauOf j σ = 1
theorem apply_j_eq_of_mem_upperAbs (a : ℕ) (ha : 1 ≤ a)
    (hea : LadicCond.ramCard (Lj j) 0 ≤ a.factorial) {v : ℝ} (hv : 4 * (a : ℝ) ^ 2 < v)
    {σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} (hσ : σ ∈ LadicCond.upperAbs p v) (x : L) :
    σ (j x) = j x
theorem restrictNormal_decomp_eq_one_of_mem_upperAbs {jQ : PkgI4.Qbar →+* PadicAlgCl p}
    (hjQ : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) x, jQ (PkgI4.decomp p σ x) = σ (jQ x))
    (K : IntermediateField ℚ PkgI4.Qbar) [NumberField K] [IsGalois ℚ K]
    (a : ℕ) (ha : 1 ≤ a)
    (hea : LadicCond.ramCard (Lj (jQ.comp (algebraMap K PkgI4.Qbar))) 0 ≤ a.factorial)
    {v : ℝ} (hv : 4 * (a : ℝ) ^ 2 < v)
    {σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} (hσ : σ ∈ LadicCond.upperAbs p v) :
    (PkgI4.decomp p σ).restrictNormal K = 1
```

(A) and (B) agree (`Combined.lean`; `placeBelow j := (primeOf j).under (𝓞 ℚ)`):

```lean
theorem finrank_Lj :
    Module.finrank ℚ_[p] (Lj j) = Nat.card (MulAction.stabilizer Gal(L/ℚ) (primeOf j).asIdeal)
theorem ramCard_Lj_eq_card_localRam (i : ℕ) :
    LadicCond.ramCard (Lj j) i = Nat.card (localRam (placeBelow j) (primeOf j) i)
theorem finrank_Lj_eq_finrank_adicCompletion :
    Module.finrank ℚ_[p] (Lj j) =
      Module.finrank ((placeBelow j).adicCompletion ℚ) ((primeOf j).adicCompletion L)
theorem apply_j_eq_of_mem_ramSet {i : ℕ} (h : GlueConductor.ramGroup L (primeOf j).asIdeal i = ⊥)
    {σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} (hσ : σ ∈ LadicCond.ramSet (Lj j) i) (x : L) :
    σ (j x) = j x
theorem ramGroup_one_eq_bot_iff :          -- tame criterion, from Tau Ceti
    GlueConductor.ramGroup L (primeOf j).asIdeal 1 = ⊥ ↔
      (((primeOf j).asIdeal.ramificationIdx (𝓞 ℚ) : ℕ) : 𝓞 ℚ ⧸ (placeBelow j).asIdeal) ≠ 0
```

### `#print axioms` (excerpt; the full output for all 132 declarations is in `scratch/g15-decomp/axioms-out.txt`)

```
'ZInQ.Contrib.G15.decompEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] 
'ZInQ.Contrib.G15.map_ramGroup_decompEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] 
'ZInQ.Contrib.G15.ramCard_eq_card_localRam' depends on axioms: [propext, Classical.choice, Quot.sound] 
'ZInQ.Contrib.G15.D1_completion' depends on axioms: [propext, Classical.choice, Quot.sound] 
'ZInQ.Contrib.G15.Ladic.mem_ramSet_iff' depends on axioms: [propext, Classical.choice, Quot.sound] 
'ZInQ.Contrib.G15.Ladic.ramCard_Lj_eq' depends on axioms: [propext, Classical.choice, Quot.sound] 
'ZInQ.Contrib.G15.Ladic.isFinGal_Lj' depends on axioms: [propext, Classical.choice, Quot.sound] 
'ZInQ.Contrib.G15.Ladic.mem_upperSet_iff' depends on axioms: [propext, Classical.choice, Quot.sound] 
'ZInQ.Contrib.G15.Ladic.decompEquivLj' depends on axioms: [propext, Classical.choice, Quot.sound] 
'ZInQ.Contrib.G15.Ladic.D1_Lj' depends on axioms: [propext, Classical.choice, Quot.sound] 
'ZInQ.Contrib.G15.Ladic.tauOf_eq_one_of_mem_upperSet' depends on axioms: [propext, Classical.choice, Quot.sound] 
'ZInQ.Contrib.G15.Ladic.apply_j_eq_of_mem_upperAbs' depends on axioms: [propext, Classical.choice, Quot.sound] 
'ZInQ.Contrib.G15.Ladic.restrictNormal_decomp_eq_one_of_mem_upperAbs' depends on axioms: [propext, Classical.choice, Quot.sound] 
'ZInQ.Contrib.G15.Ladic.ramCard_Lj_eq_card_localRam' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 2. How the proofs go

* (A) is a restatement of Tau Ceti's `HeightOneSpectrum.decompositionEquiv`,
  `map_ramificationGroup_decompositionHom`, `card_ramificationGroup_eq_card_lowerRamificationGroup`,
  `mem_ramificationGroup_iff_decompositionHom_mem` and `card_stabilizer_eq_finrank_adicCompletion`
  for the kernel's `decompGroup`/`ramGroup`. The match `ramGroup = Ideal.ramificationGroup` is
  definitional (`Ideal.ramificationGroup_def`). For the intermediate-field part, `σ ∈ D_P` fixes
  `K` iff `σ̂` fixes `K_u`, by continuity and density (`eq_completionAlgHom_of_continuous`). The
  rest is Galois theory in `L_w/ℚ_v`.
* (B) goes directly from `L` to `ℚ̄_p` and does not pass through `L_w`. The key step is that
  `x ↦ ‖j x‖` is equivalent to the `P`-adic valuation. It uses Mathlib's
  `exists_primeCompl_mul_eq_or_mul_eq` (every `z ∈ L` is `n/d` or `d/n` with `d ∉ P`) and
  `Valuation.isEquiv_of_val_le_one`. The uniformizer `j π` of `Lj j` and the bound
  `‖σy − y‖ ≤ ‖jπ‖^{i+1}` on all of `𝒪_{Lj}` come from the density of `j L` in `Lj j` (Tau Ceti
  `exists_mem_norm_sub_lt_of_mem_adjoin`) together with the ultrametric inequality. The `n/d`
  trick extends the congruence from `𝓞 L` to `𝓞_{L,P}`. To show that `D_P` preserves `‖j·‖`, two
  `ℝ≥0`-valuations equivalent to `v_P` that agree at `p` are equal. The lifts `D_P → G_{ℚ_p}`
  come from Tau Ceti `exists_algEquiv_apply_eq_of_norm_apply_eq`. Counting uses
  `card_image_eq_of_fibres`, because restrictions to `Lj j` have the same fibres as `tauOf`.
* `phiF_natCast`: on `(m, m+1]` the integrand is the constant `|Γ_{m+1}|/|Γ_0|`
  (`Int.ceil_eq_iff`). The proof is an induction with `integral_add_adjacent_intervals`.
* `tauOf_eq_one_of_mem_upperSet` builds the lower-index function `lowerIdx` of the `D_P`
  filtration, which is eventually trivial by the adic valuation of `s x − x`. That gives
  `TDifferent`'s hypothesis `hΓ`, so `ψ(v)` is the solution of `φ(u) = v`
  (`exists_phiF_eq`, `sInf_phiF`). Then `v = φ(ψ v) ≤ φ(⌈ψ v⌉) ≤ 4a²` by `D1_Lj`.

Tau Ceti modules used: all were already vendored by tc-port. No new module was vendored.

## 3. Using this from `G15RamG`

* The local field in `LadicCond` is `F = Lj j`, a subfield of `ℚ̄_p`. Its finite Galois property
  (`isFinGal_Lj`) feeds `upperAbs`. Every `σ ∈ G_{ℚ_p}` acts on `j L` through
  `tauOf j σ ∈ D_P`. In the `ℚ̄`-form (`jQ` from `decomp_spec`), `tauOf` is the restriction of
  `PkgI4.decomp p σ`, which is how `GaloisRep.restrictLocal` sees `σ`.
* `apply_j_eq_of_mem_upperAbs` / `restrictNormal_decomp_eq_one_of_mem_upperAbs` give clause (i)
  for any representation that factors through `Gal(K/ℚ)`, as soon as `e(P|p) = g_0 ≤ a!` with
  `4a² ≤ U₀`. Glazer's `U₀ = 4(D·G₀)²` would correspond to `a = D·G₀` (SPECULATIVE reading of N5 L826-830, not checked against the manuscript).
* `e ≤ a!` is supplied, in the decomposition-group form, by `GlueD1Local` (core and index
  hypotheses). The completion form is `ramificationIdx_le_factorial_completion`, and
  `ramCard_Lj_zero` converts it.

## 4. What is not done

* Krasner's choice of the number field `K` with a prescribed completion. This was not part of
  the task, and it is not in Tau Ceti.
* Clause (ii) (wild inertia) and the passage from the `ℓ`-adic `r` to a finite-level number field
  are G15RamG's own content, not transport.
* The relation between `LadicCond.wildSet` and `ramSet (Lj j) 1` was not proved. It is a
  local-field fact (Serre, *Corps locaux* IV §2, UNVERIFIED locator), not a transport.

## 5. Files

`ZInQKernel/Contrib/G15/{Transport,D1Completion,LadicBridge,LadicD1,LadicUpper,Combined}.lean`.
`lake build ZInQKernel.Contrib.G15.LadicUpper ZInQKernel.Contrib.G15.Combined
ZInQKernel.Contrib.G15.D1Completion` succeeds (VERIFIED). The results log is
`scratch/g15-decomp/log.md`, and the axiom check is `scratch/g15-decomp/Axioms.lean` with its
output in `axioms-out.txt` (132 declarations, all `[propext, Classical.choice, Quot.sound]`).

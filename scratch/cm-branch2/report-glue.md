## 2. The three glue Props of the CM branch

| glue (cm-branch) | result here | Lean |
|---|---|---|
| `HeightAdditivityUpper` (L620-621, "additivity") | **proved** from the chain's textbook field `t35` (`UniformizationExists`) and proved tree results | `CMBranch.heightAdditivityUpper_of_t35` (`CMBranch/HeightAdd.lean`) |
| `ReducedCMPeriod` (L598-599) | **reduced** to one textbook leaf, `CoxProperLattice`, plus the chain's textbook fields `t35`, `homLatticeCorr`, `t11b`; every other step proved | `CMBranch.reducedCMPeriod_of_leaves` (`CMBranch/PeriodLattice.lean`, `CMBranch/ReducedPeriod.lean`) |
| `CMFibreSplit` (A8 at a CM fibre + matrix units, L520-562, L582-586) | **open** (GLUE); decomposition in §2.3 | unchanged (`CMBranch.lean`) |

All VERIFIED: compiled with `lake env lean` and `lake build`; `#print axioms` = `propext, Classical.choice, Quot.sound`
(`scratch/cm-branch2/Axioms.lean`, output `axioms-out.txt`).

### 2.1 `HeightAdditivityUpper`

`h_F(P) ≤ h_F(A) + h_F(Z)` for `P ≅ A × Z` follows from the definition of `stableFaltingsHeight` as an infimum over
metrized models (`ZInQ.DefFaltings.stableFaltingsHeight`), with no Néron model and no semistable reduction:

1. for `ε > 0` pick metrized models `M₁` of `A` over `E₁` and `M₂` of `Z` over `E₂` with `h(Mᵢ) <` the height `+ ε/2`
   (`iInf_lt_iff` three times);
2. base-change both to a compositum `L'` (`H5Neron.compositum`), keeping the height: `G0StableBC.groupModelBaseChangeExists`,
   `G0StableBC.MetrizationBaseChange` (proved in the tree from `HodgeLineBaseChange`: `metrizationBaseChange_of_hodgeLine`
   with `hodgeLineBaseChange_of_glue4` and the four proved pieces the chain already uses), `modelHeight_eq_of_isHodgeBaseChange`;
3. the product group model over `L'` (`H5Neron.productGroupModelExists`, proved) carries a metrization of height
   `h(M₁) + h(M₂)`: `G0HeightAdd.ProductMetrization` (P2a). P2a is task metrization's reduction
   (`scratch/metrization/part_prodgeo.lean`, `part_prodlat.lean`, `part_produnif.lean`, `part_prodsplit.lean`, copied
   verbatim into `HDec.ZInQ.Metrization.CMB2`): `ProductMetrizationGeo` from `JacDetDescends` (proved),
   `ProductUniformization` (from `productUniformizationAnalytic_of` + `Metrization2.productLocalStructure`, proved),
   `ProductLatticeFacts` (proved here, copied) and `ProductHodgeCompat` (from `ProductHodgeLattice` =
   `UnifDims.productHodgeLattice_of_cotangent productCotangent tangentDimAtOrigin_proved3 t35`, and `productJacobian`);
4. so `p ≤ h(MP) < a + z + ε` (`stableFaltingsHeight_le`), hence `p ≤ a + z`.

The only non-proved input is T35, already a field of the chain's textbook bundle (`OpenTextbookLeaves4HFPZ.t35`;
`OpenTextbookLeaves18` at the top is empty, T35 being discharged above by `AvSplit.Final.h38`). New leaves: none.

### 2.2 `ReducedCMPeriod`

The manuscript's sentence "For a reduced CM period `τ = x + iy` we have `√3/2 ≤ y ≤ √|Δ|/2`" (L598-599) has no citation.
Its Lean form is cm-branch's `ReducedCMPeriod`: every `E/K` with `End(E_{K̄}) ≅ R` has, at every `σ`, a period `τ` with
`√3/2 ≤ Im τ ≤ √|Δ_R|/2`. It is now proved from:

* **`CMPeriodLattice`** (proved, `cmPeriodLattice_of`): `E(ℂ)_σ` has an analytic uniformization with full lattice `Λ`
  whose multiplier ring `{α ∈ ℂ | αΛ ⊆ Λ}` (`latticeMultipliers`) is isomorphic to `R`. Proof: T35 on
  `E_ℂ := (E_{K̄})_ℂ` (`σ̄ : K̄ → ℂ` extending `σ`); transport to `E(ℂ)_σ` by
  `HSyn.G0Split.FibreQM.CPtsT.cPts_of_isPullback` (proved; the two base-change squares pasted, `σ̄ ∘ (K → K̄) = σ`), as in
  the tree's `unifTransport_of`; `End(E_ℂ) ≅ multipliers` from `HomUnify.HomLatticeCorr` (clause 1: every endomorphism
  lifts to a `ℂ`-linear map of `ℂ¹`, i.e. a multiplication, unique because `Λ` is discrete; clause 2: every multiplier is
  induced by a unique endomorphism, which gives injectivity and surjectivity), a ring isomorphism by uniqueness
  (`end_ringEquiv_mult`); `End(E_{K̄}) ≅ End(E_ℂ)` from T11b rigidity (`end_ringEquiv_baseChange`; base change is a ring
  hom because `Over.pullback` is monoidal: `Functor.map_mul`, `Functor.map.instIsMonHom`).
* **`exists_reduced_basis`** (proved, pure Mathlib): every full lattice of `ℂ¹` is `c(ℤ + τℤ)` with `τ` in Mathlib's closed
  fundamental domain `ModularGroup.fd` (a ℤ-basis from `ZLattice.rank`, orientation, then `ModularGroup.exists_smul_mem_fd`
  and the `SL₂(ℤ)` change of basis); hence `Im τ ≥ √3/2` (`ModularGroup.three_le_four_mul_im_sq_of_mem_fd`).
* **`CoxProperLattice`** (new textbook leaf, consequence form): if `c(ℤ + τℤ)`, `Im τ > 0`, has multiplier ring `≅ R`,
  then `τ` is a root of a primitive form `(a, b, c')`, `a > 0`, with `b² − 4ac' = Δ_R = f²d_k`.
* **`im_le_of_quadratic`** (proved): such a root has `Im τ = √(4ac' − b²)/(2a) ≤ √|b² − 4ac'|/2`.

So `ReducedCMPeriod` costs one new leaf (`CoxProperLattice`) and no glue. The proof is the on-the-spot sketch cm-branch
gave (lattice homothetic to a proper `R`-ideal, reduced basis, primitive form), now a Lean proof except for Cox's
lemma.

### 2.3 `CMFibreSplit` (open)

Statement unchanged (cm-branch). It packs two manuscript steps:

1. **A8 at a CM fibre** (L520-562): a model `A/L` of the fibre with `[L:ℚ] ≤ D` over which every geometric endomorphism
   (and every ordered conjugacy homomorphism) is defined: `W₀ = Res_{K/ℚ} A`, kernel field `E` of the Galois action on the
   endomorphism lattice of rank `r ≤ 16F₀²`, `L = EK`, `[L:ℚ] ≤ F₀3^{r²} ≤ D`. The chain formalized A8 as
   `G0ModField.KernelFieldExists`, but its proof goes through `ConjMapsNoCM`, i.e. through NoCM; cm-branch localized it
   to fibres without CM (`KernelFieldExistsNC`). A8 itself does not depend on the case split; what is missing is a proof of
   the conjugacy maps (`ConjMaps`) without NoCM.
2. **Matrix units** (L563-586): `End⁰(A_ℚ̄) = M₂(k)` at a CM fibre (Milne, Part I Thms 2.8-2.9 for algebraicity of
   Hodge endomorphisms, cited at L563, plus the centralizer computation L572-577), the idempotent `e₁₁`, `E = image of e₁₁`
   (an abelian subvariety; the tree has image recipes, `Hom.image` + flat base change), the `L`-isogeny
   `E × E → A`, `(x, y) ↦ x + e₂₁y`, and `End(E_{L̄})` an order of `k`.

Neither piece is closer to a proof than in cm-branch; splitting the Prop would only add GLUE, so it is kept whole.

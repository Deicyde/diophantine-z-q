# cm-branch2: the CM branch's glue, the R5ptProps prune, and the X₆ rows

Task cm-branch2 (2026-11-17). Base: `origin/wip/cm-branch` 42d874ac with `origin/main` b1615c9b merged (top
`HDec.HSyn.sixContactMin_of_open72`, TailZ79). Results log: `scratch/cm-branch2/log.md`. Marks: VERIFIED (compiled, or
read in the tree / the manuscript diophantine_zq.tex), STANDARD (published, exact reference), UNVERIFIED (theorem
numbers from memory; this host has no network), SPECULATIVE.

## 1. Result

**The CM-branch fold reaches net zero in the GLUE column, and González–Rotger leaves the route.** The fold's next
generation is written and compiled (§7): `sixContactMin_of_open73_cm (r : OpenResearchLeaves54CM) t l : SixContactMin`,
where `OpenResearchLeaves54CM` is the current research bundle without `gonzalezRotgerThm512X6RCF` and with the 5 CM-branch
inputs. A closure scan of it (`scratch/cm-branch2/gruse73-out.txt`) finds neither `GR512Bridge.GonzalezRotgerThm512X6RCF`
nor `GRDict.GonzalezRotgerThm512X6` nor `R5ptProps`. VERIFIED, compiled with only `propext`, `Classical.choice`,
`Quot.sound`. The same route with the CM inputs as a separate argument:

```lean
theorem HDec.HSyn.sixContactMin_of_open72_cmbranch2 (r : OpenResearchLeaves53) (t : OpenTextbookLeaves18)
    (l : OpenAddedLeaves27) (c : CMBranch.CMInputs3) : ZInQ.SixContactMin
```

(`ZInQKernel/Contrib/OneProof/CMBranch2.lean`, via `sixContactMin_of_open72_cm2_r5` of `CMBranch/R5Prune.lean`): the current
top theorem with one extra hypothesis `c : CMBranch.CMInputs3`, the chain's NoCM base replaced by the manuscript's CM branch
(cm-branch), and

1. **`HeightAdditivityUpper` proved** (glue −1): from the chain's textbook field `t35` and proved tree results (§2.1);
2. **`ReducedCMPeriod` proved** (glue −1): `CMPeriodLattice` (the period lattice of a CM curve has multiplier ring `≅ R`)
   is proved from the textbook fields `t35`, `homLatticeCorr`, `t11b`. Also proved: the reduced basis, the bound
   `√3/2 ≤ Im τ ≤ √|Δ|/2`, and Cox's lemma on proper ideals, `CoxProperLattice`, including the discriminant formula
   `disc ℤ[θ] = [𝓞_k : ℤ[θ]]² d_k` (§2.2). No new leaf;
3. **`R5ptProps` pruned** (§3): the whole route, bundles from `OpenResearchLeaves34EBCF` down included, re-run with the conjunct
   replaced by `True` (`CMBranch/R5Prune.lean`, generated, 6282 lines). It compiles, so no consumer reads `R5ptProps`. The
   field `gonzalezRotgerX6Ab` is filled without González–Rotger (from `x6CoarseModuli` and `shimuraMainThmIDeligneY3AbU`).
   A closure scan of the new top (`scratch/cm-branch2/gruse-out.txt`) shows `R5ptProps`, `GRDict.r5ptProps_of_thm512` and
   `GRX6AbPrint.gonzalezRotgerX6Ab_of_print` gone. The projection `OpenResearchLeaves35EBCF.gonzalezRotgerThm512X6` of the last
   bundle carrying González–Rotger is never read. **The top field `gonzalezRotgerThm512X6RCF` is now only carried by the
   bundle conversions (53 → 36EBCF → 35EBCF), so PruneScan can drop it at the fold.**

**Count.** `CMInputs3` has 5 fields: the glue `CMFibreSplit` and cm-branch's four leaves `FowlerProp27`, `CMHeight62`,
`CMjDegree`, `CMPotentialGood`. The fold adds 1 GLUE (`CMFibreSplit`) and removes 1 GLUE (`gonzalezRotgerThm512X6RCF`,
consequence GLUE/GLUE in kinds.tsv), so the GLUE column is **net 0**. It also adds the 4 leaves: three consequence form
(`CMHeight62`, `CMjDegree`, `CMPotentialGood`) and one in printed form (`FowlerProp27`). New leaves enter "pending
review" and count as GLUE until a reviewer rates them, so under that counting the fold is **+4** until the leaves are
reviewed. For comparison, cm-branch's fold was +3 GLUE +4 leaves with nothing removed.

**X₆ rows.** `x6CoarseModuliIdeal` and `elkiesX6StarEveryIdeal` stay. The clause scan
(`scratch/cm-branch2/clauseuse.txt`) shows that `X6Props`, `R2X6Props`, `CMExists`, `X6Surj` and `R1recProps` are all
read on the new route, by `exists_fibre_object`, `residue_unramified_over_branch`, `Pin.cm_objects_of_R1R2fp` and the
period-map family. §5 gives the concrete plan for re-sourcing them to `Y₃ → P¹_j` (manuscript L421-441), with what it
needs from y3-route-a and beyond. The re-source is not a GLUE gain by itself.

**Files** (all new; none of the base's files was edited, except the generated copies of cm-branch's own `Top.lean` chain):

| file | content |
|---|---|
| `Contrib/OneProof/CMBranch/HeightAdd.lean` | `heightAdditivityUpper_of_t35`; copies of metrization's `ProductMetrizationGeo` reduction (`HDec.ZInQ.Metrization.CMB2`) |
| `Contrib/OneProof/CMBranch/ReducedPeriod.lean` | `latticeMultipliers`, `CMPeriodLattice`, `CoxProperLattice`, `im_le_of_quadratic`, `exists_reduced_basis`, `reducedCMPeriod_of` |
| `Contrib/OneProof/CMBranch/CoxProof.lean` | `CoxCore.discr_pair`, `CoxCore.discr_order`, `mult_iff_dvd`, `coxProperLattice_proof` |
| `Contrib/OneProof/CMBranch/PeriodLattice.lean` | `end_ringEquiv_mult`, `end_ringEquiv_baseChange`, `cmPeriodLattice_of`, `reducedCMPeriod_of_leaves` |
| `Contrib/OneProof/CMBranch/Top2.lean` | `CMInputs2`, the chain open72 → open4 with `c` threaded (generated, `gen/mk_top2.py`) |
| `Contrib/OneProof/CMBranch/R5Prune1..3.lean`, `R5Prune.lean` | the weak-row bypass (generated, `gen/gen_r5.py`; four files under 141 KB), top `sixContactMin_of_open72_cm2_r5` |
| `Contrib/OneProof/CMBranch/Open73.lean` | the next generation `OpenResearchLeaves54CM` and `sixContactMin_of_open73_cm` (generated, `gen/gen_open73.py`) |
| `Contrib/OneProof/CMBranch2.lean` | `CMInputs3` and the deliverable `sixContactMin_of_open72_cmbranch2` |

## 2. The three glue Props of the CM branch

| glue (cm-branch) | result here | Lean |
|---|---|---|
| `HeightAdditivityUpper` (L620-621, "additivity") | **proved** from the chain's textbook field `t35` (`UniformizationExists`) and proved tree results | `CMBranch.heightAdditivityUpper_of_t35` (`CMBranch/HeightAdd.lean`) |
| `ReducedCMPeriod` (L598-599) | **proved** from the chain's textbook fields `t35`, `homLatticeCorr`, `t11b` (Cox's lemma proved too) | `CMBranch.reducedCMPeriod_of_leaves … coxProperLattice_proof` (`PeriodLattice.lean`, `ReducedPeriod.lean`, `CoxProof.lean`) |
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
* **`CoxProperLattice`** (Cox, *Primes of the form x²+ny²*, Lemma 7.5 with Lemma 7.2; **proved**,
  `coxProperLattice_proof`, `CMBranch/CoxProof.lean`): if `c(ℤ + τℤ)`, `Im τ > 0`, has multiplier ring `≅ R`, then `τ` is
  a root of a primitive form `(a, b, c')`, `a > 0`, with `b² − 4ac' = Δ_R = f²d_k`. Proof: a multiplier outside `ℤ`
  (the image of `[𝓞_k:R]·y`, `y ∈ 𝓞_k ∖ ℚ`) gives the quadratic relation, normalized to a primitive form
  (`exists_prim`); the multiplier ring is `ℤ + ℤaτ` (`mult_iff_dvd`, Cox 7.5's elementary half); so `R = ℤ + ℤθ` with
  `θ ↦ aτ`, `θ² + bθ + ac' = 0`; finally `b² − 4ac' = [𝓞_k : R]²·d_k` (`CoxCore.discr_order`: trace discriminant of
  `(1, θ)` from the left-multiplication matrix, `AddSubgroup.relIndex_eq_abs_det` against Mathlib's integral basis,
  `Algebra.discr_of_matrix_vecMul`, `NumberField.coe_discr`).
* **`im_le_of_quadratic`** (proved): such a root has `Im τ = √(4ac' − b²)/(2a) ≤ √|b² − 4ac'|/2`.

So `ReducedCMPeriod` costs nothing: no leaf and no glue beyond the chain's textbook fields. The proof is the on-the-spot
sketch cm-branch gave (lattice homothetic to a proper `R`-ideal, reduced basis, primitive form), now entirely in Lean.

### 2.3 `CMFibreSplit` (open)

Statement unchanged (cm-branch). It packs two manuscript steps:

1. **A8 at a CM fibre** (L520-562): a model `A/L` of the fibre with `[L:ℚ] ≤ D` over which every geometric endomorphism
   (and every ordered conjugacy homomorphism) is defined: `W₀ = Res_{K/ℚ} A`, kernel field `E` of the Galois action on the
   endomorphism lattice of rank `r ≤ 16F₀²`, `L = EK`, `[L:ℚ] ≤ F₀3^{r²} ≤ D`. The chain formalized A8 as
   `G0ModField.KernelFieldExists`, but its proof goes through `ConjMapsNoCM`, i.e. through NoCM; cm-branch localized it
   to fibres without CM (`KernelFieldExistsNC`). A8 itself does not depend on the case split; what is missing is a proof of
   the conjugacy maps without NoCM. VERIFIED by reading: `G0ModField.KernelField.ConjMapsNoCM` (TailC L6108) takes
   `∀ φ ∈ com P.q, φ ∈ ℤ` at the point as a hypothesis. With trivial commutant the conjugacy isomorphisms `A^σ ≅ A` are
   unique up to sign, so the maps `m σ` on `L`-points form a descent datum. At a CM fibre the commutant contains an
   order of `k`, the isomorphisms are unique only up to its units, and the cocycle condition needs a choice. The
   manuscript does not take this route: it reads the field of definition off the Galois action on the endomorphism
   lattice of `W₀ = Res_{K/ℚ} A` (kernel field `E`, L546-555), and that argument needs no rigidity. So A8 at a CM fibre
   needs A8 re-formalized along the manuscript's Weil-restriction argument. The chain's `ConjMaps` descent cannot be
   reused there.
2. **Matrix units** (L563-586): `End⁰(A_ℚ̄) = M₂(k)` at a CM fibre (Milne, Part I Thms 2.8-2.9 for algebraicity of
   Hodge endomorphisms, cited at L563, plus the centralizer computation L572-577), the idempotent `e₁₁`, `E = image of e₁₁`
   (an abelian subvariety; the tree has image recipes, `Hom.image` + flat base change), the `L`-isogeny
   `E × E → A`, `(x, y) ↦ x + e₂₁y`, and `End(E_{L̄})` an order of `k`.

Neither piece is closer to a proof than in cm-branch; splitting the Prop would only add GLUE, so it is kept whole.

## 3. The R5ptProps prune (done: weak-row bypass, compiled)

**Result (VERIFIED, compiled, standard axioms).** `CMBranch/R5Prune.lean` (6282 lines, generated by
`scratch/cm-branch2/gen/gen_r5.py` from the dirty set `scratch/cm-branch2/dirty.tsv`) re-runs the whole CM-branch route
with the moduli row in its weak form: every occurrence of `LeafQM.AV.R5ptProps X Ψ` in the copied declarations is
replaced by `True`. It compiles with 0 errors and no `sorry`, so **no consumer on the route reads `R5ptProps`**: if one did,
its copy would fail to typecheck (it would have to use a proof of `True` as González–Rotger's Thm 5.12). The new top is

```lean
theorem HDec.HSyn.sixContactMin_of_open72_cm2_r5 (r : OpenResearchLeaves53) (t : OpenTextbookLeaves18)
    (l : OpenAddedLeaves27) (c : CMBranch.CMInputs2) : ZInQ.SixContactMin
```

(`CMInputs2` = `CMInputs3` plus `CoxProperLattice`; `sixContactMin_of_open72_cmbranch2` in `ZInQKernel/Contrib/OneProof/CMBranch2.lean`
supplies that field by `coxProperLattice_proof`).

**How.** The dirty set is every `ZInQKernel` constant in the closure of the CM-branch top whose type or value mentions
`R5ptProps` or a dirty constant, with bundle structures marked dirty with their constructors (`scratch/cm-branch2/Dirty.lean`;
955 constants, 192 copied after dropping generated ones: projections, `mk`, `rec`, …). The copies are verbatim (namespace and
`open`/`variable` context reconstructed by `gen/leanctx.py`), with every reference to a dirty constant renamed
`_root_.<full name>_r5` (members of a dirty structure `S.x` become `S_r5.x`, so dot notation still works). The dirty set
contains the research bundles `OpenResearchLeaves34EBCF` down to `OpenResearchLeaves2EB` and `ResearchLeaves3EB`
(fields `gonzalezRotgerX6Ab`, `r1r2`, `r1b`), the added bundles `OpenAddedLeaves9PZ`–`4PZ` (field `x6ConicModel`), the
rows `LeafAdopt.R1R2fpRepW`, `LeafQM.AV.R1R2fp`, `X6Kummer.X6ConicModel`, `FS5NoCM.R1R2fpFullProps`,
`QMSplit.Moduli.GonzalezRotgerX6(Ab)`, `ResidueOfX6`, the 30 chain theorems of `Top2.lean`, and the deep consumers
(`exists_fibre_object`, `residue_unramified_over_branch`, `Pin.cm_objects_of_R1R2fp`, the `FibreQM.fibreQMPeriod_*`
family, `PropTSRed.propTSAll_*`, `TSHecke.*`, `HeckeRestAll.*`, `SGRDirect.*`, `GapST.*`, `PeriodMapH.LeafQCheck.*`, …).

**Hand patches (all at producers of the conjunct, listed in the generator).**

| where | change | why |
|---|---|---|
| `openResearchLeaves34_of_OpenResearchLeaves35_eb_cf_r5` (TailZ74 L299) | `gonzalezRotgerX6Ab := QMSplit.Moduli.gonzalezRotgerX6Ab_r5_of_coarse n.shimuraMainThmIDeligneY3AbU n.x6CoarseModuli` | the only reader of `gonzalezRotgerThm512X6` (through `GRX6AbPrint.gonzalezRotgerX6Ab_of_print`); the weak field is the `X₆` witness only, from `GRX6AbPrint.x6ModuliWitness_of_coarse` (proved, no Thm 5.12) |
| `residueOfX6_of_r5fp_r5`, `r1r2fpRep_of_splitW_r5`, `…split5W_r5`, `…split6W_r5`, `…printedW_r5` | drop the `R5fp` argument; `ResidueOfX6_r5` (`∀ …, True`) proved by `trivial` | the row's `R5ptProps` conjunct was built from `R5fp`, itself from González–Rotger through `ShimuraSplit.r5fp_of_point` |
| bundle field `r5 : LeafQM.AV.R5fp` in `OpenResearchLeaves8EB_r5` … `2EB_r5`, `ResearchLeaves3EB_r5` | type `True`; `r5 := trivial` in `researchLeaves8_of_open9_hf_eb_r5` | `r5` was `r5fp_of_rep r.r1r2` (reads `R5ptProps`); no theorem of the route reads `r5` (the copies compile) |
| not copied | `HSyn.r5fp_of_rep`, `ShimuraSplit.r5fp_of_point`, `…point_of_r5fp`, `GRDict.r5ptProps_of_thm512`, `GRDict.gonzalezRotgerX6Ab_of_witness`, `GRX6AbPrint.gonzalezRotgerX6Ab_of_coarse`, `…_of_print` | the producers of `R5ptProps` from González–Rotger |

So the consumers that "genuinely need `R5ptProps`" are **none** on the CM-branch route; the only readers were the
NoCM proof (FS5, removed by cm-branch) and the producers above. Generic fixes the generator needed (for a future
fold): comment-aware context extraction; `open … in` lines are not context; a global `_root_.X` in the full import
makes `X` ambiguous in `SGRDirectNV`, so `Polynomial.X` is written out there; local names equal to a dirty member's last
component (`h5`) must not be renamed.

### 3.1 Closure scans (VERIFIED)

* `scratch/cm-branch2/GRUse.lean` on `sixContactMin_of_open72_cm2_r5` (`gruse-out.txt`, 130539 constants): `R5ptProps`,
  `GRDict.r5ptProps_of_thm512`, `GRX6AbPrint.gonzalezRotgerX6Ab_of_print`, `FS5NoCM.R1R2fpFullProps` absent;
  `OpenResearchLeaves35EBCF.gonzalezRotgerThm512X6` (the last carrier's projection) absent; the top projection
  `OpenResearchLeaves53.gonzalezRotgerThm512X6RCF` present only through the conversions 53 → 36EBCF → 35EBCF, which
  carry it.
* The same scan on `sixContactMin_of_open73_cm` (§7; `gruse73-out.txt`, 130280 constants): no González–Rotger constant at
  all (`GR512Bridge.GonzalezRotgerThm512X6RCF`, `GR512Bridge.gonzalezRotgerThm512X6_of_rcf`,
  `GRDict.GonzalezRotgerThm512X6`, `R5ptProps` absent).
* `scratch/cm-branch2/FieldScan.lean` (`fieldscan-out.txt`): every field of `OpenResearchLeaves54CM` (31) and
  `OpenAddedLeaves27` (2) occurs in the closure of `sixContactMin_of_open73_cm`; no other field is left syntactically unread.


## 4. The new statements and their rating

| statement | kind | Lean | source / locator | printed form? |
|---|---|---|---|---|
| `FowlerProp27` | leaf (cm-branch) | `CMBranch.FowlerProp27` | Fowler, Math. Proc. Cambridge Philos. Soc. 180 (2026) 607-641, Prop. 2.7 (manuscript `\cite[Proposition 2.7]{fowler}`, L588); AUDIT-READ (upstream audit) | yes, through `h(Δ) = #Pic(R)`, `Δ = f²d_k` |
| `CMHeight62` | leaf (cm-branch) | `CMBranch.CMHeight62` | Barquero-Sanchez et al., Res. Number Theory 3 (2017) art. 13, Eq. (6.2) (manuscript `\cite[Eq. (6.2)]{cmheight}`, L603); AUDIT-READ | consequence (good reduction, `≤` half; the stable height over `L₁` bounds the height of `E`, which is L597-598's "does not change", see §6) |
| `CMjDegree` | leaf (cm-branch), **ELLIOT-literature** | `CMBranch.CMjDegree` | classical: `[ℚ(j(E)):ℚ] = h(R)` (Cox Thm 11.1, UNVERIFIED); manuscript L586-587 states it without citation | consequence (`#Pic(R) ≤ [L:ℚ]`) |
| `CMPotentialGood` | leaf (cm-branch), **ELLIOT-literature** | `CMBranch.CMPotentialGood` | classical: CM ⇒ potentially good reduction (Serre–Tate 1968, UNVERIFIED); manuscript L596-597 without citation | consequence |
| `CoxProperLattice` | **proved** (was introduced as a textbook leaf, then proved) | `CMBranch.coxProperLattice_proof` | Cox, *Primes of the form x²+ny²*, Lemma 7.5, Lemma 7.2 (numbers UNVERIFIED) | — (a theorem) |
| `CMFibreSplit` | GLUE (cm-branch, open) | `CMBranch.CMFibreSplit` | manuscript A8 L520-562 + L582-586 | — |
| `CMPeriodLattice` | glue, **proved** | `CMBranch.cmPeriodLattice_of` | — | — |
| `HeightAdditivityUpper` | glue, **proved** | `CMBranch.heightAdditivityUpper_of_t35` | — | — |
| `ReducedCMPeriod` | glue, **proved** (with `coxProperLattice_proof`) | `CMBranch.reducedCMPeriod_of_leaves` | — | — |

Proposed rows for `docs/research/locators.md` (not edited here, since that file belongs to the locator audit):
`CMjDegree` and `CMPotentialGood` (classical, uncited in the manuscript; locators UNVERIFIED, no network on this host).

## 5. Re-sourcing R2 to `Y₃ → P¹_j` (scope only; not done)

**What the two `X₆` fields give today** (VERIFIED by reading TailZ70/TailZ75 docstrings, TailZ21, GRX6AbPrint.lean):

| field | statement (short) | feeds |
|---|---|---|
| `x6CoarseModuliIdeal` | `X₆ = X₀(6,1)` over `ℚ` is a coarse moduli scheme of QM pairs: proper smooth curve, `Ψ : X₆(ℚ̄) ≃ {QM pairs}/≅` Galois-natural, Atkin–Lehner `w_m` in ideal-quotient form, classifying maps of level-3 families over proper smooth curves | the `X₆` witness `(X, Ψ, fY)` of the moduli row (`X6Props`), via `GRX6AbPrint.x6ModuliWitness_of_coarse` with `shimuraMainThmIDeligneY3AbU` |
| `elkiesX6StarEveryIdeal` | Elkies §3: on every witness, some `t : X₆ → P¹` with `ℚ(X₆)^W = ℚ(t)`, CM values `t = 0, 1, ∞` at discriminants `−24, −4, −3`, charts `s² = −t`, `r² = 3(t − 1)` | `π₆` and `R2X6PropsIff` (fibres of `π₆` = `W`-orbits, CM values), `X6Surj`, through `elkiesX6StarPrinted` / `babaGranathRationalAb` |

The consumers read the row through `LeafQM.AV.R1R2fp_Y`: `(Y, Φ, π := π₆ ∘ fY)` with `R1fpProps`, `R1heckeProps`,
`R2fpProps` (fibres of `π` on `Y₃(ℚ̄)` = `Aut 𝒪`-twist classes, values `0, ∞, −16/27` at the CM points `−4, −3, −24`),
plus the conjuncts listed by the clause scan (§5.1).

### 5.1 Which conjuncts of the row are read (VERIFIED, `scratch/cm-branch2/ClauseUse.lean`, `clauseuse.txt`)

On the weak-row top, binders whose type is the clause and whose body uses them:

| clause | readers (constants) | main readers |
|---|---|---|
| `R5ptProps` | 0 | — (pruned) |
| `R5fp` (the bundle field `r5`) | 0 | — |
| `X6ConicModel` (the added field `x6ConicModel`) | 0 | — (NoCM only) |
| `R1fpProps` | 88 | everywhere (`Y₃` itself) |
| `R2fpProps` | 50 | `TSHecke.*`, `SGRDirect.*`, period maps, `KernelField.*`, `CMBranch.cmBranchOut_of` |
| `X6Props` | 41 | `ElkiesPrint.*`, `X6ALIdeal.*`, `x6Props_transport`, `gonzalezRotgerX6Ab_r5_of_coarse` |
| `R1heckeProps` | 14 | `TSHecke.*`, `PropTSGlue.*`, `PeriodGlue.twistOrbitFinite_of` |
| `R2X6Props` | 9 | `R2fpProps_of_X6`, `exists_fibre_object_r5`, `residue_unramified_over_branch_r5`, `cm_of_val` |
| `R2X6PropsIff` | 7 | `babaGranathX6_of`, `hauptmodulOfX6_of`, `cmExists_of_iff` |
| `X6Surj` | 6 | `exists_fibre_object_r5`, `Pin.cm_objects_of_R1R2fp_r5`, `GapST.cm_pointW_r5`, `pairsLift_of_rep_r5` |
| `CMExists` | 5 | `residue_unramified_over_branch_r5`, `Pin.cm_objects_of_R1R2fp_r5`, `cm_of_val`, `hauptmodulUniqueX6S_of` |
| `R1recProps` | 4 | `residue_unramified_over_branch_r5`, `ShimuraSplit.r1rec_of_point` |

So a `Y₃`-only re-source must supply, on `Y₃`: `R2fpProps` (fibre and CM-value clauses for `π : Y₃ → P¹_j`),
surjectivity of `π` on `ℚ̄`-points, the existence of the three CM points, and reciprocity at them. The readers that are
stated on `X₆` data (`exists_fibre_object`, `residue_unramified_over_branch`, `cm_objects_of_R1R2fp`, `cm_of_val`) would
need `Y₃` forms, i.e. a second weak-row bypass like §3 with the row replaced by its `Y₃` form.

**The manuscript's route** (L421-441): the normalizer `N` of `𝒪̂` acts on the level-3 curve `Y₃` (all determinant
components) through `N/(𝔸_f^× K₃)`, the quotient is `P¹_j` with branch values `0, ∞, −16/27` and indices `4, 6, 2`
(`[babagranath, linyang]`, L420-422), and `deg(Y₃ → P¹_j) ≤ 4·|(𝒪/3𝒪)^×| ≤ 324`; the integral model comes from
Buzzard Thm 2.1 / Cor. 2.3 applied to `V₁(5)` over `ℤ[1/30]` (L444-470). `X₆` never appears.

**What a re-source needs.**

1. *From y3-route-a* (Buzzard Thm 2.1/Cor 2.3 as the manuscript cites, L444): the fine moduli scheme `Y₃` over `ℚ`
   (and `ℤ[1/30]`) with its universal QM abelian scheme and full level-3 structure, i.e. the content of the current
   research field `y3FineModuliAbP` (`R1fpPropsAbP`), in the printed form. This replaces the `Y₃` half of the witness;
   it does not give `π`.
2. *Beyond y3-route-a*:
   - (a) **the normalizer action on `Y₃`** by `ℚ`-automorphisms inducing the twists `α ∈ Aut 𝒪` and the right
     multiplications `u ∈ 𝒪^×` on points: this is `R1heckeProps`, already in the row and proved in the tree
     (`heckeOfFine_proof`, from the fine moduli property);
   - (b) **the quotient `Y₃/G` by a finite group of automorphisms** as a proper smooth curve with `(Y₃/G)(ℚ̄) =
     Y₃(ℚ̄)/G` (textbook leaf: Mumford, *Abelian varieties* §7 Thm 1, or SGA 1 Exp. V Prop. 1.8 with normality ⇒
     smoothness of a curve in characteristic 0; not in Mathlib; locators UNVERIFIED);
   - (c) **the identification `Y₃/N ≅ P¹_j`** with the stated branch values: the manuscript cites Baba–Granath and
     Lin–Yang (L420-422). Baba–Granath state it for `X₆/W` (the tree's `babaGranathRationalAb`, Baba–Granath §3);
     to avoid `X₆` one needs either `Y₃/N = X₆/W` (which is the forgetful map, i.e. `X₆` again) or Lin–Yang's form:
     the polarized moduli point of the fibre as a function of `j`, `[J₂ : J₄ : J₆ : J₁₀] = [12(j+1) : 6(j²+j+1) :
     4(j³−2j²+1) : j³]` (L544-547; the tree has `LeafPush2.LinYangTuple`, `linYang_j_eq`), which defines
     `π : Y₃ → P¹` directly from the Igusa invariants of the universal family;
   - (d) **the fibre clause of `R2fpProps`** on `Y₃` (same `π`-value ⇔ `Aut 𝒪`-twist-equivalent QM pairs): from (b)
     and (c) with Baba–Granath's polarized equivalence relation `V_ℤ = V/W` (L534-537) — or, on the Lin–Yang route,
     Igusa's theorem that `[J₂:…:J₁₀]` determines the principally polarized surface plus "isomorphic ppav ⇒ twist
     equivalent" (Baba–Granath);
   - (e) **surjectivity of `π` on `ℚ̄`-points** (the first half of `X6Surj`, used to choose a fibre over `J(u)`, A4):
     immediate from (b) (a non-constant map of proper curves);
   - (f) **the CM existence clause** `CMExists` (three CM points with the given values), the reciprocity clause
     `R1recProps` and the second half of `X6Surj` (`Y₃ → X₆` onto), all read on the route (§5.1).
3. *What would leave the route*: `x6CoarseModuliIdeal` and `elkiesX6StarEveryIdeal` (and `babaGranathRationalAb`'s
   `X₆` form, `rayClassCMAb` if only used for `X₆`), replaced by (b), (c) (Lin–Yang or Baba–Granath on `Y₃/N`) and
   (d). Net: two GLUE fields out, at least two new leaves in ((b) textbook, (c) printed), plus the glue for (d) unless
   (c)'s print states the fibre clause. **Not a net GLUE gain by itself**; its value is following the manuscript
   (no `X₆` at all, L421-441) rather than the count.


## 6. Labels, on-the-spot steps, Known issues

* **ELLIOT-literature**: `CMjDegree` (L586-587) and `CMPotentialGood` (L596-597) are classical facts the manuscript uses
  without a citation.
* **ELLIOT (uncited manuscript step), L597-598**, "This extension does not change its stable Faltings height". It is not a
  source issue and not false. For the definition in the tree (an infimum over all finite extensions) it is
  `G0StableBC.StableHeightBaseChange`, proved in the tree and already used by the chain (`hBC` in
  `CMBranch/Open4.lean`). In the CM branch it is built into `CMHeight62`, whose conclusion bounds `h_F^st(E)` by a model over
  the extension `L₁`. No hypothesis is missing.
* **On-the-spot (L598-599, reduced CM period)**. The manuscript gives no source. The Lean proof (§2.2, complete, no
  leaf) follows the classical argument. The lattice of `E^σ(ℂ)` is homothetic to a proper fractional ideal of `End(E) ≅ R` (T35, T11a/b as
  `HomLatticeCorr`, `T11b`). A reduced basis gives `|Re τ| ≤ 1/2` and `|τ| ≥ 1`, hence `Im τ ≥ √3/2`. `τ` is a root of a
  primitive form `(a, b, c')` of discriminant `Δ_R` with `a ≥ 1` (Cox), hence `Im τ = √|Δ_R|/(2a) ≤ √|Δ_R|/2`.
* **On-the-spot (L620-621, "additivity")**. The manuscript writes "additivity". The half used here (`h(A × Z) ≤ h(A) +
  h(Z)`) is proved from the definition (§2.1), with the product of near-optimal metrized models. Faltings 1983 §1
  states equality (UNVERIFIED locator); no leaf is needed.
* **Known issues**: none new. cm-branch's Known issue 2 (the CM branch needs A8 without NoCM) is unchanged; it is the
  content of `CMFibreSplit` (§2.3). No Gross–Zagier or Tian–Yuan–Zhang argument is used. No consumer's statement was
  changed. The `_r5` copies are new constants with weakened statements (`R5ptProps` replaced by `True`, the field `r5`
  replaced by `True`), each implied by its original.


## 7. The fold

* **The next generation is written** (`ZInQKernel/Contrib/OneProof/CMBranch/Open73.lean`, generated by
  `scratch/cm-branch2/gen/gen_open73.py`; VERIFIED, compiled, standard axioms, `scratch/cm-branch2/axioms3-out.txt`):
  ```lean
  structure HDec.HSyn.OpenResearchLeaves54CM : Prop  -- OpenResearchLeaves53 − gonzalezRotgerThm512X6RCF + 5 CM fields
  theorem HDec.HSyn.sixContactMin_of_open73_cm (r : OpenResearchLeaves54CM) (t : OpenTextbookLeaves18)
      (l : OpenAddedLeaves27) : ZInQ.SixContactMin
  ```
  The two bundles that carried the field (`OpenResearchLeaves36EBCF`, `35EBCF`) are copied without it (`_cm`), with the
  three conversions verbatim minus that line. A closure scan of `sixContactMin_of_open73_cm` (`gruse73-out.txt`) finds no González–Rotger constant. So the fold is:
switch `frozenTarget`'s research bundle to
  `OpenResearchLeaves54CM` and its first argument to `sixContactMin_of_open73_cm r t l`
  (`scratch/cm-branch2/autofold.json`). It is not the mechanical autofold (no top field is discharged by a proof of its
  own statement), but it needs no further Lean.
* **Dry run**: `CMBranch2.lean` itself (VERIFIED: `lake build ZInQKernel.Contrib.OneProof.CMBranch2`, standard axioms,
  `scratch/cm-branch2/axioms2-out.txt`). `#discharges` output: `scratch/cm-branch2/discharges.txt` (§7.1).
* **Net GLUE change**: GLUE column 0 (+`CMFibreSplit`, −`gonzalezRotgerThm512X6RCF`). New leaves pending review: 4
  (cm-branch's), so the strict count is +4 until they are rated.

### 7.1 `#discharges` (VERIFIED)

`scratch/cm-branch2/Discharges.lean` (imports Main, Discharges, `CMBranch2`), output `scratch/cm-branch2/discharges.txt`:
"34 open hypotheses, 17130 theorems checked, 123 discharge one" (rerun after `CoxProof.lean`). 19 of them are the pre-existing reductions also
reported on the base (cm-branch reported the same 19). The other 104 are projections of the copied bundle structures
(`OpenResearchLeavesNGMEB_r5.r9a`, …), which `#discharges` reads as "discharges" because a projection of a structure field
has the field's type. This is the known noise for copied structures in Contrib modules (raynaud-narrow). No CM-branch
theorem discharges a top field, as expected: the contribution re-routes; it does not prove a field's statement.

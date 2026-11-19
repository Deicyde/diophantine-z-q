# Active residual witness: verification


## Update (2026-11-18)

The module `ZInQKernel.Contrib.CloudB3RC53.GenuineInst.ResidualAfterT` is now part of the integration branch, so `Witness.lean` imports it and calls `ZInQ.Contrib.CloudB3RC53.GenuineInst.residualRankCounts_afterT` directly; the former copied section `AfterTCopy` described below has been removed. The copied local Kummer section is unchanged.

## Result

`Witness.lean` applies three RC53 residual-count constructors to one instance in which the
derivative labels, the old Kummer labels, the local conditions, the support change and the residual
model carry content:

* `ZInQ.Contrib.CloudB3RC53.Mattuck.residualRankCounts_genuine` (`activeGenuineCounts`) and
  `ZInQ.Contrib.CloudB3RC53.GenuineInst.residualRankCounts_actual` (`activeActualCounts`), with
  coefficients `𝔽₂`: `2 ≤ genericRank < rankTot`, `genericRank ≤ 294`;
* `ZInQ.Contrib.CloudB3RC53.GenuineInst.residualRankCounts_afterT` (`activeAfterTCounts`, through a
  verbatim copy), the transfer after inverting `t`: `2 ≤ genericRank ≤ rankTot`,
  `genericRank ≤ 294`, with the active comparison blocks at the places above `13` non-acyclic over
  `𝔽₂[[t]]` and acyclic over `𝔽₂((t))`.

The instance and the status of every input are in `Hypotheses.md`. Summary:

* `K = ℚ(i)`, `E₁₁ : y² = x(x − 11)(x + 33)`, `N = 66`, moving prime `5`, derivative prime `7`,
  active prime `13`; `S` = places above `{2, 3, 5, 7, 11}`, `S'` adds the places above `13`;
  coefficients the actual residual module `𝔽₂ ⊗ M₁` of `E₁₁` (index `j = 0`).
* Genuine local conditions: the Kummer complex of `E₁₁(K_v)` above `2, 3, 11`, the relaxed
  derivative condition `τ≤1` above `7`, the full condition above `5`; unramified conditions at the
  active places.
* The residual model consists of the cohomology of the global complex, of the local conditions and
  of the local complexes, with the induced maps, and maps to the genuine Selmer complex by an actual
  quasi-isomorphism (`formalMap_quasiIso`, valid for arbitrary local conditions over a field).
* `hcondD` and `hfull` are used with realized premises; `hUm` holds with equality, its left side is
  at least `2`, and the old Kummer rows have exactly Mattuck's dimension with nonzero `H¹`; `hLm`
  has left side at least `2`.
* Over `𝔽₂` the text's change from the unramified to the full condition at an active place has a
  non-acyclic quotient (`active_full_change_not_acyclic`); the first two constructors are applied
  with a contractible thickening instead. The text's case is the third constructor: the free model
  over `𝔽₂[[t]]`, the active blocks `[𝔽₂[[t]]² --((1+t)^e − 1)--> 𝔽₂[[t]]²]` above `13`, and the
  homotopy equivalence of the generic minimal model with the base change of the free model, obtained
  through the generic original-support model (`afterT_active_case`, `afterE`).
* Model-level parts (see `Hypotheses.md`): the `𝔽₂[[t]]` smaller-support model is the constant
  extension of the residual cone, the active blocks are the text's reduction of (4.4) rather than
  Galois cochains with `𝔽₂[[t]]` coefficients, and the integral original-support model is a split
  extension.

## Verification performed

* Base revision `6ea158a404343c90a445c129cd0d1f3a0d4b8ddc` (detached worktree; the consumers'
  modules were already compiled). No existing file was edited and no prerequisite module was
  built. Repository operations: at the start, one read-only query of the current revision and of
  the working-tree status of the worktree; later, as instructed, a fetch of the branch that adds
  `GenuineInst/ResidualAfterT.lean` (revision `40dafaff0c0cb5339234e30ee5cb214d334fa7b3`) into a
  remote-tracking ref of the integration checkout, a read of that file, and read-only comparisons
  of that revision with the base. Nothing was committed, checked out or changed in a working tree.
  Nobody was contacted.
* `Witness.lean` was compiled as a single file with the repository's environment, six Lean worker
  threads, CPU affinity 64–79 and niceness 10: exit status 0, no errors and no warnings, about 75
  seconds.
* Options: `maxHeartbeats 400000` and `backward.isDefEq.respectTransparency false` (as in the
  earlier residual witness), the latter after the copied Kummer section. The copied
  `ResidualAfterT` section is compiled with the default options (`maxHeartbeats 200000`,
  `respectTransparency true`), set inside its own section.
* Source guard: no `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, notation, macro,
  syntax, `#eval`, `run_cmd`, `#check` or `#print` in `Witness.lean`. Finite facts are proved by
  `decide` and `norm_num`. No new proposition is assumed: the printed inputs are the existing
  explicit hypotheses. The only new `Prop`-valued definition is the abbreviation `Good C`
  ("finite cohomology vanishing outside degrees `0, 1, 2`"), proved for every complex it is applied
  to; `ModelMap` and `CHomotopy` are structures of data.
* Public text guard: no internal tool, platform or session names and no filesystem paths in the
  shipped files.
* Axiom audit: a separate copy of `Witness.lean` followed by `#print axioms` for each of its 452
  named theorems, definitions, abbreviations and named instances (including both copied sections).
  Every report is a subset of `[propext, Classical.choice, Quot.sound]`; 436 use exactly these
  three. `Axioms.txt` is the complete list. The audit copy is not shipped.
* Copied sections, each a verbatim copy of the declarations of a module whose compiled form is not
  part of this build, with only the namespace changed:
  * `LocalKummer`: `ZInQKernel.Contrib.OneProof.RC.CoefModules.Kummer` (60382 bytes, SHA-256
    `e16fd9b3aa8c3156a16d41f90ac8f92e40f8656edf206e127b5ad45196003cb3`);
  * `AfterTCopy`: `ZInQKernel.Contrib.CloudB3RC53.GenuineInst.ResidualAfterT` at revision
    `40dafaff0c0cb5339234e30ee5cb214d334fa7b3` (11165 bytes, SHA-256
    `1c74454da1aea7339c515d2a4632f9cde3e61821d408d33f0d41f9cc017d8077`). Its only import,
    `Mattuck/ResidualGenuine.lean`, and that file's direct dependencies are byte-identical between
    the base and that revision. Compiling against the module itself needs a worktree at that
    revision.

## Main statements

Namespace `ZInQ.Contrib.RC53Assist.ResidualWitnessActive`. In the first group `k` is a field and
`GS, Gv, loc, M, Δ` are arbitrary Galois-type data (as in the repository's `selData`); `v` is a
finite place of `ℚ(i)`; `R → A` is an algebra and `S` a commutative ring; `Rt = 𝔽₂[[t]]`,
`Kt = 𝔽₂((t))`. Each statement below has axioms `[propext, Classical.choice, Quot.sound]`.

```lean
theorem homologyModelTo_quasiIso (C : CochainComplex (ModuleCat.{0} k) ℤ) :
    QuasiIso (homologyModelTo C)

theorem exists_htpy {X Y : CochainComplex (ModuleCat.{0} k) ℤ} (f : X ⟶ Y) (n : ℤ) :
    ∃ h : X.homology n ⟶ Y.X (n - 1), h ≫ Y.d (n - 1) n =
      ((homologyModelTo X).f n ≫ f.f n : X.homology n ⟶ Y.X n) -
        HomologicalComplex.homologyMap f n ≫ (homologyModelTo Y).f n

theorem ModelMap.sel_quasiIso (F : ModelMap D₁ D₂) (hG : QuasiIso (GHom.toCC F.gG))
    (hU : QuasiIso (GHom.toCC F.gU)) (hL : QuasiIso (GHom.toCC F.gL)) :
    QuasiIso (GHom.toCC F.sel)

theorem piMap_quasiIso {ι : Type} {A B : ι → GCx k} (f : ∀ v, GHom (A v) (B v))
    (hf : ∀ v, QuasiIso (GHom.toCC (f v))) : QuasiIso (GHom.toCC (piMap f))

theorem formalMap_quasiIso :
    QuasiIso (GHom.toCC (formalMap GS Gv loc M Δ).sel)

theorem newPlaces_nonempty : Nonempty (NewPlaces SmallK SmallS SmallS')

theorem Tv_trivial (σ : Gloc SmallK v) (t : Tv v) : σ • t = t

theorem kumIota_equivariant (σ : Gloc SmallK v) (t : Tv v) :
    kumIota v (σ • t) = σ • kumIota v t

theorem kumLambda_injective : Function.Injective (kumLambda v)

theorem finrank_kum_H1_eq :
    Module.finrank (ZMod 2) ((kumCC v).homology 1) =
      Module.finrank (ZMod 2) (ModN (smallCurve (v.adicCompletion SmallK)).toAffine.Point 2)

theorem kum_dims_eq :
    Module.finrank (ZMod 2) ((kumCC v).homology 0) +
        Module.finrank (ZMod 2) ((kumCC v).homology 1) +
        Module.finrank (ZMod 2) ((kumCC v).homology 2) =
      kummerResidualDim v (smallLocalModels v)

theorem kum_H1_pos : 0 < Module.finrank (ZMod 2) ((kumCC v).homology 1)

theorem actΔ_U_oldKummer (v : Places SmallK SmallS) (hv : actCond v.1.asIdeal = .oldKummer) :
    actΔ.U v = ofCC (kumCC v.1)

theorem actΔ_U_derivRelaxed (v : Places SmallK SmallS) (hv : actCond v.1.asIdeal = .derivRelaxed) :
    actΔ.U v = ofCC (relCC v.1)

theorem actΔ_U_full (v : Places SmallK SmallS) (hv : actCond v.1.asIdeal = .full) :
    actΔ.U v = ofCC (locCC v.1)

theorem oldKummer_places_exact (v : Places SmallK SmallS)
    (hv : actCond v.1.asIdeal = .oldKummer) :
    actΔ.U v = ofCC (kumCC v.1) ∧ 0 < Module.finrank (ZMod 2) ((kumCC v.1).homology 1) ∧
      Module.finrank (ZMod 2) ((kumCC v.1).homology 0) +
          Module.finrank (ZMod 2) ((kumCC v.1).homology 1) +
          Module.finrank (ZMod 2) ((kumCC v.1).homology 2) =
        kummerResidualDim v.1 (smallLocalModels v.1)

theorem act_hUm (h28 : MilneADT_I_2_8) :
    ∑ n ∈ actDegrees, Module.finrank (ZMod 2) (actSel.U.X n) ≤
      ∑ p ∈ chargedPrimes 66 5 actD,
        condSum SmallK (genCondDimFun2 SmallK SmallS actCond
          (kummerDimOfCurves SmallK smallLocalModels (kd2OfCurves SmallK smallLocalModels))) p

theorem act_hUm_eq (h28 : MilneADT_I_2_8) :
    ∑ n ∈ actDegrees, Module.finrank (ZMod 2) (actSel.U.X n) =
      ∑ p ∈ chargedPrimes 66 5 actD,
        condSum SmallK (genCondDimFun2 SmallK SmallS actCond
          (kummerDimOfCurves SmallK smallLocalModels (kd2OfCurves SmallK smallLocalModels))) p

theorem act_hLm (h28 : MilneADT_I_2_8) :
    ∑ n ∈ actDegrees, Module.finrank (ZMod 2) (actSel.L.X (n - 1)) ≤
      ∑ p ∈ chargedPrimes 66 5 actD, genLocSum SmallK SmallS p

theorem actPP_quasiIso : QuasiIso actPP

theorem actPL_quasiIso (h788 : NekovarProp788ii SmallK) : QuasiIso actPL

theorem exists_derivative_place :
    ∃ v : Places SmallK SmallS, actCond v.1.asIdeal = .derivRelaxed

theorem exists_oldKummer_place :
    ∃ v : Places SmallK SmallS, actCond v.1.asIdeal = .oldKummer

theorem act_U_positive (h28 : MilneADT_I_2_8) :
    2 ≤ ∑ n ∈ actDegrees, Module.finrank (ZMod 2) (actSel.U.X n)

theorem act_L_positive (h28 : MilneADT_I_2_8) :
    2 ≤ ∑ n ∈ actDegrees, Module.finrank (ZMod 2) (actSel.L.X (n - 1))

theorem actW_nontrivial : Nontrivial (actW.X 0)

theorem actP_d_ne_zero :
    ∃ x : (selCx actSel).toCC.X 0, ((selCx actSel).toCC.d 0 (0 + 1)).hom x ≠ 0

theorem activeBound :
    residualBoundConstant (2 * 66).primeFactors.card 0 actD.card = 294

theorem residualRankCounts_genuine_active (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) (h788 : NekovarProp788ii SmallK) :
    (activeGenuineCounts h410 h51 h28 h23 h788).genericRank ≤
        (activeGenuineCounts h410 h51 h28 h23 h788).rankTot ∧
      (activeGenuineCounts h410 h51 h28 h23 h788).genericRank ≤ 294

theorem residualRankCounts_actual_active (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) (h788 : NekovarProp788ii SmallK) :
    (activeActualCounts h410 h51 h28 h23 h788).genericRank ≤
        (activeActualCounts h410 h51 h28 h23 h788).rankTot ∧
      (activeActualCounts h410 h51 h28 h23 h788).genericRank ≤ 294

theorem activeGenuineCounts_strict (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) (h788 : NekovarProp788ii SmallK) :
    (activeGenuineCounts h410 h51 h28 h23 h788).genericRank <
      (activeGenuineCounts h410 h51 h28 h23 h788).rankTot

theorem activeActualCounts_strict (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) (h788 : NekovarProp788ii SmallK) :
    (activeActualCounts h410 h51 h28 h23 h788).genericRank <
      (activeActualCounts h410 h51 h28 h23 h788).rankTot

theorem two_le_genericRank (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) (h788 : NekovarProp788ii SmallK) :
    2 ≤ (activeGenuineCounts h410 h51 h28 h23 h788).genericRank ∧
      2 ≤ (activeActualCounts h410 h51 h28 h23 h788).genericRank

theorem active_instance_nondegenerate (h28 : MilneADT_I_2_8) :
    (∃ v : Places SmallK SmallS, actCond v.1.asIdeal = .derivRelaxed) ∧
      (∃ v : Places SmallK SmallS, actCond v.1.asIdeal = .oldKummer) ∧
      Nonempty (NewPlaces SmallK SmallS SmallS') ∧
      2 ≤ ∑ n ∈ actDegrees, Module.finrank (ZMod 2) (actSel.U.X n) ∧
      2 ≤ ∑ n ∈ actDegrees, Module.finrank (ZMod 2) (actSel.L.X (n - 1)) ∧
      Nontrivial (actW.X 0) ∧
      ∃ x : (selCx actSel).toCC.X 0, ((selCx actSel).toCC.d 0 (0 + 1)).hom x ≠ 0

theorem active_unramified_not_full (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (q : NewPlaces SmallK SmallS SmallS')
    (φ : GHom (natCx (contCochains (ZMod 2) (GUr SmallK q.1) (ResMod (urFactor SmallK q) SmallM)))
      (natCx (contCochains (ZMod 2) (Gloc SmallK q.1)
        (ResMod (locMap SmallK SmallS' q.1) (ResMod (inflMap SmallK smallS_sub) SmallM))))) :
    ¬ QuasiIso (GHom.toCC φ)

theorem active_full_change_not_acyclic (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (q : NewPlaces SmallK SmallS SmallS') {W : GCx (ZMod 2)}
    (f : GHom (natCx (contCochains (ZMod 2) (GUr SmallK q.1) (ResMod (urFactor SmallK q) SmallM)))
      (natCx (contCochains (ZMod 2) (Gloc SmallK q.1)
        (ResMod (locMap SmallK SmallS' q.1) (ResMod (inflMap SmallK smallS_sub) SmallM)))))
    (g : GHom (natCx (contCochains (ZMod 2) (Gloc SmallK q.1)
        (ResMod (locMap SmallK SmallS' q.1) (ResMod (inflMap SmallK smallS_sub) SmallM)))) W)
    (hfg : ∀ i u, g.f i i rfl (f.f i i rfl u) = 0)
    (hinj : ∀ i, Function.Injective (f.f i i rfl))
    (hsurj : ∀ i, Function.Surjective (g.f i i rfl))
    (hex : ∀ i u, g.f i i rfl u = 0 → ∃ u', f.f i i rfl u' = u) :
    ¬ W.toCC.Acyclic

theorem bcG_acyclic_of_homotopy {C : GCx R} {c : R} (H : CHomotopy C c)
    (hc : IsUnit (algebraMap R A c)) : GAcyclic (bcG A C)

theorem activeCone_acyclic_of_isUnit {c : S} (hc : IsUnit c) :
    GAcyclic (activeCone S c)

theorem activeCone_not_acyclic {c : S} (hc : ¬ IsUnit c) : ¬ GAcyclic (activeCone S c)

theorem activeC_constantCoeff (e : ℤ) : PowerSeries.constantCoeff (activeC e) = 0

theorem activeC_not_isUnit (e : ℤ) : ¬ IsUnit (activeC e)

theorem activeC_eq_X_mul {e : ℤ} (he : e = 1 ∨ e = -1) :
    ∃ v : Rtˣ, activeC e = PowerSeries.X * (v : Rt)

theorem activeC_isUnit_generic {e : ℤ} (he : e = 1 ∨ e = -1) :
    IsUnit (algebraMap Rt Kt (activeC e))

theorem activeW_not_acyclic : ¬ activeW.toCC.Acyclic

theorem activeW'_acyclic : activeW'.toCC.Acyclic

theorem afterSES_shortExact : afterSES.ShortExact

theorem afterIncl_quasiIso : QuasiIso (GHom.toCC afterIncl)

theorem afterP_hred (n : ℤ) :
    Module.finrank Rt (afterP.X n) = Module.finrank (ZMod 2) ((selCx actSel).X n)

theorem afterT_active_case :
    Nonempty (NewPlaces SmallK SmallS SmallS') ∧
      (∀ q, PowerSeries.constantCoeff (activeC (activeExp q)) = 0 ∧
        ∃ v : Rtˣ, activeC (activeExp q) = PowerSeries.X * (v : Rt)) ∧
      ¬ activeW.toCC.Acyclic ∧ activeW'.toCC.Acyclic ∧ QuasiIso (GHom.toCC afterIncl)

theorem activeAfterTCounts_genericRank (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) :
    (activeAfterTCounts h410 h51 h28 h23).genericRank =
      ∑ n ∈ actDegrees, Module.finrank Kt (afterQ'.homology n)

theorem activeAfterTCounts_rankTot (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) :
    (activeAfterTCounts h410 h51 h28 h23).rankTot =
      ∑ n ∈ actDegrees, Module.finrank (ZMod 2) ((selCx actSel).X n)

theorem residualRankCounts_afterT_active (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) :
    (activeAfterTCounts h410 h51 h28 h23).genericRank ≤
        (activeAfterTCounts h410 h51 h28 h23).rankTot ∧
      (activeAfterTCounts h410 h51 h28 h23).genericRank ≤ 294

theorem two_le_afterT_genericRank (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) :
    2 ≤ (activeAfterTCounts h410 h51 h28 h23).genericRank
```

## The target declarations

* `ZInQ.Contrib.CloudB3RC53.Mattuck.residualRankCounts_genuine` (source 6952 bytes, SHA-256
  `41da1457b6701d6a8b150223a7e9afe23bc4f838d50f3fea01027345477d33dd`)
* `ZInQ.Contrib.CloudB3RC53.GenuineInst.residualRankCounts_actual` (source 16216 bytes, SHA-256
  `e40818f9ec3bb06b69a37af56e9c71eaa23fb0764dd5e12b2660ddc7b3e9a657`)
* `ZInQ.Contrib.CloudB3RC53.GenuineInst.residualRankCounts_afterT` (source 11165 bytes, SHA-256
  `1c74454da1aea7339c515d2a4632f9cde3e61821d408d33f0d41f9cc017d8077`, revision `40dafaff`)

## File identities

* `Witness.lean`: 251621 bytes; SHA-256 `d2c18bd8744e5a32fbe8d7e41dd69eae59583ecab49f771ee45b60b55ec47ebf`.
* `Hypotheses.md`: 12517 bytes; SHA-256 `f0edf2bec3f6f7e9496346cd5189923f40519ef680673c250ea0317fa0928835`.
* `Axioms.txt`: 46302 bytes; SHA-256 `20c1c0d231b0108f419d2973a48b5eaaac0986576c9733f73fe02cc30bd22d19`.

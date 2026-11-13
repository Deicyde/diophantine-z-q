# diff-bridge results log

## Step 0: setup (VERIFIED)
- Targets: `GlueConductor.HilbertDifferentFormula` (Breaks.lean:341), `GlueConductor.SerreDifferentBound`
  (Breaks.lean:350). `ramGroup L P i = (P ^ (i + 1)).inertia Gal(L/ℚ)`; `ramCard = Nat.card ∘ ramGroup`.
- Merged origin/wip/tc-port (f22bb604): 397 port1 + 714 kw-rest + 7 extra Tau Ceti oct16 modules.
- Tau Ceti `Ideal.ramificationGroup G Q i := (Q ^ (i + 1)).inertia G` (TauCeti/RingTheory/Ideal/RamificationGroup.lean:60),
  the same term as `ramGroup` (VERIFIED, read).
- Tau Ceti `IsDedekindDomain.HeightOneSpectrum.multiplicity_differentIdeal_eq_finsum_card_ramificationGroup_sub_one`
  (LocalGlobal/Different/Exponent.lean): global Hilbert formula over `𝓞 K` (VERIFIED, read).
- Tau Ceti `multiplicity_differentIdeal_le_ramificationIdx_sub_one_add_multiplicity_span`
  (LocalGlobal/Different/Wild.lean): global Serre bound `v_w(𝔇) ≤ e - 1 + v_w(e)` (VERIFIED, read).
  Wild.lean is outside port1/kw-rest: its oct16 closure (177 modules) needs 11 modules outside the lists,
  listed in scratch/diff-bridge/wild-extra.txt; vendored by this task with tcport.py (oct16, 5a01f5fe).
- `lake build ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.LocalGlobal.Different.Wild`:
  Build completed successfully (4051 jobs), no change to the vendored files (VERIFIED, 59 s).

## Step 1: local leaves importable (VERIFIED, compiled)
- `ZInQKernel/Contrib/Different/Local.lean`: scratch/t-different/All.lean with its local copies of
  `lowerRam`/`lowerRamR`/`herbrandPhi`/`upperRam`/`lowerRam_tower` and of the four leaf defs removed,
  importing `ZInQKernel.HDecomp.Conductor.I6Base` instead. `lake build ZInQKernel.Contrib.Different.Local`:
  Build completed successfully (warnings only: deprecations, unused section variables), 2 min.
- scratch/diff-bridge/AxiomsLocal.lean (`example : PkgI6.X := PkgI6.x` for the four, then #print axioms):
  all four depend on axioms [propext, Classical.choice, Quot.sound].

## Step 2: T20 global (VERIFIED, compiled: `lake env lean scratch/diff-bridge/Global.lean`, no errors)
- `DiffBridge.range_algebraMap_ringOfIntegers_rat : (algebraMap (𝓞 ℚ) ℚ).range = (algebraMap ℤ ℚ).range`.
- `DiffBridge.differentIdeal_int_eq_differentIdeal_ringOfIntegers_rat :
   differentIdeal ℤ (𝓞 L) = differentIdeal (𝓞 ℚ) (𝓞 L)` (via `coeSubmodule_differentIdeal` and
   `Submodule.mem_traceDual`: both trace duals are cut out by the same range in ℚ).
- `DiffBridge.ramificationIdx_int_eq : P.ramificationIdx ℤ = P.ramificationIdx (𝓞 ℚ)` (unfold
  `Ideal.ramificationIdx_def`; `ℤ → 𝓞 ℚ` surjective).
- `DiffBridge.ramificationGroup_eq_ramGroup : P.ramificationGroup Gal(L/ℚ) i = GlueConductor.ramGroup L P i`
  (Tau Ceti `Ideal.ramificationGroup_def`; same action instance, closes by the lemma).
- `DiffBridge.hilbertDifferentFormula : GlueConductor.HilbertDifferentFormula` from Tau Ceti
  `multiplicity_differentIdeal_eq_finsum_card_ramificationGroup_sub_one` (K = ℚ),
  `Ideal.exists_forall_ramificationGroup_eq_bot` (FaithfulSMul via `IsGaloisGroup.faithful (𝓞 ℚ)`),
  `finsum_eq_sum_of_support_subset`, `Ideal.finiteMultiplicity`, `pow_multiplicity_dvd`,
  `FiniteMultiplicity.not_pow_dvd_of_multiplicity_lt`.

## Step 3: T21 global and the Contrib file (VERIFIED, compiled)
- `ZInQ.Contrib.Different.multiplicity_span_ramificationIdx_le : multiplicity P (span {(e : 𝓞 L)}) ≤ e * padicValNat p e`
  (e = p^k m, p ∤ m; `emultiplicity_mul/pow` for the prime ideal P; `v_P(p) = e` by
  `Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity`; `m ∉ P` from `P.under ℤ = (p)`).
- `ZInQ.Contrib.Different.serreDifferentBound : GlueConductor.SerreDifferentBound` from Tau Ceti
  `multiplicity_differentIdeal_le_ramificationIdx_sub_one_add_multiplicity_span` (K = ℚ, v = w.under (𝓞 ℚ)).
- `ZInQ.Contrib.Different.D1_genuine_closed`: `GlueConductor.D1_genuine` with both leaves applied.
- File `ZInQKernel/Contrib/Different/Global.lean` (namespace `ZInQ.Contrib.Different`).
  `lake build ZInQKernel.Contrib.Different.Global`: Build completed successfully (9225 jobs).
- scratch/diff-bridge/AxiomsGlobal.lean: `example : GlueConductor.HilbertDifferentFormula := …`,
  `example : GlueConductor.SerreDifferentBound := …` typecheck; #print axioms of
  hilbertDifferentFormula, serreDifferentBound, D1_genuine_closed: [propext, Classical.choice, Quot.sound].

## Step 4: restructure + second proof of T21 via t-different (VERIFIED, compiled)
- Split: `Contrib/Different/Bridge.lean` (bridge lemmas + T20 `hilbertDifferentFormula`; imports Breaks,
  Tau Ceti Exponent, Ideal.RamificationGroup; no Wild), `Contrib/Different/Global.lean` (T21
  `serreDifferentBound` via Tau Ceti Wild + `D1_genuine_closed`), `Contrib/Different/SerreLocal.lean`
  (T21 `serreDifferentBound_of_local` via `PkgI6.differentBound` + `D1_genuine_closed_of_local`).
- Instances for `PkgI6.differentBound (v.adicCompletionIntegers ℚ) (w.adicCompletionIntegers L)` are all found
  (probe, #synth): DVR, `HeightOneSpectrum.isAdicComplete_adicCompletionIntegers`, `PerfectField.ofFinite` with
  `finite_residueField_adicCompletionIntegers`, `adicCompletionIntegersExtensionAlgebra`, `adicCompletionIntegers_moduleFinite`,
  `adicCompletionIntegers_isTorsionFree`, `Algebra.IsAlgebraic.isSeparable_of_perfectField` (scope AdicCompletionExtension).
- `map_asIdeal_eq_maximalIdeal : v.asIdeal.map (algebraMap (𝓞 ℚ) 𝒪_v) = 𝔪_v` (DVR: I = 𝔪^n, multiplicity 1).
- `ramificationIdx_maximalIdeal_adicCompletionIntegers : Ideal.ramificationIdx 𝔪_w 𝒪_v = w.asIdeal.ramificationIdx (𝓞 ℚ)`
  (`ramificationIdx_eq_multiplicity` twice, `multiplicity_map_adicCompletionIntegers`, square
  `adicCompletionIntegersExtension_algebraMap`).
- `lake build ZInQKernel.Contrib.Different.SerreLocal ZInQKernel.Contrib.Different.Global`: success.
  #print axioms serreDifferentBound_of_local, D1_genuine_closed_of_local, hilbertDifferentFormula,
  serreDifferentBound, D1_genuine_closed: [propext, Classical.choice, Quot.sound].

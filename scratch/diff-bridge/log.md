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

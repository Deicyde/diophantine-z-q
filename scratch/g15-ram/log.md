# g15-ram results log

## Step 1 (2026-11-13 04:20 PST): statements
- `scratch/g15-ram/G15Ram.lean` §0: verbatim copies of `ModData`, `U0`, `LocalRamG`, `G15RamG`
  (scratch/g0-mod-newform/NewForm.lean 1684-1690, 2037, 2448-2464) and `G0Galois.G11Out`
  (scratch/g0-mod-galois/part_galois.lean 164).
- §1: named Props `HilbertSerreLadic`, `UpperBreakFix`, `UpperWild`, `WildFixTame` (closed,
  local fields), `TwistShape`, `TwistUpper`, `TwistTame`, `SmallPrimeData`, `LargePrimeData`,
  `LocalData` (on G8's data).
- Compile: `lake env lean scratch/g15-ram/G15Ram.lean` exit 0, no output (VERIFIED, 7 s, after
  `lake build` of the six imported kernel modules).
- Finding F1 (VERIFIED, logical): `G15RamG D u` is a predicate on `D : ModData L A`, whose fields
  are bare representations; for arbitrary `D` it is false (take `r5` with a wildly ramified
  finite-order twist). So it cannot be proved as a closed statement; it is proved here from Props
  on the same `D` (G8's construction) and closed local-field Props.

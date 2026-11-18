# rc-appE-phase (fleet note)

**Main result.** `EvenPhaseData (Ecurve ℓ) L σ D₀` is filled for E_ℓ, every sign σ and every
positive squarefree D₀ prime to 2N with L_*(σD₀) ≠ 0. The retained set is the manuscript's whole
S₀ filter (S₀ = primes(2N)) and z is the manuscript's phase z_D. The theorem is
`evenPhaseData_Ecurve` in `ZInQKernel/Contrib/OneProof/RC/AppE/Assembly.lean`. Its inputs:
- the tree's prints `WaldspurgerCor2` and `ModularNewform`, and the GLUE `HasseConvergence`;
- the new print `RamseyAlgebraicModel`;
- `WaldspurgerNonvanishingTwoPower`, which is the tree's print plus "ψ has two-power order";
- one open GLUE hypothesis, `HalfIntegralTwist` (scoped stop).

**Findings, to report now (not manuscript errors; no manuscript error found):**
1. The tree's print `WaldspurgerNonvanishing` omits the two-power order of ψ. The manuscript
   asserts it (tex 7920–7922, 7944), and `EvenPhaseData.z_root` with `z_sq` needs it. Without it
   the structure cannot be filled on the filter, because a cubic twist stays in a good-Hecke
   eigenspace. Proposed fix: add `∃ k, ψ ^ (2 ^ k) = 1` to the print.
2. `EvenPhaseData` does not bound `retained` from below. `evenPhaseData_singleton` inhabits it
   with `retained = {D₀}` from the tree's print alone, so `EvenPhaseData.minimum` is meaningful
   only with `P.retained = {D | S0Filter S₀ D₀ D}`, which this lane's theorems record. Consumers
   should use `evenPhaseData_Ecurve`, or the structure should get a lower-bound field.

**What compiles.** Seven new files under `ZInQKernel/Contrib/OneProof/RC/AppE/`: Phase, Linear,
Ramsey, Galois, Rational, Assembly, Vacuity (about 1,600 lines). There is no sorry and no axiom.
`#print axioms` gives [propext, Classical.choice, Quot.sound] for all 25 new theorems.

**What remains.** `HalfIntegralTwist` (tex 8099–8103): twisting a weight-3/2 form by a character
gives a form of character ψν² at a level with the same prime support (Shimura 1973, Lemma 3.6,
UNVERIFIED). Proving it on the tree's definition needs the theta-multiplier formula on Γ₀(4),
which is not in Mathlib (several thousand lines). Ramsey's print is not read (locators
UNVERIFIED).

Report: `docs/research/rc-appE-phase.md`.

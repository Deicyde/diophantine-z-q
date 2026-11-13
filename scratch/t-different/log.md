# t-different results log

## Step 1 (22:08 PST): statements copied verbatim
- `scratch/t-different/Statements.lean`: PkgI6 lines 5029-5133 and GlueConductor lines 5717-5746 of
  `scratch/h-decomposition/Leaves.lean`, verbatim (only namespace/section wrappers added).
- Compile: `lake env lean scratch/t-different/Statements.lean`: no errors, no warnings (VERIFIED, 65 s).
- Mathlib 4.35 survey (VERIFIED by reading `.lake/packages/mathlib`):
  * `Mathlib/RingTheory/DedekindDomain/Different.lean`: `differentIdeal`, `conductor_mul_differentIdeal`
    (`conductor(x) * 𝔇 = (f'(x))` when `K(x) = L`), `aeval_derivative_mem_differentIdeal`,
    `pow_sub_one_dvd_differentIdeal` (lower bound `e-1`), `not_dvd_differentIdeal_of_intTrace_notMem`,
    `dvd_differentIdeal_iff` (P ∣ 𝔇 iff ramified).  No upper bound, no Hilbert formula.
  * `Mathlib/RingTheory/Conductor.lean`: `conductor_eq_top_of_adjoin_eq_top`.
  * `Mathlib/RingTheory/Invariant/Basic.lean`: `MulSemiringAction.charpoly G b = ∏ g, (X - C (g • b))`.
  * No lower/upper ramification groups, no Herbrand function, no monogenicity of complete DVR
    extensions (Serre III §6 Prop. 12) in Mathlib: grep for herbrand / ramificationGroup / monogenic
    finds nothing relevant.

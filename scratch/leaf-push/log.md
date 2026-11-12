# leaf-push results log

## Files
- `Push.lean`: §1 copies pkg-I2's abelian-variety/points/inertia defs (I2.lean l.69-140,
  verbatim); new leaves `R08_GrothendieckMonodromy`, `T09_WeilPairing`,
  `T29a_DivisionNormalizer`, `T29b_SplitNormalizer`, `T32a_TameQuadratic`,
  `T32b_QuadraticRamification`; helper defs `IsPadicInt`, `QIntegral`, `IsOUnit`, `IsIntMat`,
  `GQ`, `IsAtPrime`, `inertiaQ`.
- `PushDR.lean`: l.1-1108 of pkg-I4's I4.lean verbatim (B_dR with G_{Q_p}-action, `IsDeRham`),
  then new leaf `PkgI4.T23_FontaineClosure` and helper `ContRep`.

## Compile outcomes (lake env lean, Lean 4.35.0 / Mathlib v4.35.0)
- Push.lean, first version: 3 errors (no `Inv` on `ℍ[ℚ_p,a,b]`; `inertiaQ` needs
  `noncomputable`). Fixed with `IsOUnit` (two-sided inverse inside the integral elements).
  Recompiled: no errors, no warnings. VERIFIED.
- Push.lean with revised T9 (all `n` invertible, nondegenerate up to `d`): no output. VERIFIED.
- PushDR.lean: no errors (53 s). VERIFIED.

## Statements and findings
- R8: Lean form = pkg-I2's `GrothendieckMonodromy` (SGA 7 IX 3.6 + direction of 3.5),
  consequence. Reclassified from "new defs" to "yes (consequence form)".
- T9: first draft required `(n, d) = 1`, which does not cover `ℓ = 5` at C8 step 1 when the
  polarization degree is divisible by 5. Revised: every `n` invertible in `K`, nondegeneracy
  "up to `d`" (left kernel killed by `d`; proof: `ψ` with `λψ = [d]`). Consequence of Mumford
  §§20, 23 (UNVERIFIED locators), enough for `GSp` on `V_ℓ` for every `ℓ` invertible.
- T29: (a) division case written as "integral elements form a ring; ∃ π not in `ℚ_p^×𝒪^×`;
  every `x ≠ 0` in `ℚ_p^×𝒪^× ∪ ℚ_p^×π𝒪^×`" = index exactly 2 (Vignéras II, UNVERIFIED locator);
  (b) split case `N_{GL₂(ℚ_p)}(M₂(ℤ_p)) = ℚ_p^×GL₂(ℤ_p)`. Both exact.
- T32: inertia subgroups of `G_ℚ` are cheap: Mathlib's `ValuationSubring.inertiaSubgroup` for a
  valuation subring `w ⊆ ℚ̄` over `ℤ_(p)` (characterized as a DVR of `ℚ` in which `p` is not a
  unit). (a) `Nat.card {χ : I_w →* ℤˣ // Continuous χ} = 2` for `p` odd; (b) for `d ≡ 1 mod 4`
  squarefree, some inertia element moves `√d` iff `p | d`. Consequences of Serre, Local fields
  IV §2 and Neukirch I-III (UNVERIFIED locators).
- T23: Fontaine's Tannakian closure for continuous `ℚ_p`-representations in matrix form
  (basis change, dual, subquotient of block-triangular, direct sum, Kronecker tensor) over
  pkg-I4's `IsDeRham`. Exact (special case of the published statement).
- Not stated (missing definitions): R1 (dual abelian scheme/polarizations, PEL moduli), R2 and
  R5 (canonical model of `X₆`; ring class fields for R5), R3 (Jacobians of genus-2 curves),
  R16 (`X₁(N)`, `J₁(N)` over ℚ), R17 (absolute upper ramification filtration of `G_{ℚ_p}`
  and the Artin conductor of an ℓ-adic representation), R18-R22 (Faltings height; theta height
  for R22; Belyi maps for R18), T10 (étale cohomology), T11-T12 (analytification).
- Observation: R2's analytic content alone ("a Hauptmodul of `Γ*\ℍ` takes values 0, ∞, −16/27 at
  the elliptic points") is vacuous up to a Möbius change of coordinate; its content is the
  ℚ-structure, i.e. R1. Not stated for this reason.

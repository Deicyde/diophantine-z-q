# x1-belyi (fleet report)

**Main result.** I proved both glue targets of `ZInQKernel/HDecomp/ModCurves/` in Lean from five
literature leaves. The targets are `X1ModelExists` (MC4 + MC10: a pointed smooth proper model of
`X₁(N)` over `ℚ` with function field `ℚ(j)(x(P))`) and `BelyiX1` (MC5: `j/1728` is a Belyi
function on `K_N` with `[K_N : ℚ(j)] ≤ N²`). The kernel definitions are imported, not restated.

- `X1Belyi.belyiX1_of_leaves : TorsionStructure → GoodReductionUnramified → BelyiX1`
- `X1Belyi.x1ModelExists_of_leaves : TorsionStructure → CurveOfFunctionFieldQ → X1ConstantField
  → X1RationalCusp → X1ModelExists`
- `X1Belyi.modCurveLeaves_of` fills the field `x1` of `ModCurveLeaves`.

**What compiles.** `scratch/x1-belyi/X1Belyi.lean` compiles with `lake env lean`: no errors, no
`sorry`. Axioms: `propext`, `Classical.choice`, `Quot.sound`. The glue proved along the way:
- the degree bound, from the Galois conjugates `x(σP)`, `σP ∈ E[N]`;
- transcendence of `j/1728`;
- the change of variables from the place `q(j/1728)` to an irreducible `p ∈ ℚ[j]` with
  `p ∤ j²(j−1728)⁹`;
- good reduction of Mathlib's `E_j` away from `j = 0, 1728`;
- existence of a point of exact order `N`.

**Leaves** (`def … : Prop`; theorem numbers from memory, UNVERIFIED):
- T1: `E[N] ≅ (ℤ/N)²` over an algebraically closed field of characteristic 0 (Silverman III.6.4).
- T2: Néron–Ogg–Shafarevich in function-field form (Serre–Tate 1968, Thm 1).
- M1: smooth projective model of a function field of transcendence degree 1 over `ℚ`, with
  closed points matching places (Stacks, *Curves and function fields*).
- M2: `ℚ` is algebraically closed in `K_N` (Igusa / Shimura §6).
- M3: `K_N` has a place of degree 1, i.e. a rational cusp (Tate curve; Ogg).

**Computed check** (PARI, `N ≤ 7`): the x-coordinate polynomial of points of exact order `N` on
`E_j` is irreducible over `ℚ(j)`, of degree `μ = [SL₂(ℤ):±Γ₁(N)]`. Its discriminant is supported
on `{j, j−1728}`.

**Finding.** The docstring of `LeafModCurves.Ej` (`ModCurves/Defs.lean`) describes an older
Mathlib model. Mathlib 4.35's `ofJNe0Or1728 j` is `⟨j−1728, 0, 0, −36(j−1728)³, −(j−1728)⁵⟩`.

**What remains.**
- The five leaves are formalization targets. M1 is the largest; T1 needs the division-polynomial
  `[n]P` formula, which Mathlib does not have.
- No human review of the leaf statements. One model review: no leaf false, vacuous or stronger than published (caveats in the report).
- Integration: copy the file to `ZInQKernel/HDecomp/ModCurves/X1Belyi.lean`.

Report: `docs/research/x1-belyi.md`. Log: `scratch/x1-belyi/log.md`.

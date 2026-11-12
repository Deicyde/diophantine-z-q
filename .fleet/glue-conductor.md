# glue-conductor (h-trust D1-D5: Glazer's uniform conductor bound)

**Main result.** Every integer or rational inequality in N5's conductor paragraph (L796-857) is
now a Lean theorem: compiled, no `sorry`, axioms `propext`, `Classical.choice` and `Quot.sound`.
D1 is proved over genuine Mathlib definitions from two statable leaves. The level product
`N ≤ Q_R·M_S(u)²` is proved over the repository's own `heightQ`, `heightE0` and
`contactSupport`. Report: `docs/research/glue-conductor.md`.

**Compiles** (`scratch/glue-conductor/`):
- `Breaks.lean`:
  - D1: `upper_break_le` (`u_last ≤ 2δ/e ≤ 2(1+log₂ a!) ≤ 4a²`) and `herbrand_integral`.
  - D1 over genuine definitions: `D1_genuine`, from the leaves `HilbertDifferentFormula` and
    `SerreDifferentBound`, stated over `differentIdeal ℤ (𝓞 L)` and
    `G_i = (P^{i+1}).inertia Gal(L/ℚ)`.
  - D3: `phi_le_self` (`ψ(u) ≥ u`).
  - D4: `swan_le`, `artin_le` (`a_p ≤ 2+2U₀ ≤ E₀`), and the tame case.
  - D2: `char_trivial_of_odd_pgroup`.
  - Constants: `card_GL4_F5` (`|GL₄(𝔽₅)| = G₀`) and `max_le_U0`.
- `Level.lean`: `level_le` (`N ≤ heightQ R · M²`).
- `Dyadic.lean`: `exists_fourth_root` and `fourth_pow_mem`, i.e. `(U^{e+1})⁴ = U^{3e+1}` in any
  complete local ring with `(2) = 𝔪^e`, via Hensel. This replaces the citation of Silverman
  IV.6.4.

**Leaves (10).**
- I6, statable:
  - L1 Serre's different bound (stated);
  - L2 Hilbert's formula (stated);
  - L3 Herbrand's quotient theorem and L7 the subgroup formula (statable for finite towers).
- I6, not statable:
  - L6 local reciprocity with upper numbering;
  - L8 conductor formula for ℓ-adic representations.
- I2, not statable: L4 Raynaud's criterion, L5 semistable implies unipotent inertia, L9 NOS.
- I4, not statable: L10 Carayol Thm (A).

Glue = the proved lemmas, plus Galois theory for `e ≤ a!` (provable, not done).

**Findings.**
- No error in N5 L796-857.
- The D2 "pro-p" step must assume p-power order of the *values* of β (pro-p groups are not
  torsion).
- At p = 2 the field is `L_v` (`e ≤ D`, Galois).
- Given A6, Raynaud is needed only at p = 3.

**Biggest obstacle.** D2-D5 speak of ℓ-adic representations of `G_{ℚ_p}` from an abelian
surface and a newform (semistability, Artin conductors, Carayol). Mathlib v4.35 can state none
of these, nor upper numbering on `G_{ℚ_p}`.

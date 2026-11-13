# r1b-state (fleet summary)

**Result.** R1(b), the analytic uniformization clause of R1 (Shimura–Deligne), is now a concrete
Lean leaf over genuine definitions, `R1bState.R01b_ComplexUniformization' := ∃ Y Φ, R1fpProps Y Φ ∧
R1bProps Y Φ`, replacing `opaque R01b_ComplexUniformization`. `R1bProps` has three clauses:
(a) every `P : QML3 ℂ` has a `ι`-compatible uniformization `ℂ²/ι(𝒪)(τ,1)ᵀ ≃ P.A(ℂ)` (bp-analytic's
`IsUniformization`, `qmLattice`) for some `τ ∈ ℍ`; (b) a family `y : ℍ → Y(ℂ)` whose objects are
uniformized by `Λ_τ` with the standard level structure `a ↦ [ι(a)(τ,1)ᵀ/3]`; (c) regular functions
on Zariski opens are holomorphic along `y`. The Q3 form (`τ ↦ π(P_τ)` holomorphic into `P¹` for
every `π : Y → P¹`) is proved from it, and the existential leaf gives `R1bProps` for every
candidate with `R1fpProps` (via qm-pin's `phi_part`; no `PinUnique`/`MobiusGlue`).

**FibreQMPeriod follows.** g0-thetapoint's `FibreQMPeriod` (restated over build names) is proved
from R1(b), `QMHauptmodul`, the leaf T11a, the leaf candidate `T11aHom` (T11a in `Hom` form) and
six glue Props: `MobiusRigidity` (pure complex analysis), `HauptmodulHolomorphic` and `JDenNonzero`
(theta functions only), `FamilyOrbitsSep`, `R2OnC` (R2 at ℂ-points), `UnifBaseChange`
(`fibreQMPeriod_of_r1b_orbits`). Proved on the way: CM points exist (`cmPointsExist`), the family's
CM values from T11a (`familyCMValues_of_T11a`), `π` depends only on the QM lattice
(`piOfQMLattice_of`), `Γ*`-invariance of `π ∘ y` (`familyOrbitsInv_of`).

**Traps.** No theta/`x/0` in the leaf; the comparison with `jNum/jDen` is used only where `π` is
finite and nonzero; only the type-μ `Ω(τ)` is used, never `∀ Ω`. Numerically (`jden_check.py`):
at the disc −3 point both `Σθ⁸` and `∏θ` vanish (Lean's `jNum/jDen = 0` while `π = ∞`).

**Compiles.** `scratch/r1b-state/R1b.lean` (assembled by `build.sh`, ~1 950 lines, imports build
modules only): 0 errors, no `sorry`, every audited theorem `[propext, Classical.choice,
Quot.sound]`. Consistency probes compiled (`iotaC_mem`, `level_linear`, `level_ker`).

**Review.** One independent model review of the leaf: FAITHFUL WITH CAVEATS (no defect).

**Remains.** The six glue Props; review of `T11aHom` as a leaf; a human check of the faithfulness
argument (docs/research/r1b-state.md §2) and of the Shimura 1967 / Deligne 1971 locators
(UNVERIFIED). Report: docs/research/r1b-state.md.

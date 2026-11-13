# r1b-state: R1(b), the analytic uniformization clause of R1, stated concretely

Task r1b-state, 2026-11-13. Lean: `scratch/r1b-state/R1b.lean`. `build.sh` assembles it from
`PkgI1Copy.part` (pkg-I1's definitions through `QMHauptmodul`, copied verbatim from
`scratch/h-decomposition/Leaves.lean` lines 104-316) and the parts `R1b.part`, `Part2_P1.part`,
`Part3_Fibre.part`, `Part4_Probes.part`, `Part5_Split.part`, `Part6_Family.part`, `Part7_CM.part`,
`Part8_T11a.part`, `Part8b_Hom.part`, `Part8c_Orbits.part`, `Part9_Audit.part` (about 1 950 lines). It imports only build modules:
`ZInQKernel.HDecomp.Analytic.{Uniformization, QMLattice}`, `ZInQKernel.HDecomp.QM.Pin`,
`ZInQKernel.HDecomp.LeafPush2.{R22, UnifBridge}` and `ZInQKernel.HDecomp.Assembly` (build them first
with `lake build`; `Assembly` needs the upstream `ZInQ` helpers). Results log:
`scratch/r1b-state/log.md`. Numerical check: `scratch/r1b-state/jden_check.py`.
No file under `ZInQKernel/` or `blueprint/`, and no other task's notes or scratch files, was edited.

Marks: **VERIFIED** (read in a source, computed, or compiled), **STANDARD** (published, exact
reference), **SPECULATIVE**. Theorem numbers recalled from memory are **UNVERIFIED** (no network).

## 1. Main result

**R1(b) is now a concrete Lean statement over genuine definitions, in the family form that
rv-blueprints' Q3 asks for, and g0-thetapoint's `FibreQMPeriod` follows from it.** The leaf
replaces the placeholder `opaque R01b_ComplexUniformization` of
`scratch/h-decomposition/Leaves.lean` (bundle field `r1an` of `ResearchLeaves`):

```
def R1bState.R01b_ComplexUniformization' : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpProps Y Φ ∧ R1bProps Y Φ
```

`R1bProps Y Φ` has three clauses:

- **(a) every complex object occurs.** Every `P : QML3 ℂ` has a QM-compatible analytic
  uniformization `φ : ℂ²/Λ_τ ≃ P.A(ℂ)` for some `τ ∈ ℍ` (`IsQMUnif`). Here `Λ_τ = ι(𝒪)(τ, 1)ᵀ` is
  bp-analytic's `qmLattice`, and `φ` is an isomorphism of complex Lie groups in bp-analytic's sense
  (`Uniformization.IsUniformization`). The matrix `ι(a)` on `ℂ²` corresponds to `ι_P(a)` on
  `P.A(ℂ)` (`qmAct`).
- **(b) every `τ ∈ ℍ` occurs, in a family.** There is a map `y : ℍ → Y(ℂ)` such that, for every
  `τ ∈ ℍ`, `Φ_ℂ(y(τ))` is the class of an object `P_τ` with a QM-compatible uniformization by
  `Λ_τ`. That uniformization carries the torus's standard level structure
  `a ↦ [ι(a)(τ, 1)ᵀ/3]` to `η_{P_τ}` (`IsQMUnifLevel`). This pins `y(τ)`.
- **(c) the family is holomorphic.** For every Zariski open `U ⊆ Y` and every
  `s ∈ Γ(U, 𝒪_Y)`, the set `{τ ∈ ℍ : y(τ) ∈ U(ℂ)}` is open and `τ ↦ s(y(τ))` is holomorphic on
  it. Values are taken through Mathlib's `Scheme.SpecToEquivOfField` and `Scheme.evaluation`, as
  `ToP1.val` does.

Proved in Lean, with standard axioms only (VERIFIED: `lake env lean scratch/r1b-state/R1b.lean`,
0 errors, no `sorry`; `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for each):

| theorem | content |
|---|---|
| `r1bProps_of_leaf` | the leaf gives `R1bProps Y Φ` for **every** `(Y, Φ)` with `R1fpProps Y Φ`. qm-pin's `phi_part` maps the witness to `Y` compatibly with `Φ`, and `R1bProps.of_hom` transports forward. No `PinUnique` or `MobiusGlue` is needed. |
| `holomorphicP1On_of_family`, `q3_form_of_R1bProps` | Q3's form: every `τ` occurs, and `τ ↦ π(Φ⁻¹[P_τ]) ∈ P¹(ℂ)` is holomorphic on `ℍ` for **every** morphism `π : Y → P¹` (`ToP1`). Holomorphy into `P¹` is defined by charts (`HolomorphicP1On`, with `recipP1 0 = ∞` written out). |
| `fibreQMPeriod_of_r1b` | `FibreQMPeriod'` from the leaf, `PkgI1.QMHauptmodul`, `HauptmodulCompare` and `UnifBaseChange` |
| `hauptmodulCompare_of_parts` | `HauptmodulCompare` from `FamilyHauptmodul`, `PiOfQMLattice`, `JDenNonzero` and the leaf |
| `fibreQMPeriod_of_r1b_parts` | `FibreQMPeriod'` from the leaf, `QMHauptmodul`, and the four glue Props `FamilyHauptmodul`, `PiOfQMLattice`, `JDenNonzero`, `UnifBaseChange` |
| `familyHauptmodul_of_parts` | `FamilyHauptmodul` from `MobiusRigidity` (pure complex analysis), `HauptmodulHolomorphic` (theta functions only), `FamilyOrbits`, `FamilyCMValues`, `CMPointsExist` |
| `cmPointsExist` | `ι(i+j)` fixes `√2 + i`, `ι((1+j)/2)` fixes `i√3`, `ι(2j+ij)` fixes `i√(9+6√2)`, with `det > 0` |
| `familyCMValues_of_T11a` | `FamilyCMValues` from leaf-push2's leaf `T11a_RiemannEnd` and the glue `R2CMOnC` (R2's CM clauses on `ℂ`-points) |
| `fibreQMPeriod_of_r1b_T11a` | `FibreQMPeriod'` from the leaf R1(b), `QMHauptmodul`, the leaf T11a and seven glue Props (`MobiusRigidity`, `HauptmodulHolomorphic`, `FamilyOrbits`, `R2CMOnC`, `PiOfQMLattice`, `JDenNonzero`, `UnifBaseChange`) |
| `piOfQMLattice_of`, `r2CMOnC_of` | `PiOfQMLattice` from `T11aHom` (T11a in `Hom` form) and the glue `R2OnC` (R2's clause list at `ℂ`-points). The analytic `ι`-equivariant isomorphism is algebraic, which gives a `QMIso`. `R2CMOnC` follows from `R2OnC` |
| `familyOrbitsInv_of` | the `Γ*`-invariance half of `FamilyOrbits`, from `T11aHom` and `R2OnC`. For `γ = ι(x)`, `M = μ⁻¹ι(x)` maps `Λ_τ` to `Λ_{γτ}`; `conjO` is the twist `a ↦ x⁻¹ax`; inverse and equivariance come by uniqueness |
| **`fibreQMPeriod_of_r1b_orbits`** | **the finest reduction: `FibreQMPeriod'` from the leaf R1(b), `QMHauptmodul`, the leaf T11a, the leaf candidate `T11aHom`, and six glue Props** (`MobiusRigidity`, `HauptmodulHolomorphic`, `FamilyOrbitsSep`, `R2OnC`, `JDenNonzero`, `UnifBaseChange`) |
| `iotaC_mem`, `iota_mul`, `level_linear`, `level_ker` | consistency probes (§3) |

## 2. Why the leaf is the published statement or a consequence of it, never stronger

*Published statement.* Shimura, Ann. of Math. 85 (1967), Main Theorem I and §§2-3, and Deligne,
Sém. Bourbaki 389 (1971), §4 (all locators UNVERIFIED; the locator audit read Deligne §§4.9-4.17
for R1(a), not for this part):
- the family `A_τ = ℂ²/ι(𝒪)(τ, 1)ᵀ`, `τ ∈ ℍ`, with the Riemann form `Trd(μ⁻¹xȳ)` and level
  structures;
- the complex uniformization of the canonical model, `Y₃(ℂ)^an = G(ℚ)\(ℍ^± × G(𝔸_f)/K₃)`.

*Each clause is a consequence* (STANDARD argument; the step through Lemma P is rv-qm-polar's):
- **(b).** On the component of `(τ, 1)` the object is `(ℂ²/Λ_τ, ι, E_μ, η_τ)`. The map
  `τ ↦ (τ, 1)` is holomorphic into `Y₃(ℂ)^an`. Forgetting `E_μ` costs nothing: by Lemma P it is
  the unique type-`μ` principal polarization. The level structure
  `η_τ(a) = [ι(a)(τ, 1)ᵀ/3]` has `QML3`'s shape: it is `𝒪`-linear with kernel exactly `3𝒪`
  (§3).
- **(c).** Regular functions are holomorphic on the analytification, and `U^an` is open.
- **(a).** Let `ρ` be the analytic representation of `P`. It is a 2-dimensional complex
  representation of `B`, hence `≅ ι ⊗ ℂ` (Skolem–Noether over `B ⊗ ℂ = M₂(ℂ)`). Transport the
  lattice to coordinates where `ρ = ι ⊗ ℂ`. There it is a left `𝒪`-lattice in `B·v`, so it equals
  `ι(𝒪)w`, because `𝒪` has class number one (Eichler; `B` is indefinite). Write
  `w = c(τ', 1)ᵀ` with `τ' ∉ ℝ` (otherwise the real rank would be 2). If `Im τ' < 0`, replace `w`
  by `ι(1 + i)w`: `1 + i ∈ 𝒪^×` has `nrd = 1 − 2 = −1`, so this flips the half plane without
  changing `ι(𝒪)w`. Level structures are forgotten in (a).
- **Nothing more is claimed.** The leaf says nothing about other components of `Y₃(ℂ)` beyond
  (a), and nothing about polarizations, theta functions or `π`.

*The leaf also asserts `R1fpProps Y Φ`.* That is the leaf `R1fp` (R1(a)), so `R01b'` is
"R1(a) and R1(b) on the same `Y₃`": the same theorem, not a combination of publications. It
inherits R1fp's audit caveat ("UNVERIFIED as the full literal leaf; qualified CONSEQUENCE") and
Lemma P as a folded-in published input, like every leaf over the Shimura curve.

*The traps the review listed, and how the statements avoid them.*
- **No theta functions or `x/0` in the leaf.** The comparison with `jNum/jDen` is glue, and it is
  used only where `π(y)` is finite and nonzero (`HauptmodulCompare` takes `c ≠ 0` and
  `π(y) = some c`).
  - The trap is real (VERIFIED numerically, `jden_check.py`). At the disc `−3` point `τ = i√3`
    both `Σθ⁸` and `∏θ` vanish to 30 digits, so Lean's `jNum/jDen` is `0` there while `π = ∞`.
  - At the disc `−4` point, `Σθ⁸ = 33.9` but `∏θ ≈ 0`.
  - At the disc `−24` point, `jNum/jDen = −16/27`.
  - At five sample points, among them the `u = 1` fibre point where `jNum/jDen = J(1)`, `|Σθ⁸|` is
    between 7.7 and 108.
- **No `∀ Ω` statements.** Only pkg-I1's fixed `Ω(τ)`, the type-`μ` period matrix, enters. The
  numbers above show the theta product vanishing at both elliptic CM points: there the type-`μ`
  polarization itself has `∏θ = 0`.
- **Not vacuous.** `R1bProps` has no hypothesis that could fail. Its two compatibility conditions
  are consistent on the torus side (§3). Without that consistency the leaf would be *false*, not
  vacuous.

## 3. Consistency probes (VERIFIED, compiled)

- `iotaC_mem`: for `a ∈ 𝒪`, `ι(a)Λ_τ ⊆ Λ_τ`, so `ι(a)` acts on `ℂ²/Λ_τ`. Supporting lemmas:
  - `iota_mul`: `ι` is multiplicative;
  - `latVec_mul`: `ι(ax)(τ, 1)ᵀ = ι(a)·ι(x)(τ, 1)ᵀ`;
  - `latVec_ofInt`: the coordinates against N5's basis.
- `level_linear`, `level_ker`: `a ↦ ι(a)(τ, 1)ᵀ/3` is `𝒪`-linear, and lies in `Λ_τ` iff
  `a ∈ 3𝒪`. This matches `Level3`'s conventions `η(ab) = ι(a)η(b)` and kernel `3𝒪`. It uses
  `latVec_eq_zero` (`x ↦ ι(x)(τ, 1)ᵀ` is injective on `B` for `Im τ ≠ 0`, from the irrationality
  of `√2`) and `mem_qmLattice_iff`.
- The domain is nonempty: `I ∈ ℍ`, and `Λ_I` is a full lattice (bp-analytic's instances).

## 4. `FibreQMPeriod` from R1(b)

`FibreQMPeriod'` is g0-thetapoint's `HSyn.G0Split.ThetaPt.FibreQMPeriod` with the same text
except for names:
- the build's `PkgI3.AbVar` replaces the scratch copy `ZInQ.DefFaltings.AbVar`. In the build,
  `ZInQ.DefFaltings` uses `PkgI3.AbVar` itself (`Faltings/Models.lean`: `open PkgI3 (AbVar)`), so
  `LeafAdopt.abVarEquiv` is the identity and is dropped (VERIFIED, read);
- `CPts` and `IsUniformization` are the build's `ZInQ.LeafPush2` ones, which have the same text
  as the `HSyn.G0Split` copies;
- `FibreOver'` is g0-split's `FibreOver` with the same change.

The proof (`fibreQMPeriod_of_r1b`; every step compiled):
1. From `FibreOver` take `emb : K → ℚ̄`, a `ℚ̄`-point `y`, `P` with `Φ(y) = [P]` and
   `π(y) = J(u)`.
2. Choose `ε : ℚ̄ → ℂ` (`IsAlgClosed.lift`).
3. The naturality clause of `R1fpProps` gives `P_ℂ` with `Φ_ℂ(y ∘ Spec ε) = [P_ℂ]` and
   `IsBaseChangeOf ε P P_ℂ`. `ToP1.val_comp` gives `π(y ∘ Spec ε) = J(u) ∈ ℂ`.
4. R1(b)(a) at `P_ℂ` gives `τ ∈ ℍ` and a QM-compatible `φ : ℂ²/Λ_τ ≃ P_ℂ.A(ℂ)`.
5. `HauptmodulCompare` with `c = J(u) ≠ 0` (`jmap_ne_zero`, proved for `u ∉ 𝒞`) gives
   `jDen(Ω(τ)) ≠ 0` and `jNum/jDen = J(u)`.
6. `UnifBaseChange` gives a uniformization of `A(ℂ)_σ` at `σ = ε ∘ emb` with kernel `Λ_τ`.
   Take `F = id`.

The glue Props, each with its argument in the docstring. The finest reduction is
`fibreQMPeriod_of_r1b_orbits`. The coarser Props `HauptmodulCompare`, `FamilyHauptmodul`,
`FamilyCMValues`, `CMPointsExist`, `PiOfQMLattice`, `R2CMOnC` and `FamilyOrbitsInv` are proved
from these:

| Prop | kind | content | status |
|---|---|---|---|
| `T11aHom` | textbook leaf candidate | T11a for homomorphisms `A → B`: every `ℂ`-linear `M` with `MΛ_A ⊆ Λ_B` is induced by a unique homomorphism | leaf-push2's `T11a_RiemannEnd` is its case `A = B`. Same sources: Mumford §1-2, Birkenhake–Lange 1.2.1, GAGA (UNVERIFIED numbers) |
| `MobiusRigidity` | glue, pure analysis | two holomorphic maps `ℍ → P¹` whose fibres are the orbits of the same `G ⊆ GL₂(ℝ)`, the first continuous and onto, that agree at three points with distinct values are equal | true: `F = g∘f` with `g` a continuous bijection of `P¹`, holomorphic off the finitely many critical values (removable singularities), hence Möbius. Mathlib has removable singularities but lacks the degree theory of `P¹ → P¹`. A good crowdsourcing target |
| `HauptmodulHolomorphic` | glue, theta functions only | `QMHauptmodul`'s `f` is holomorphic into `P¹` | `f` is a continuous quotient of holomorphic functions of `τ` |
| `FamilyOrbitsSep` | glue | on the family, equal `π` implies `τ' ∈ Γ*τ` | needs the converse half of T11a(Hom), Skolem–Noether (not in Mathlib 4.35; T13 is proved only in scratch) and "the centralizer of `ι(B)` in `M₂(ℂ)` is the scalars" |
| `R2OnC` | glue | R2's clause list (`R2fpProps`) at `ℂ`-points | coarse moduli of `X₆` over every algebraically closed field of characteristic 0, and `π` is determined by its values on `ℚ̄`-points (Lefschetz principle) |
| `JDenNonzero` | glue, theta functions only | where `f` is finite, `jDen(Ω(τ)) ≠ 0` | `ψ₄∘Ω` is a weight-8 form for `Γ*` with orbifold degree `1/3`, so it vanishes only at the order-6 orbit (disc `−3`, where `f = ∞`). Checked numerically at 8 points. SPECULATIVE until proved |
| `UnifBaseChange` | glue | uniformizations transport along `A_ℚ̄ ≅ P.A` and `IsBaseChangeOf` | base change of points (Yoneda), plus rigidity (leaf T11b) to fix the identity, since neither `FibreOver`'s isomorphism nor `IsBaseChangeOf`'s map is required to be a group map |

*Candidates.* Every glue Prop that quantifies over all candidates `(Y, Φ, π)` satisfying the
clause lists is true because every candidate is the published one. `(Y, Φ) ≅ (Y₃, Φ)`: apply
`phi_part` in both directions; a self-map of a reduced separated scheme that is the identity on
all field points is the identity. `π` is the published map on `ℚ̄`-points: both have the same
fibres and the same three values, so they differ by an algebraic bijection of `P¹`, which is
Möbius and hence the identity (qm-pin's `MobiusGlue`). A morphism is then determined by its
`ℚ̄`-points. This argument is written in `R2OnC`'s docstring and is not compiled.

Where R1(b) is used:
- Clause (a) is consumed directly by `fibreQMPeriod_of_r1b`, at the fibre object.
- The family clauses (b) and (c) are consumed by `familyHauptmodul_of_parts`. Clause (c) gives
  the holomorphy of `τ ↦ π(y(τ))` that `MobiusRigidity` needs. Clause (b) gives the family on
  which `FamilyOrbits` and `FamilyCMValues` are evaluated. On that family, `FamilyOrbitsInv` and
  `FamilyCMValues` are compiled arguments over T11a/`T11aHom` and `R2OnC`.
- In `familyCMValues_of_T11a`, clause (b) and the leaf T11a are combined in a compiled argument:
  - at a fixed point `τ` of `ι(x)`, `(τ, 1)ᵀ` is an eigenvector of `ι(x)` (`latVec_fixed`);
  - multiplication by the eigenvalue `λ` preserves `Λ_τ` (`lam_mem`);
  - by T11a, `λ` is induced by an endomorphism `f ∈ End_𝒪` (`exists_cm_end`);
  - `f² = −1`, `f² − f + 1 = 0` or `f² = −6` follows from the same relation for `λ`, by
    uniqueness in T11a.

`QMHauptmodul` is pkg-I1's composite statement (a consequence of R2, R3 and R4, not a bundle
field).

## 5. Integration notes (for after the announcement)

- **The bundle.** In `Leaves.lean`, the field `r1an : R01b_ComplexUniformization` would become
  `r1an : R1bState.R01b_ComplexUniformization'`. `Leaves.lean` does not import
  `ZInQKernel.HDecomp.Analytic` or `ZInQKernel.HDecomp.QM` (it has its own copies of the QM
  layer), so the integrator either imports the build modules or copies bp-analytic's `Torus`,
  `QMLattice` and `Uniformization` sections. `R1b.part`, `Part2_P1.part` and `Part4_Probes.part`
  need nothing else.
- **g0-assemble.** In `GluePieces2`, the field `fibreQMPeriod` (no. 10, "GLUE, QM-PIN") can be
  replaced by:
  - the six glue Props of `fibreQMPeriod_of_r1b_orbits`;
  - `QMHauptmodul`;
  - the leaf `r1an`;
  - the leaf T11a (already in the bundle as `T11a_RiemannEnd`);
  - the leaf candidate `T11aHom`. It could replace T11a in the bundle, since T11a is its case
    `A = B` (not compiled here).
- **The universal form.** `FibreQMPeriodAll` (every `σ`, every uniformization) follows the same
  way. It additionally needs bp-analytic's uniqueness `IsUniformization.exists_equiv`, with the
  transport between the two uniformization predicates. This is not compiled here.

## 6. What remains

- The six glue Props of §4:
  - `UnifBaseChange` and `R2OnC` are algebraic geometry: base change, rigidity (T11b), and the
    Lefschetz principle.
  - `FamilyOrbitsSep` needs Skolem–Noether in Lean.
  - `MobiusRigidity` is pure complex analysis.
  - `HauptmodulHolomorphic` and `JDenNonzero` concern theta functions on `ℍ` (modular forms on
    `Γ*`).
- The leaf candidate `T11aHom` needs review as a leaf: it is the `Hom` form of the textbook
  T11a.
- A human check of the faithfulness argument of §2, in particular clause (a): class number one of
  `𝒪`, and the claim that every component of `Y₃(ℂ)` is uniformized by `ι(𝒪_g)(τ, 1)ᵀ` with
  `𝒪_g ≅ 𝒪`. Also the exact locators in Shimura 1967 and Deligne 1971.

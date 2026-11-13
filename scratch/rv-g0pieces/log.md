# rv-g0pieces results log

Base: wip/rv-g0pieces (883c4ddf) + `git merge origin/wip/g0-split` (c20fa62b): the ten pieces are
`scratch/g0-split/part_split.lean` lines 70-356 (= `Split.lean` §3′, `HSyn.G0Split`).

## Definitions read (VERIFIED, read in `scratch/g0-split/Split.lean`)
- `PkgI3.AbVar` / `DefFaltings.AbVar`: group object in `Over (Spec K)`, proper, smooth, geometrically
  integral; `dim = topologicalKrullDim X.left`; `baseChange` = `Over.pullback`.
- `stableFaltingsHeight A = ⨅ (E : FinExt K) (g) (M : MetrizedModel A E.L g), modelHeight` (EReal);
  `modelHeight = arakelovDegree / [E:ℚ]` (normalized).
- `IsIsogeny φ = IsMonHom φ ∧ IsFinite ∧ Surjective`; `PkgI3.AbVar.IsIsogenyMor = IsFinite ∧ Surjective`.
- `R1fpProps Y Φ` = proper ∧ smooth rel. dim 1 ∧ a `ℚ̄`-point ∧ naturality of `Φ` under field maps
  `K →ₐ[ℚ] L` only. `R2fpProps Y Φ π` = (π-fibres of `ℚ̄`-points = twist classes) ∧ CM values
  `−4 ↦ 0`, `−3 ↦ ∞`, `−24 ↦ −16/27`.
- `contactSet = {0,−15,−20,−24,−30,−60}`; `M_S(u) = contactSupport` (product of primes, ≥ 1);
  `Q = heightQ heightD = D^(D·E₀)`; manuscript L713 `[L':ℚ] ≤ QM`, L857 `N ≤ QM²` (read).
- Only the three g0-split pieces `FibreSimple`, `ThetaPointOfFibre`, `ModularConstituent` quantify
  universally over triples `(Y, Φ, π)` with `R1fpProps ∧ R2fpProps`; every leaf uses `∃` (grep).

## Computations (VERIFIED, saved scripts)
- `nocm_square_check.py`: `t(u) = 1 + 27J(u)/16 = (H/G³)²`, `1 − t(u) = 3(180F/G³)²` (sympy identity).
  None of Elkies' 24 rational non-elliptic CM values `t_D` (re-entered from scratch/rv-nocm) passes
  the necessary square test, and `H² − t_D G⁶` has no rational root for any row. `F` has rational
  roots exactly `𝒞`; `G`, `H` have none. Consistent with A10 (NoCM).
- `theta_igusa_check.py`: two random real-rooted sextics, period matrices by numerical integration
  (symmetric, `Im Ω > 0`), ten even theta constants: `I4⁵/I10² = (Σθ⁸)⁵/(Πθ²)²` to relative error
  `7e-23`, `1e-22`. With `J2 = I2/8`, `J4 = (4J2² − I4)/96`, `J10 = I10/4096` (STANDARD, UNVERIFIED
  from memory) this is Igusa's `ψ4 = 2⁻²Σθ⁸`, `χ10 = −2⁻¹⁴Πθ²` in Lin–Yang's identification
  (`ψ4 = J2² − 24J4`, `χ10 = −J10/4`), hence `3779136·(Πθ)⁴/(Σθ⁸)⁵ = j` on LY's Igusa vector
  (closes h-v14's UNCHECKED Igusa normalization, numerically).

## Finding (logical, VERIFIED by argument; Lean half below)
- `R1fpProps` does not pin `Φ`: for a permutation `s` of closed points of `Y` with ring isos
  `φ_x : κ(s x) ≅ κ(x)`, `τ(x, ι) = (s x, ι ∘ φ_x)` is a natural bijection of field points, and
  `Φ ∘ τ` satisfies `R1fpProps`; `R2fpProps` survives if `s` maps π-fibres to π-fibres (over
  rational points: needs the two fibres ℚ-isomorphic as finite étale schemes) and fixes the CM fibres.
  So g0-split §3's "these clauses pin down Y₃ and the Hauptmodul" is false for `Φ`.

## Compile outcomes (VERIFIED)
- run1 `lake env lean scratch/rv-g0pieces/Exotic.lean` (Split.lean 1-15140 + section `RvG0Pieces`):
  0 errors, 4m09s; `#print axioms LeafQM.AV.r1r2_relabel` = `[propext, Classical.choice, Quot.sound]`.
- `ExoticCore.lean` (Mathlib only; copies of `specToEquivOfField_comp`, `fieldPt`, `fieldMap`):
  first run unterminated comment / missing `end` (assembly slips), then 0 errors;
  `relabelOver_natural`, `relabelPt_point` standard axioms.
- run2 `Exotic.lean` with section `RvG0Exotic` added (non-geometric relabeling `relabelPt`,
  `relabelPt_bijective`, `relabelPt_comp`, `relabelPt_point`, `relabelOver`, `relabelOver_natural`,
  `r1fp_exotic`): 0 errors, 2m05s; `r1r2_relabel`, `r1fp_exotic`, `relabelPt_point` standard axioms
  (`exotic_run2.summary.txt`).

## Statements compiled
- `r1fp_relabel : R1fpProps Y Φ → IsNaturalRelabel Y τ → R1fpProps Y (relabel Φ τ)`.
- `r2fp_relabel`: R2fp preserved if τ maps π-fibres of ℚ̄-points to π-fibres and fixes the CM fibres.
- `r1fp_exotic (h : R1fpProps Y Φ) (s : Y.left ≃ Y.left) (φ : ∀ x, κ(s x) ≅ κ(x)) :
  R1fpProps Y (relabel Φ (relabelOver Y s φ))`; `relabelPt_point`: τ moves the point of y to s(point).

## Verdicts (see docs/research/rv-g0pieces.md)
UNSURE (universal form; TRUE for the genuine triple): ThetaPointOfFibre, FibreSimple.
TRUE given Glazer §4 (universal form likely robust, SPECULATIVE): ModularConstituent.
TRUE: HeightAdditivity, StableHeightBaseChange, ReverseIsogeny, ProductExists, X1BelyiOnModel,
DimBaseChange, DimFinite. No piece refuted.

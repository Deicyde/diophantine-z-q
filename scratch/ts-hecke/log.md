# ts-hecke results log

Base: wip/ts-hecke (6f296292) + merge of origin/wip/prop-ts-glue. Targets (verbatim in
scratch/prop-ts-glue/PropTSGlue.lean, Part C): HeckeIrreducible, HeckeNormalizationIrr,
HeckeDegree, HeckeBranch, HeckeNoVertRam.

## Step 1. Computation for HeckeIrreducible (`pi0_check.py`, output `pi0_check.out`) — VERIFIED (computed)

- `mulCoord` of Structures.lean agrees with the quaternion product of B = (2,-3); nrd multiplicative.
- |O/3O| = 81, |(O/3O)^x| = 72; nrd mod 3 on (O/3O)^x takes both values 1, 2 (36 each);
  an element of O/3O is a unit iff nrd ≢ 0 mod 3.
- The units of O with coordinates in [-3,3] (338 of them, 156 of norm -1) generate all 72
  elements of (O/3O)^x (so O^x → (O/3O)^x is onto).
- Orbits of O^x on {±1} × (O/3O)^x, u·(s,a) = (s·nrd u, a u^{-1}) (the components of
  Y₃(ℂ) = O^x \ (H^± × (O/3O)^x)): exactly 2 orbits, of size 72 each, separated by the invariant
  s·nrd(a) ∈ {±1}.
- Complex conjugation (s,a) ↦ (-s,a) swaps the two orbits. Hence the two geometric components of
  Y₃ are conjugate and Y₃ is ℚ-irreducible (given the uniformization, STANDARD: Shimura).
- Riemann–Hurwitz for one geometric component (degree 72 over P¹_j, indices 4, 6, 2): g = 4,
  matching the area count 18·(1/3) = 6 = 2g − 2 for Γ₃ ⊂ O¹/±1 (index 18).
- x²+x+1 (the constant field ℚ(ζ₃)) is irreducible over ℚ; over F_p it splits iff p ≡ 1 mod 3
  (p = 5..37 checked). No explicit equation of Y₃ exists to factor; the decisive computation is
  the orbit count above.

Verdict: HeckeIrreducible is TRUE (not speculative any more, modulo the published uniformization).

## Step 2. Lean, Part 1 (`TSHecke.lean`, assembled by `assemble.py`) — VERIFIED (compiled, 0 errors, ~17 s)

- `exists_surjective_of_R1fp`: two triples with R1fp ⇒ a surjective `g : Y' ⟶ Y` (phi_part + κ(x)-points).
- `Y3Connected` (leaf R1conn, witness form: some R1fp triple has `ConnectedSpace Y.left`).
- `heckeIrreducible_of_connected : Y3Connected → HeckeIrreducible` (via curve-glue's
  `componentIrreducible`, copied with infra-smooth-dim's stalk dimensions).
- `connected_of_heckeIrreducible : R1R2fp → HeckeIrreducible → Y3Connected` (so the leaf is exactly
  what is needed).
- all `#print axioms`: [propext, Classical.choice, Quot.sound].

## Step 3. Lean, Part 2: HeckeDegree — VERIFIED (compiled, 0 errors)

- `twistFibre P` = classes whose QM pair is an Aut(𝒪)-twist of P's (a π-fibre, by R2fp).
- `twistFibre_count (hT : ObjBridge.TorsionStructure) P : finite ∧ ncard ≤ 324` (4 inner classes
  from aut-o-finite's `autO_mod_inner_exact`, copied; ≤ 81 level structures per pair from the
  kernel's `Level3.torsor`; helper `pullLevel`, `pullIso`, `innerIso`, `exists_sub_liftO`).
- `GenericFibreCount` (glue: some t ∈ ℚ has ≥ [E:ℚ(X)] ring maps B → ℚ̄ with X ↦ t):
  **proved**, `GenericFibre.lean` (Mathlib only; primitive element made integral, minpoly over the
  integrally closed ℚ[X], separability with denominators cleared by `integerNormalization`, a value
  t avoiding the zeros of D, roots of f(t,T) in ℚ̄, extension of each root map to B by lying over +
  `IsAlgClosed.lift`). 0 errors, axioms standard.
- `heckeDegree_of_torsion : ObjBridge.TorsionStructure → HeckeDegree`. So HeckeDegree rests only on
  the kernel's textbook leaf I2-Tors (Mumford §4).

## Step 4. Lean, Part 3: HeckeNormalizationIrr — VERIFIED (compiled, 0 errors)

- `Units.lean`: `exists_unit_congr` (𝒪^× → (𝒪/3𝒪)^× onto): table of 72 explicit units
  (`units_table.py`), `tbl_spec` by `decide +kernel`, reduced norm `nrdC` multiplicative (ring),
  inverse = ±conjugate. Axioms standard.
- `fibre_transitive` / `fibre_transitive_aut`: two ℚ̄-points with the same π-value differ by
  g₁ ≫ g₂ (R1hecke's twist α, rightMul u). Inputs: R2fp, R1hecke, TorsionStructure (torsor), units.
- `pi_invariant_twist`, `pi_invariant_rightMul`: these automorphisms preserve π on ℚ̄-points.
- `fibre_finite`: π-fibres on ℚ̄-points are finite (twistFibre_count).
- `CurveGaloisChart` (new glue Prop, curve theory with no moduli: proper smooth irreducible curve,
  finite ℚ̄-fibres, π-preserving automorphisms transitive on ℚ̄-fibres ⇒ finite Galois E with
  NormalizationModel).
- `heckeNormalizationIrr_of : CurveGaloisChart → TorsionStructure → HeckeNormalizationIrr`;
  `heckeNormalization_of : Y3Connected → CurveGaloisChart → TorsionStructure → HeckeNormalization`.

## Step 5. Lean, Part 4: HeckeBranch — VERIFIED (compiled, 0 errors, no sorryAx)

- New Props: `RamOfFibreCount` (algebra glue: e(Q)·#{ψ : B → ℚ̄ | ψ X = t} = [E:ℚ(X)] for Galois
  E, plus the ∞ chart and the junk prime 0), `NormalizationModelInf` (definition: chart at ∞),
  `CurveChartInf` (curve glue: chart at 𝔸¹ ⇒ chart at ∞), `HeckeFibreSizes` (moduli input: twist
  fibres ≤ M, = M off CM by ℤ[i], ℤ[ζ₃], ℤ[√−6], and M | 4F, 6F, 2F at those; Baba–Granath §3.1).
- Compiled: `chart_count`, `chart_count_inf` (ℚ̄-points of the charts = π-fibres), `fibre_ncard`
  (π-fibre = twist fibre), `ker_eval_rat`, `exists_ker_eval`, `finrank_le_twistFibre`,
  `heckeBranch_of : RamOfFibreCount → CurveChartInf → HeckeFibreSizes → TorsionStructure →
  (CM objects) → HeckeBranch`, `heckeBranch_of_R1R2fp` (CM objects from R1R2fp).

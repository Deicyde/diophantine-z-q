# pkg-I6 results log

Package I6 (h-trust steps B1, B2, C10, D1, D3, D4). Lean drafts: `scratch/pkg-I6/I6.lean`
(Mathlib-only import). Compile with `lake env lean scratch/pkg-I6/I6.lean`.

## Step 1 (Mathlib inventory, VERIFIED by grep of .lake/packages/mathlib, v4.35.0)
- Present: `Field.absoluteGaloisGroup` (+ `.map` for a field map, continuous),
  `continuousCohomology n (A : TopRep ℤ G)`, `ContinuousCohomology.map`,
  `ContinuousCohomology.tateShafarevich` (Sha.lean, 2026), `ContRepresentation.trivial`,
  `PadicAlgCl p` with spectral norm (`NormedField`), `IsAbelianGalois`, `IsArithFrobAt`,
  `differentIdeal` with `pow_sub_one_dvd_differentIdeal` (lower bound `P^{e-1} ∣ 𝔇`) and
  `dvd_differentIdeal_iff` (ramified ⇔ divides), `Algebra.IsCentral`, `IsSimpleRing`,
  `BrauerGroup` (CSA classes, definition only).
- Absent: Skolem–Noether, Hilbert symbol, Brauer base change / local invariants, Chebotarev,
  Brauer–Nesbitt, upper bound for the different, higher (lower/upper) ramification groups,
  Herbrand function, Artin conductor, local reciprocity map. (grep: no hits)
- Tau Ceti / other libraries: not available offline; statuses copied from
  docs/research/prereq-survey.md (not re-checked here).

## Step 2 (Part I drafts)
- `I6.lean` Part I compiles (`lake env lean`, no errors, no sorry) — VERIFIED:
  - `SkolemNoether` (Leaf I6.1) and `skolemNoether_aut` (B1 form; proved from the leaf).
  - `Z2 K` = trivial `TopRep ℤ G_K` on `ZMod 2`; `loc F n`, `locP p`, `locInf` via
    `ContinuousCohomology.map (Field.absoluteGaloisGroup.map (algebraMap ℚ F)) (𝟙 _) n`
    (same maps as Mathlib's `tateShafarevich`).
  - `BrauerHasse2` (I6.2a, Ш²(ℚ,ℤ/2)=0 over ℝ and all ℚ_p), `BrauerReciprocity2` (I6.2b,
    finite even support), `LocalH2Card` (I6.2c, local H² has 2 elements).
  - `LocalKroneckerWeber p` (I6.3) over `PadicAlgCl p`.
  - `ChebotarevExists` (I6.4) with Mathlib's `IsArithFrobAt ℤ σ Q`, `Algebra.IsUnramifiedAt`.
  - `BrauerNesbittChar0` (I6.5) for `Representation k G V`, semisimple `asModule`.

## Step 3 (Part II drafts: local fields)
- `I6.lean` compiles (VERIFIED, `lake env lean`): only warnings are `sorry` in two GLUE theorems
  (`artinConductor_le_of_upper`, `sq_principalUnits`) and an overlapping-instance lint.
- Definitions (Serre, Corps locaux), proved to be subgroups: `lowerRam A B i` (G_i:
  `σ b − b ∈ 𝔪_B^{i+1}` ∀ b), helper `map_mem_maximalIdeal_pow` (proved), `lowerRamR` (real index),
  `herbrandPhi` (interval integral of |G_t|/|G_0|), `upperRam` (G_{ψ(v)}, ψ via sInf),
  `unitFiltration`, `codimInv`, `artinConductor` (Serre VI §2, finsum).
- `lowerRam_tower` (subgroup rule for lower numbering) PROVED by `rfl`.
- Leaves: `DifferentBound` (I6.6, 𝔇 ∣ 𝔪^{e-1}(e)), `HilbertDifferentFormula` (I6.7),
  `HerbrandQuotient` (I6.8), `HerbrandTransitivity` (I6.9), `LocalReciprocityUpper` (I6.10:
  ∃ θ : K^× ↠ Gal, ker = norms, θ(π) = Frobenius on residue field, θ(U^n) = G^n).
- GLUE statements (sorry): `artinConductor_le_of_upper` (G^v trivial for v > U ⇒ f(V) ≤ dim V (1+U)),
  `sq_principalUnits` (2B = 𝔪^e, r > e ⇒ 1+𝔪^{r+e} ⊆ (1+𝔪^r)²).

## Step 4 (B2 glue proved; LocalReciprocityUpper sharpened)
- `eq_of_same_finite_support` PROVED (no sorry) from `BrauerHasse2`, `BrauerReciprocity2`,
  `LocalH2Card`: two classes of H²(G_ℚ, ℤ/2) locally nonzero at the same primes are equal.
  This is the Brauer step of B2 (N5 L683-692, classes [ε] and δχ). Helper
  `eq_of_ne_zero_of_card_two` proved. Compiles (VERIFIED).
- `LocalReciprocityUpper` now states θ(U^{⌈v⌉}) = G^v for all real v ≥ 0 (upper numbering
  theorem + Hasse–Arf); still a consequence of published theorems. Compiles (VERIFIED).
- Finding (argument, SPECULATIVE until reviewed): D3's use of norm functoriality of local
  reciprocity can be avoided. β⁴ = χ² on G_F and χ² is a Dirichlet character of odd conductor,
  hence unramified at 2, so β⁴ is trivial on the inertia of F; θ_F(U_F) = G_0 then gives
  (β∘θ_F)⁴ = 1 on U_F, and `sq_principalUnits` twice gives U^{3e+1} ⊆ (U^{e+1})⁴. Only
  `LocalReciprocityUpper` for F is needed.

## Step 5 (cochain-level Brauer leaves; alignment with other tasks)
- `lowerRam` now uses Mathlib's `AddSubgroup.inertia` of `𝔪_B^{i+1}` (same construction as
  glue-conductor's global `ramGroup`); `mem_lowerRam` is `Iff.rfl`.
- New: `IsCocycle2`, `IsCoboundary2` (continuous inhomogeneous cochains, ZMod 2 trivial action),
  `resC F ε`, leaves `BrauerHasse2C`, `BrauerReciprocity2C`, `LocalH2CardC` (via `H2TwoClasses`).
  Glue `cob_of_same_finite_support` PROVED (no sorry). Compiles (VERIFIED).
- `#print axioms` (VERIFIED): `eq_of_same_finite_support`, `cob_of_same_finite_support`,
  `skolemNoether_aut`, `lowerRam_tower`: [propext, Classical.choice, Quot.sound].
- `sq_principalUnits` (D3 glue) is proved by glue-conductor (`Dyadic.lean`,
  `exists_sq_eq_one_add`/`exists_fourth_root`, commit 2aeeb7f2); here statement only.
- Cross-check with hdec-faithful's Leaves.lean (origin/wip/hdec-faithful): it leaves
  `L15b_BrauerCohomology`, `L16_LocalCFT`, `L20_RamificationGroups` as `def … : Prop := sorry`
  ("missing"). This file states all three over Mathlib: L15b is bypassed by I6.2a-c (stated on
  H²(G_ℚ, ℤ/2) directly, both via `continuousCohomology` and on cochains); L16 by I6.3 + I6.10;
  L20 by I6.6-I6.9 with concrete definitions.

## Step 6 (non-vacuity of local hypotheses)
- `scratch/pkg-I6/Check.lean` compiles (VERIFIED): for `ℤ_[p]`, Mathlib infers
  `IsDiscreteValuationRing`, `IsAdicComplete (maximalIdeal _)`, `PerfectField (ResidueField _)`,
  `Finite (ResidueField _)`, `Module.Finite`, `Module.IsTorsionFree`, `Algebra.IsSeparable` on
  fraction rings. So the hypothesis lists of I6.6-I6.10 have models (the trivial extension);
  non-trivial extensions were not instantiated.

## Step 7 (deliverable)
- `docs/research/pkg-I6.md` written: leaf table I6.1-I6.10 with N5 lines, Lean names, library
  status; glue per step; findings (§3.4 D3 without norm functoriality, SPECULATIVE).

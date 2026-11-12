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

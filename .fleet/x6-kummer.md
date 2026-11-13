# x6-kummer (2026-11-13)

**Result: N2 `X6KummerFibre` is proved in Lean** (statement verbatim from fs5-nocm) from one new
explicit leaf and the existing curve glue:

    theorem X6Kummer.x6KummerFibre_of_conic (hM : MobiusGlue) (hL : X6ConicModel) : X6KummerFibre

- `X6ConicModel` (leaf, new): one witness of the repaired QM bundle has a Galois-equivariant
  bijection `X₆(ℚ̄) ≃ C(ℚ̄)`, `C : Y² + 3X² + 3Z² = 0`, with `π₆ = −16(X²+Z²)/(27Z²)` (Elkies'
  model `X₆ = X*(6)(√−t, √(3(t−1)))`, Kurihara's conic; locators UNVERIFIED; constants
  independently derived in rv-h-cm §2.3, checked on 24 CM rows by rv-nocm; conic_check.py).
- `MobiusGlue`: existing (qm-pin; mobius-glue reduced it to CurveRatFactor, CurveSurj, T5).
- Compiled on the way: residue field = fixed field of the point's Galois stabilizer
  (`galPt_eq_self_iff`, infinite Galois theory); N2 from the fibre form; transport between
  witnesses; the new glue `PairBaseChangeUnique` **proved** (pullback uniqueness + mul-rigidity's
  `rigidityHom`); fibre form from the conic form.
- N2's statement is true and needs no correction; but it is not pure glue: its constants are a
  literature fact about `X₆`, now isolated in one equation.

**N1b `CMConductorCoprime6`**: true; a consequence of published statements, not of Eichler's
theory alone. Eichler's local half (optimal ⇒ `p ∤ f` for `p | 6`) is proved in Lean for the
project's order (fs5-nocm `not_dvd_conductor_of_optimal`, re-compiled here). The other half
(`End_𝒪(A) = φ⁻¹(𝒪)`) is Shimura's description of CM points = fs5-nocm's `CMOptimalEmbedding`.
Recommend that leaf in place of N1b.

**Compiles** (VERIFIED): `scratch/x6-kummer/X6Kummer.lean` exit 0, 33 s, 8 `#print axioms` all
`[propext, Classical.choice, Quot.sound]`; `scratch/x6-kummer/N1b.lean` exit 0, standard axioms.

**Remains**: human check of `X6ConicModel`'s and `CMOptimalEmbedding`'s locators; mobius-glue's
`CurveRatFactor`, `CurveSurj`. Report: docs/research/x6-kummer.md.

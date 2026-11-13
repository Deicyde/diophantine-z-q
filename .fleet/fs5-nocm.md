# fs5-nocm (fleet summary)

**Result.** FS5 `FibreComTrivial` (NoCM on the fibre: `End_𝒪(P.A) = ℤ` over `J(u)`, `u ∉ 𝒞`) is
**proved in Lean**. The statement is verbatim, with `R1fpProps` read as after qm-pin's full repair.
`FS5NoCM.fibreComTrivialFull_of_leaves'` derives it from:

- leaves: the repaired QM bundle `R1R2fpFull`, `R5fpCount`, T27 (Yu), T6 (Mumford), and one
  **new leaf N1b** `CMConductorCoprime6`. N1b says a CM order `End_𝒪(A)` has conductor prime to 6
  (Eichler optimal embeddings, Vignéras; Jordan/González–Rotger; locators UNVERIFIED);
- glue: one **new glue Prop N2** `X6KummerFibre`. N2 is Elkies' Kummer model of `X₆ → P¹`: points
  over rational `j₀ ∉ {0, −16/27}` have residue field `ℚ(√−t₀, √3(t₀−1))`, and the fibre has four
  points;
- glue: mobius-glue's `MobiusGlue`. `fibreComTrivialFull_of_curves_leaves` in `FS5Curves.lean`
  replaces it by `CurveRatFactor`, `CurveSurj` and T5.

**How the proof goes.**

1. NoCM on the leaf's own witnesses (`fibreComTrivialOwn_of`):
   - the residue field is `ℚ(i)` (Elkies identities, compiled);
   - R5's degree and embedding clauses apply;
   - 2 is not inert in `ℚ(i)` (compiled);
   - so `#CM(R) = 2`, but the fibre gives four classes with CM by `R`.
2. Transfer to all triples by qm-pin's `pointwise_of_witness_mor` (`fibreComTrivialFull_of_own`).
3. N1a (`End_𝒪(A)` is `ℤ` or an order of an imaginary quadratic field) is **proved from T27 and T6**
   (`comIntOrQuadOrder_of_leaves`). It is not assumed:
   - case `End⁰ ≅ B`: the centre of `ℍ[ℚ,2,−3]` is `ℚ`, plus integrality;
   - CM case: a matrix commuting with a quaternion pair in `M₂(K)` is scalar, `ℚ(√d)` is a
     totally complex quadratic field, and the image of `End_𝒪(A)` has rank 2 in `𝒪_k`.

**What compiles (VERIFIED).**

- `scratch/fs5-nocm/FS5NoCM.lean` (1168 lines): exit 0, no `sorry`, 16 `#print axioms` lines, all
  `[propext, Classical.choice, Quot.sound]`.
- `scratch/fs5-nocm/FS5Curves.lean` (2456 lines; includes mobius-glue's file): exit 0, standard
  axioms.
- The copied statements (FS5, qm-pin's patched `R1fpProps`, the qm-pin and g0-fibresimple blocks)
  were checked verbatim by string comparison.

**What remains.**

- N2: the explicit Kummer model, plus its transport to an arbitrary bundle witness. The transport
  is argued through qm-pin's comparison, rigidity, and "residue field = fixed field of the
  stabilizer".
- A human check of N1b's literature.
- mobius-glue's curve facts.

Report: `docs/research/fs5-nocm.md`.

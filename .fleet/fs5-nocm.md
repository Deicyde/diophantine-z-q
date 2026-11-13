# fs5-nocm (fleet summary)

**Result.** FS5 `FibreComTrivial` (NoCM on the fibre: `End_𝒪(P.A) = ℤ` over `J(u)`, `u ∉ 𝒞`) is
**proved in Lean**. The statement is verbatim, with `R1fpProps` read as after qm-pin's full repair.
`FS5NoCM.fibreComTrivialFull_of_leaves''` derives it from:

- leaves: the repaired QM bundle `R1R2fpFull`, `R5fpCount`, T27 (Yu), T6 (Mumford), and **one new
  leaf N1b′** `CMOptimalEmbedding`. N1b′ is Shimura's description of CM points:
  `End_𝒪(A) ≅ φ⁻¹(𝒪)` for an embedding `φ : k → B` (Shimura 1967; Jordan 1981; González–Rotger
  2006; locators UNVERIFIED);
- glue: **one new glue Prop N2** `X6KummerFibre`. N2 is Elkies' Kummer model of `X₆ → P¹`: points
  over rational `j₀ ∉ {0, −16/27}` have residue field `ℚ(√−t₀, √3(t₀−1))`, and the fibre has four
  points. Its constants are consistent with González–Rotger on all 24 CM rows (rv-nocm script,
  re-run);
- glue: mobius-glue's `MobiusGlue`. `fibreComTrivialFull_of_curves_leaves'` in `FS5Curves.lean`
  replaces it by `CurveRatFactor`, `CurveSurj` and T5.

**Proved here (all compiled).**

1. NoCM on the leaf's own witnesses: the residue field is `ℚ(i)` (Elkies identities); R5's degree
   and embedding clauses; 2 is not inert in `ℚ(i)`; so `#CM(R) = 2`, but the fibre gives four
   classes with CM by `R`.
2. Transfer to all triples by qm-pin's `pointwise_of_witness_mor`.
3. N1a (`End_𝒪(A)` is `ℤ` or an order of an imaginary quadratic field), from T27 and T6:
   - case `End⁰ ≅ B`: the centre of `ℍ[ℚ,2,−3]` is `ℚ`;
   - CM case: a matrix commuting with a quaternion pair in `M₂(K)` is scalar, and `ℚ(√d)` is a
     totally complex quadratic number field;
   - the image of `End_𝒪(A)` is integral, of rank 2, hence of finite index in `𝒪_k`.
4. N1b (the CM conductor is prime to 6), from N1b′: Cauchy's theorem in `𝒪_k/R`, minimal
   polynomials, and `p² ∣ nrd ⇒ p ∣ coordinates` for `p = 2, 3` (`decide` modulo 4 and 9).

**Compiles (VERIFIED).**

- `scratch/fs5-nocm/FS5NoCM.lean` (1390 lines): exit 0, no `sorry`, 20 `#print axioms` lines, all
  `[propext, Classical.choice, Quot.sound]`.
- `FS5Curves.lean` (2684 lines; includes mobius-glue's file): exit 0, standard axioms.
- The copied statements were checked verbatim by string comparison.

**Remains.**

- N2: the explicit model of `X₆`, plus its transport to an arbitrary bundle witness (argued through
  qm-pin's comparison, rigidity, and "residue field = fixed field of the stabilizer").
- A human check of N1b′'s literature, including the `B^op` convention.
- mobius-glue's curve facts.

Report: `docs/research/fs5-nocm.md`. Final compile 06:25 PST (run1.txt, run2.txt in scratch/fs5-nocm/).

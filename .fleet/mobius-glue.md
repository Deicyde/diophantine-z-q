# mobius-glue (fleet summary)

**Result.** qm-pin's `MobiusGlue` (copied verbatim, with the qm-pin definitions it uses) is proved
in Lean from two named curve facts and the existing textbook leaf T5:
`mobiusGlue_of_curves : CurveRatFactor → CurveSurj → ObjBridge.TorsionStructure → MobiusGlue`
(`scratch/mobius-glue/MobiusGlue.lean`; 0 errors, 0 warnings; 16 `#print axioms`, all
`[propext, Classical.choice, Quot.sound]`). Downstream: `sameTripleMor_of_curves`,
`pointwise_of_witness_curves` (the transfer used by FibreSimple, ThetaPointOfFibre, ModularConstituent).
- `CurveRatFactor`: on a proper smooth curve over ℚ, a map to P¹ constant on the fibres of another
  map σ to P¹ is a rational function [F : G] of σ at ℚ̄-points (textbook curves; not in Mathlib).
- `CurveSurj`: a map to P¹ with finite ℚ̄-fibres from a proper smooth curve with a ℚ̄-point is onto
  P¹(ℚ̄) (Hartshorne II.6.8; not in Mathlib).

**Compiled glue.**
- Möbius step: an injective rational function on an algebraically closed field of char. 0 has
  degree ≤ 1 (Wronskian argument); with no finite pole and fixing 0 and c ≠ 0 it is the identity.
- Reduction bookkeeping: same fibres, CM values, surjectivity, injectivity of the factor.
- Finite twist classes: finitely many level structures per pair from T5 (kernel `Level3.torsor`);
  transport of level structures along QM isomorphisms.
- **Aut(𝒪) modulo inner automorphisms by units is finite, proved:**
  - extension of α ∈ Aut 𝒪 to Aut_ℚ(B); Skolem–Noether from the kernel's proof;
  - **N(𝒪)/ℚ^×𝒪^× = {1, i, j, ij}**, by descent on the reduced norm. The integer identity
    6x_l² = Σλ·coord(u e_k ū) comes from PARI; the checks mod 2 and mod 3 are done by `decide`.

**Remains.** The two curve facts. They are true (argued in docs/research/mobius-glue.md §3) and need
curve theory Mathlib lacks: degree of finite morphisms, P¹ points, image curves.
Report: docs/research/mobius-glue.md. Log: scratch/mobius-glue/log.md.

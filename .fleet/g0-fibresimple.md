# g0-fibresimple (fleet note)

**Result.** g0-split's piece 4, `HSyn.G0Split.FibreSimple`, is proved in Lean with its statement
unchanged. The inputs are four leaves and two glue Props.

- Leaves:
  - T27 (Yu, `QMDichotomyYu`) and T6 (Mumford §19 Thm 3, `HomFreeFinite`), both from
    `TextbookLeaves`.
  - New textbook leaf `MulIsogeny` (Mumford §4 / Milne Thm 8.2: `[n]` is an isogeny).
  - New textbook leaf `RigidityHom` (Mumford §4 Cor. 1: a morphism preserving `0` is a
    homomorphism).
- Glue:
  - FS1b′ `FiniteDescends`: `IsFinite` descends along `Spec L → Spec K`. Pure scheme theory;
    Mathlib lacks only the `IsAffineHom` fpqc descent.
  - FS5 `FibreComTrivial`: NoCM on the fibre, `End_𝒪(P.A) = ℤ` over `J(u)`.

Entry point: `G0FibreSimple.fibreSimple_of_leaves (t : TextbookLeaves) hMul hRig
(p : FibreSimplePieces)`.

**Proved glue.**

- `B6_isUnit`, and `qm_embeds_end0` (QM gives `ℍ[ℚ,2,-3] →ₐ End⁰`).
- From T6: the CM case gives a non-integral `𝒪`-centralizer.
- From T6 and `MulIsogeny`: `End⁰` a division ring ⇒ every nonzero endomorphism is an isogeny.
- From `RigidityHom`: invariance under isomorphism of `k`-schemes.
- Faithfulness of base change, from Mathlib's fpqc instance.
- Descent of "isogeny" from finiteness descent.

**Compiles.** `scratch/g0-fibresimple/FibreSimple.lean` (Split.lean verbatim + new section),
checked with `lake env lean`: exit 0, no `sorry`, axioms propext, Classical.choice, Quot.sound only
(VERIFIED).

**Finding (matters for the whole decomposition).** FibreSimple, and FS5, quantify over every
`(Y, Φ, π)` with `R1fpProps ∧ R2fpProps`. These clauses do not determine `Φ` on closed points.

- Proved in Lean: composing `Φ` with a natural point automorphism that permutes `π`-fibres and
  fixes the three CM fibres preserves both clause lists (`r1fpProps_twistBy`,
  `r2fpProps_twistBy`).
- So FibreSimple is equivalent to NoCM for the true `Y₃` together with an undecided arithmetic
  condition: no rational CM value has a `π`-fibre Galois-isomorphic to the fibre over some
  `J(u)`.
- FibreSimple is **not shown false**, but it is **not a consequence of the published leaves as
  stated**.
- Proposed repair (not applied; R1 belongs to another task): add a family clause to R1, "`Φ` is
  induced by an abelian scheme over `Y`" (fine moduli, WP12's "R1(b) in family form"). After it,
  FS5 reduces to NoCM.
- g0-split's pieces 9 and 10 quantify the same way; this was not checked.

**Remains.** FS1b′ (Mathlib-level fpqc descent). FS5: after the R1 repair it needs the Kummer model
of `X₆ → P¹`, González–Rotger (R5) and the count of rv-h-cm §7.2. Report:
docs/research/g0-fibresimple.md.

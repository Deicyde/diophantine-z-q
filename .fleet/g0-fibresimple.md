# g0-fibresimple (fleet note)

**Result.** g0-split's piece 4, `HSyn.G0Split.FibreSimple`, is proved in Lean with its statement
unchanged. The inputs are four leaves and two named glue Props:

- Leaves: T27 (Yu, `QMDichotomyYu`), T6 (Mumford §19 Thm 3, `HomFreeFinite`), and two new
  textbook leaves, `MulIsogeny` (Mumford §4 / Milne Thm 8.2: `[n]` is an isogeny) and
  `RigidityHom` (Mumford §4 Cor. 1: a morphism preserving `0` is a homomorphism).
- Glue: FS1 `EndDivisionDescent` (simplicity descends along a field extension) and FS5
  `FibreComTrivial` (NoCM on the fibre: `End_𝒪(P.A) = ℤ` over `J(u)`).

The entry point is `G0FibreSimple.fibreSimple_of_leaves (t : TextbookLeaves) (hMul) (hRig)
(p : FibreSimplePieces)`.

**Proved glue.**

- `B6_isUnit`: `B` is a division algebra.
- `qm_embeds_end0`: a QM structure gives `ℍ[ℚ,2,-3] →ₐ End⁰(A)`.
- `centralizerOfMatrixEnd0_of_homFree`: the CM case gives a non-integral `𝒪`-centralizer.
- `end0Division_of_homFree`: `End⁰` division ⇒ every nonzero endomorphism is an isogeny.
- `endDivisionOfSchemeIso_of_rigidity`: simplicity is invariant under scheme isomorphism.

**What compiles.** `scratch/g0-fibresimple/FibreSimple.lean` (Split.lean verbatim + new
section) compiles with `lake env lean`: exit 0, no `sorry`, axioms propext, Classical.choice,
Quot.sound only (VERIFIED).

**Finding (important for the decomposition).** FibreSimple, and FS5, quantify over every
`(Y, Φ, π)` that satisfies `R1fpProps ∧ R2fpProps`. These clauses do not determine `Φ` on closed
points. It is proved in Lean that composing `Φ` with any natural point automorphism `σ` that
permutes `π`-fibres and fixes the 3 CM fibres preserves both clause lists (`r1fpProps_twistBy`,
`r2fpProps_twistBy`).

So FibreSimple is equivalent to NoCM for the true `Y₃` plus an undecided arithmetic statement: no
rational CM value has a `π`-fibre Galois-isomorphic to the fibre over some `J(u)`. FibreSimple is
**not shown false**, but it is **not a consequence of the published leaves as stated**.

Proposed repair (not applied; it is another task's leaf): add a family clause to R1 ("`Φ` is
induced by an abelian scheme over `Y`"), as in WP12's "R1(b) in family form". Pieces 9 and 10 of
g0-split quantify the same way (not checked).

**Remains.** FS1 (fpqc descent bookkeeping for def-faltings' `baseChange`). FS5 needs the R1
repair, then the Kummer model of `X₆ → P¹`, González–Rotger and the count of rv-h-cm §7.2.
Report: docs/research/g0-fibresimple.md.

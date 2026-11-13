# ag-inputs (fleet note)

**Verdict.**
- pi0-x6's Galois-component argument for `π₀(X₆) = 1` is correct. The adversarial review found
  no gap in the deduction (VERIFIED as an argument; the deduction is compiled).
- Residue fields `ℚ(i)` over 0 and `ℚ(√−3)` over ∞ are also confirmed independently, by Shimura
  reciprocity and `X^D(ℝ) = ∅`.
- Correction: pi0-x6's "algebraic geometry" input (d) also needed a quaternion fact, finite
  `π₆`-fibres (`Aut(𝒪)/Inn(𝒪^×)` finite). The exact-CM clause (c), `R2X6CMExact`, remains a
  restatement of Baba–Granath (or c2 glue, not done).

**Main result (VERIFIED: compiled, standard axioms only, no sorry/axiom, no warnings).**
In `scratch/ag-inputs/AGInputs.lean`, all three fields of `AGInputs` are proved from standard
leaves, and the bundle clause `R1pi0Props` becomes glue:
- `AGInLA.r1R2fpRep_of_noPi0' : R1R2fpRepNoPi0 → R5fpCount → ConnectedGeomConnected →
  ComponentInfinite → ConstOrSurj → LeafSkolemNoether → AtkinLehnerFinite → R1R2fpRep`.
- `R1R2fpRep` is a verbatim copy of `LeafAdopt.R1R2fpRep`. `R1R2fpRepNoPi0` is the same bundle
  with `R1pi0Props` replaced by (c).

Proved glue:
- `descend_of_leaf`: pullback pasting, `ℚ̄ ↪ K̄`, surjective base change;
- finite fibres from R2's fibre clause (`qmIsoOfConj`, `fibres_finite`);
- `extAut`: `Aut(𝒪) → Aut_ℚ(B)`;
- `autModInnFinite_of`, from Skolem–Noether (proved by t-skolem-kw, same statement) and AL.

**Leaves that remain** (textbook, not in Mathlib v4.35; locators UNVERIFIED):
- AG-GC `ConnectedGeomConnected`: connected and proper over an algebraically closed `k` ⇒
  geometrically connected (EGA IV₂ 4.5).
- AG-CD1 `ComponentInfinite`: each component of `X_ℚ̄` has infinitely many `ℚ̄`-points.
- AG-CD2 `ConstOrSurj`: `π : C → P¹` is constant or surjective (Hartshorne II.6.8).
- AL `AtkinLehnerFinite`: `N(𝒪)/ℚ^×𝒪^×` finite (Vignéras; Voight).

**Open.**
- (c2): derive (c) from `QMDichotomyYu` and `HomFreeFinite`. A roadmap is in the report.
- A human check of the locators.

Report: `docs/research/ag-inputs.md`; log: `scratch/ag-inputs/log.md`.

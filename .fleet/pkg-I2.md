# pkg-I2 (reduction theory: A5, A6, A8, C6, C10, D2) — fleet report

**Main result.** Every I2 input used by Theorem 4.1 can be stated faithfully in Lean today over
genuine Mathlib v4.35 objects, which corrects wk-h §3.2 (I2: "no").
- Abelian varieties are proper, smooth, geometrically integral group objects of `Over (Spec K)`.
- Torsion points are `Spec K̄ ⟶ A` with Mathlib's group law.
- Inertia is `ValuationSubring.inertiaSubgroup`.
- Good reduction is an abelian scheme over the DVR, with base change via `Over.pullback … mapGrp`.

Tate modules are replaced by their finite levels. Néron-model statements are replaced by their
published Galois consequences (SGA 7 IX 3.5). Details: docs/research/pkg-I2.md; drafts:
scratch/pkg-I2/I2.lean.

**Leaves (11 `def … : Prop`, all compile; locators UNVERIFIED).**
- Purity of the branch locus (SGA 1 X 3.4 / Stacks 0BMB, ring form).
- Abhyankar for DVRs (SGA 1 X 3.6). The SGA 1 XIII 5.2 form is glue from purity + the DVR form
  (SPECULATIVE).
- Néron–Ogg–Shafarevich (Serre–Tate Thm 1).
- Serre–Tate Thm 2.
- Grothendieck monodromy (SGA 7 IX 3.6 + 3.5).
- Raynaud's criterion (SGA 7 IX 4.7 + 3.5).
- Néron mapping property for abelian schemes (BLR 1.2/8).
- Reduction bijective on prime-to-p torsion (Serre–Tate §1).
- Boundary with I3: Mumford §4 (`A[n] ≅ (ℤ/n)^{2g}`), §19 Thm 3 (rank of Hom), §19 Thm 4
  (charpoly independent of ℓ).

**Glue.**
- PROVED from the leaves (standard axioms only, `#print axioms`):
  - C6/A8: good reduction ⇒ inertia trivial on `A[ℓⁿ]`;
  - D2: Raynaud ⇒ an inertia element of p-power order fixes `A[ℓⁿ]`.
- STATED, body `sorry`, full outline: A6 (Lemma PR(ii)) by a new route. It uses Raynaud at `m = 3`,
  NOS, `A[3ⁿ]` and the division algebra `B ⊗ ℚ₃`. This drops SGA 7 IX 3.6, the toric-part/Néron
  argument (Morita) and Serre–Tate Thm 2 from A6 (SPECULATIVE, unreviewed). The core package
  becomes 6 leaves: purity, Abhyankar, NOS, Raynaud, NMP (abelian schemes), torsion reduction.
- Described: A5 (Prop. TS / Lemma NV; `𝕎(𝔽̄_p)` can replace the missing strict henselization),
  A8 (needs Weil restriction), C10 (needs Frobenius).

**Compiles.** `lake env lean scratch/pkg-I2/I2.lean`: no errors; one `sorry` (the A6 glue body).

**Biggest obstacle.** The glue, not the leaves.
- A5's glue sits on I1 (the cover `Y₃ → P¹_j`, Shimura reciprocity), which cannot be stated.
- Mathlib has no API for points of group schemes: finiteness of torsion, `T_ℓ` as a
  `ℤ_ℓ`-module, continuity of the Galois action, `End` as a ring, Frobenius, Weil restriction.
  Every glue proof beyond C6/D2 needs some of it.
- Proving the leaves themselves needs Néron models and SGA 7: years of work.
- Non-vacuity of `IsAbelianVariety` was not checked in Lean.

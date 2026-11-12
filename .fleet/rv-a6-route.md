# rv-a6-route — fleet report

**Verdict: SOUND AFTER REPAIRS.** pkg-I2's Raynaud route for A6 (Lemma PR(ii)) proves the lemma as
h-b1 states it and as h-trust uses it: good reduction of `A` and of every conjugate at every
finite `v ∤ 3`, including `v | 2`. It uses three leaves:

- I2-Ray (SGA 7 IX 4.7 with 3.5), at `m = ℓ = 3`;
- I2-NOS (Serre–Tate Thm 1, (c) ⇒ (a));
- I2-Tors (Mumford, `A[n] ≅ (ℤ/n)^{2g}`).

This drops SGA 7 IX 3.6, the toric-part argument and the general Néron mapping property, and
Serre–Tate Thm 2 from A6. Report: `docs/research/rv-a6-route.md`.

**Repairs (both fix wording; the route is unchanged):**

- **R1.** "Order `3^{4n}` with exponent `3ⁿ` forces `A[3ⁿ] ≅ Λ/3ⁿ`" is false.
  - Counterexample: `Λ/Π^{2n−1} ⊕ Λ/Π`, computed by Smith normal form.
  - At `n = 1`, `𝔽₉² ≅ (ℤ/3)⁴` as groups.
  - Fix: use the full group structure `(ℤ/3ⁿ)⁴` and `n = 2k ≥ 2`, with a short Nakayama proof
    (report §3).
- **R2.** "nrd is anisotropic mod 3" is false for the quaternary form: `(0,0,1,0)` is a zero.
  - Fix: `B ⊗ ℚ₃` is a division algebra, so `v_Π` is a valuation.
  - Equivalently, `c² ≡ 0 (mod 3^{2k})` implies `c ≡ 0 (mod 3ᵏ)`, now proved in Lean.

**Computations (VERIFIED, PARI):**

- `(2,−3)_p = −1` exactly at `p = 2, 3`.
- `Λ = ℤ⟨i,j⟩` has reduced discriminant 24, so `Λ ⊗ ℤ₃` is maximal.
- Exhaustive checks mod 9 and mod 81.
- Split contrast: `M₂(ℤ/9)` has a square-zero element not divisible by 3, so the division
  property is essential.

**What compiles (no sorry; axioms propext, Classical.choice, Quot.sound):**

- `scratch/rv-a6-route/A6.lean`: `RvA6.goodReduction_of_QM_rational3`, which has pkg-I2's A6
  statement. It is proved from `NeronOggShafarevich`, `RaynaudCriterion` and `TorsionStructure`
  (the I2 leaves, copied verbatim) plus one pure-algebra glue Prop, `QuatUnipotentTrivial`. That
  Prop concerns a commutative group with endomorphisms `I, J, S`, where `I² = 2`, `J² = −3`,
  `IJ = −JI`, `S` commutes with `I` and `J`, and `(S − 1)² = 0` on `G[3^{2k}] ≅ (ℤ/3^{2k})⁴`. It
  concludes that `S = 1` on `G[3ᵏ]`.
- `scratch/rv-a6-route/QuatVal.lean`: `RvA6.quat_sq_dvd`, the valuation step of that lemma for
  every `k`, in coordinates.

**What remains:** the rest of `QuatUnipotentTrivial`, steps 1-3 and 5 of report §3:

- `G[3^{2k}]` is free of rank one over `Λ/3^{2k}`;
- `S − 1` is right multiplication by some `c`.

This is elementary finite linear algebra, a good crowdsourcing item (a few hundred lines,
SPECULATIVE). Also open: the existence of a valuation ring `w ⊂ K̄` over a given `O` (standard
glue).

h-trust A6 is not edited. The integration task should replace its suppliers line with "Raynaud
(SGA 7 IX 4.7 + 3.5), Serre–Tate Thm 1, Mumford §4, `B ⊗ ℚ₃` division", keeping h-b1's
argument as a second route.

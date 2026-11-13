# leaf-qm-fp (report)

**Main result.** The opaque placeholders R01 (Shimura–Deligne), R02 (Baba–Granath) and R05
(González–Rotger) of the H decomposition now have concrete Lean statements in field-point form,
over the kernel's `PkgI3.AbVar` and Mathlib schemes. They are in
`scratch/leaf-qm-fp/QMLeaves.lean`, which compiles (`lake env lean`, about 19 s) with no `sorry`
and no `axiom`. Every `#print axioms` gives propext, Classical.choice, Quot.sound. The note is
`docs/research/leaf-qm-fp.md`.

**The leaves** (bundle `LeafQM.AV.QMLeaves`):
- `R1R2fp`, on one `Y₃` and one `X₆`:
  - `Y` proper and smooth of relative dimension 1 over ℚ, with `Y(K) ≃ M3 K` for every field
    `K ⊇ ℚ`, natural in `K`;
  - `Γ'` (Aut 𝒪-twists and `𝒪^×`) acts by automorphisms of `Y`;
  - `X₆` with `X(ℚ̄) ≃ {QM pairs}/≅`, Galois-equivariant, with `W` and the forgetful `Y → X`;
  - `π₆ : X → P¹` (by charts) whose fibres are the W-orbits, with CM values `0, ∞, −16/27`;
  - the three CM points exist.
- `R1rec`: Shimura reciprocity in unramified form (p ≥ 5).
- `R5fp`: González–Rotger Thm 5.12, giving the degree, and `k ⊆ ℚ(x)` when `D(R) ≠ 1`.
- `R5fpCount`: Prop. 5.6, `#CM(R) = 2^b h(R)`.

**Definitions built.**
- QM and level-3 structures; level-3 structures live on `K`-points, so base change needs no
  counting leaf.
- Objects, isomorphism classes, the Γ′-operations.
- Base change as a pullback-square relation.
- Fields of moduli.
- Morphisms to P¹ by charts (`ToP1`), with values at field points, naturality and composition.

**Glue proved from the leaves (compiled).**
- A7's statement (`conj_iso_of_rational`): conjugates of a fibre object with rational j are
  twist-equivalent, so the abelian surfaces are isomorphic over ℚ̄.
- h-b1 M9 on `X₆` (`cm_of_val`): the fibres over 0, ∞, −16/27 are CM points by ℤ[i], ℤ[ζ₃],
  ℤ[√−6]. This uses invariance of CM under isomorphism and twist.
- R2 on `Y₃` from R2 on `X₆` (`R1R2fp_Y`).
- For A3: the `𝒪^×` action laws, and the level-structure torsor (given nested ranges).

**Finding.** NoCM needs `k ⊆ ℚ(x)`, not only `[ℚ(x):ℚ]`. With the degree alone, disc −19 is not
excluded. So bp-qmmoduli's degree-only R5fp was too weak, and R5fp now carries the containment.

**Review.** An adversarial model review (not human) found no DEFECT. Its two RISKs:
- every leaf rests on bp-qmmoduli §2.2 (the polarization of `(A, ι)` exists and is unique;
  SPECULATIVE), since the objects omit λ;
- the leaves lacked a vacuity guard; non-emptiness clauses are now added.

Docstrings were repaired: the audit verdict on R1, λ in R1hecke, Baba–Granath §3.1 for the CM
clauses, `N* = 1`.

**What remains** (note §4): glue for A2, A3, A5 and A10 that Mathlib cannot yet support:
- degree theory of finite morphisms of curves;
- Galois/inertia theory of the function-field cover `ℚ(Y^{(1)})/ℚ(j)`;
- the Kummer model of `X₆ → P¹`, with the fibre field `ℚ(i)`;
- residue field of a point versus field of moduli;
- the 81 = 81 count from `TorsionStructure` for A3;
- A4 plumbing.

R1an (complex uniformization, for F1) and R3 (Lin–Yang) are out of scope. No leaf is proved.

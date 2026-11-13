# leaf-push2 (fleet summary)

**Result.** R18, R22 and R3 now have concrete Lean statements. So do T11 (two textbook leaves)
and T12 (a glue target, in the form G10 uses). R17's `LadicCond.CarayolR17'` is confirmed with no
change. With the earlier reports (leaf-qm-fp, leaf-modcurves, def-ladic-cond, def-faltings), 13 of
the 14 placeholders of `Leaves.lean` are now concrete. T10 is the one left.

**What compiles.** `scratch/leaf-push2/LeafPush2.lean` (imports `ZInQKernel.HDecomp.Objects`):
`lake env lean` gives exit 0, no errors, no warnings and no `sorry`; all 15 `#print axioms` lines
are standard. The file contents:
- def-faltings' `stableFaltingsHeight`, copied and rebased onto the kernel's `PkgI3.AbVar`;
- leaf-modcurves' `IsJacobian` and `IsBelyiFunction`.

The leaves:
- **`R18_Javanpeykar`.** `h_F^st(J) ≤ 13·10⁶ g d⁵` with `g = dim J`. A consequence, given H5.
- **`R22_Pazuki`.** The audit's upper half, over a new period-matrix predicate (`IsSiegel`,
  `IsPeriodMatrix`), which encodes every principal polarization with no polarization object, and
  over the theta constants `θ[a;b](0,Ω)`.
- **`R03_LinYang`** (over `ℂ`). A QM surface is either `≅ Jac(C)` with `C` on the Lin–Yang family at
  some `j ≠ 0`, or `≅ E₁ × E₂`. The statement is existential and polarization-free.

Proved along the way:
- `linYangTuple_onQMLocus`: Lin–Yang's `J`-tuple is hdec-elementary's Igusa–Clebsch locus, so the
  two conventions agree.
- `linYang_j_eq`, `R22_plus3`, `R18_real`, `exists_isComplexConj`.

For T11/T12, a new textbook leaf: `UniformizationExists` (AN3 for `AbVar`).

**Finding.** Mathlib v4.35 has pro-étale ℓ-adic cohomology (`Scheme.EllAdicCohomology`), but only
as an abelian group: no `ℤ_ℓ`-structure, no functoriality. So only a non-equivariant T10 is
statable (`T10_groupIso`); the Galois-equivariant form that is used is not.

**Polarization (rv-qm-polar).** R22 and R3 as stated do not change if a QM surface carries several
principal polarizations. What would change: a universal form of R3 ("every `C` with `Jac C ≅ A`"),
and the coordinate-linked form `j = π₆(x)`, which is not stated.

**Check.** One independent model review: no DEFECT. Two open RISKs:
- R22: Pazuki's Def. 2.6 coordinates are `θ[a;b](0,Ω)` (UNVERIFIED);
- R3: the tuple is checked only against the repository's own transcription.

**Remains.**
- R3 linked to the `X₆` coordinate.
- Equivariant T10.
- Proofs of the glue targets (T12 eigenspaces, Lefschetz form of R3).
- Folding into `Leaves.lean`.

Report: docs/research/leaf-push2.md.

(Written 2026-11-12, 20:00 PST, before the 22:30 deadline.)

# fold notes: hodge-lattice

Source: `scratch/hodge-lattice/HodgeLattice.lean` (1186 lines; imports `ZInQKernel.HDecomp.Faltings.Models`),
report `docs/research/hodge-lattice.md`. Fragment: `scratch/leaf-adopt3/fold/hodge-lattice.lean`
(1176 lines, `section HodgeLatticeSec ... end HodgeLatticeSec`; no `noncomputable section` needed,
the source marks its defs `noncomputable`). New declarations are all in `ZInQ.DefFaltings.HodgeLattice`.
Insert order: hodge-lattice first, then h5-neron. Neither fragment uses the other.

## The one `sorry` occurrence
It is in the module docstring ("No `sorry`, no `axiom`."), not in code. It is reworded in the fragment
("No unproved step, no `axiom` (in the source file).") so the fragment contains no `sorry` token.

## Changes from the source
- Dropped the `import` line and the 13 `#print axioms` lines (all listed `[propext, Classical.choice,
  Quot.sound]` per the report): `hodgeLattice_of_lattice`, `hodgeLatticeTheorem_of`,
  `hodgeLatticeTheorem_of_local`, `omegaLocal`, `hodgeLatticeTheorem_of_cotangentRank`,
  `hodgeLatticeTheorem_of_regular`, `hodgeLattice_lattice_of_regular`, `hodgeLatticeTheorem_of_abVar`,
  `originStalkIso_of`, `hodgeLatticeTheorem_of_varieties`, `genericFibreStalkIso`,
  `hodgeLatticeTheorem_of_abVarFacts`, `hodgeLatticeTheorem_of_tangent`.
- Deleted the 9 lines `open PkgI3 (AbVar)`. **Main difference between kernel and Leaves.lean.** The
  kernel's `ZInQ.DefFaltings` has no `AbVar`: `GroupModel` etc. are over `PkgI3.AbVar`. Leaves.lean's
  `DefFaltingsSec` has its own copy `ZInQ.DefFaltings.AbVar` (+ `.baseChange`, `.dim`), with the same
  fields and the same bodies as `PkgI3.AbVar` (checked), and `GroupModel`/`HodgeLatticeTheorem` are over
  that copy. Inside `namespace ZInQ.DefFaltings.HodgeLattice`, Lean prefers the namespace match, so the
  bare `AbVar` is `ZInQ.DefFaltings.AbVar` (checked in Lean 4.35 `ResolveName.lean`: the
  `resolveUsingNamespace` match beats the open declarations). Keeping the opens would also have
  worked; I deleted them to avoid confusion. **So every new Prop (`TangentDimAtOrigin`,
  `RegularAtOrigin`, `DimAtOrigin`, `DimBaseChange`, `OriginStalkIso`, ...) is now over
  `ZInQ.DefFaltings.AbVar`, not over `PkgI3.AbVar` as in the kernel-compiled file.**
- Nothing else changed: statements and proofs are verbatim.

## Kernel vs Leaves.lean check
I diffed `HodgeData.lean + IdealLines.lean + Models.lean + Height.lean + Leaves.lean` of
`ZInQKernel/HDecomp/Faltings/` against Leaves.lean lines 16714-18616, ignoring blank lines. The only
differences are:
1. the `AbVar` block above;
2. `_root_.PkgI3.AbVar.structMapOn` / `_root_.PkgI3.AbVar.origin` in the kernel vs
   `ZInQ.DefFaltings.AbVar.structMapOn` / `.origin` in Leaves.lean. Neither task uses them by name
   (dot notation follows the type);
3. two line-wrapping differences.

Every kernel declaration the task uses is therefore in Leaves.lean, with the same text. No kernel
declaration was copied in. No declaration duplicates a Leaves.lean name: nothing in
`ZInQ.DefFaltings.HodgeLattice` exists in Leaves.lean, `parts/`, or the other fold files.

## Bridges (already in the file; types exactly the Leaves.lean Prop)
`ZInQ.DefFaltings.HodgeLatticeTheorem` (Leaves.lean ~18078) is not a field of `ResearchLeaves` or
`TextbookLeaves`. It is a glue row (AN3, algebraic half) and appears in the H5 caveat. So no bundle field
changes. The reductions are:
- `ZInQ.DefFaltings.HodgeLattice.hodgeLatticeTheorem_of_tangent (h1 : TangentDimAtOrigin) (h3 : DimBaseChange) : HodgeLatticeTheorem`.
  This is the strongest form: two open Props.
- `tangentDimAtOrigin_of (h1 : RegularAtOrigin) (h2 : DimAtOrigin) : TangentDimAtOrigin`.
- `hodgeLatticeTheorem_of_abVarFacts (h1 : RegularAtOrigin) (h2 : DimAtOrigin) (h3 : DimBaseChange) : HodgeLatticeTheorem`.
- **The "four Props" form.** The bridges that take four Props are:
  - `hodgeLatticeTheorem_of_varieties (h0 : GenericFibreStalkIso) (h1 : RegularAtOrigin) (h2 : DimAtOrigin) (h3 : DimBaseChange) : HodgeLatticeTheorem`;
  - its sibling `hodgeLatticeTheorem_of_abVar`, with `h0 : OriginStalkIso`.

  The first of the four is proved in both cases: `genericFibreStalkIso : GenericFibreStalkIso`, and
  `originStalkIso_of genericFibreStalkIso : OriginStalkIso`. That leaves three
  (`_of_abVarFacts`), or two (`_of_tangent`).
- Intermediate forms (also proved):
  - `hodgeLatticeTheorem_of (OmegaFG) (CotangentRank) (OmegaSpans)`;
  - `_of_local (OmegaLocal) (CotangentRank)`, where `omegaLocal : OmegaLocal` is proved;
  - `_of_cotangentRank`;
  - `_of_regular (RegularOrigin) (DimOrigin)`.

## New leaf / glue Props (textbook facts about varieties over a field; STANDARD, locators UNVERIFIED)
- `TangentDimAtOrigin`: `∀ L [Field L] (B : AbVar L) (g : ℕ), B.dim = g → finrank_{κ(0)} (CotangentSpace 𝒪_{B,0}) = g`, with `0 = originPt B`.
- `RegularAtOrigin`: `∀ L [Field L] (B : AbVar L), IsRegularLocalRing 𝒪_{B,0}` (EGA IV 17.5.1).
- `DimAtOrigin`: `∀ L [Field L] (B : AbVar L) (g : ℕ), B.dim = g → ringKrullDim 𝒪_{B,0} = g` (Hartshorne I.1.8A).
- `DimBaseChange`: `∀ (K) [Field K] (A : AbVar K) (L) [Field L] [Algebra K L], (A.baseChange L).dim = A.dim` (EGA IV 4.1.4).

Here `AbVar` = `ZInQ.DefFaltings.AbVar` and `originPt` = `ZInQ.DefFaltings.HodgeLattice.originPt`
(new def). The blocker is the missing dimension theory of varieties in Mathlib.

## `DimBaseChange` vs g0-split's `DimBaseChange`
- hodge-lattice: `ZInQ.DefFaltings.HodgeLattice.DimBaseChange :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [Algebra K L], (A.baseChange L).dim = A.dim`.
  In the kernel it was over `PkgI3.AbVar`; in the fragment it is over `ZInQ.DefFaltings.AbVar`.
- g0-split: `HSyn.G0Split.DimBaseChange :=
  ∀ (K : Type) [Field K] (L : Type) [Field L] [Algebra K L] (A : ZInQ.DefFaltings.AbVar K), (A.baseChange L).dim = A.dim`
  (part_split.lean ~73; parts/70_g0.lean ~80).

**Same statement up to the order of the binders** (`A` before or after `L`). In the fragment both are
over the same `ZInQ.DefFaltings.AbVar`, `.baseChange` and `.dim`. They are not syntactically equal, so
one Prop serves both only through a trivial conversion. G0Split comes after this fragment, so the
conversion has to be placed after g0-split's definitions:
```lean
theorem G0Split.dimBaseChange_of_hodgeLattice (h : ZInQ.DefFaltings.HodgeLattice.DimBaseChange) :
    G0Split.DimBaseChange := fun K _ L _ _ A => h K A L
theorem G0Split.hodgeLattice_dimBaseChange_of (h : G0Split.DimBaseChange) :
    ZInQ.DefFaltings.HodgeLattice.DimBaseChange := fun K _ A L _ _ => h K L A
```
An alternative is to define g0's `DimBaseChange` as `ZInQ.DefFaltings.HodgeLattice.DimBaseChange`
and fix the single use in `model_dim` (`hDim L Qbar A` becomes `hDim L A Qbar`).

## Expected trouble spots
- Proofs that unfold `A.baseChange L` or use its group structure (`fst_genericFibre_unit`,
  `gen_genericFibreUnit`, `originStalkIso_of`, `tangentDim_of_abVar`) now run on the copy
  `ZInQ.DefFaltings.AbVar.baseChange`. Its body is textually identical to `PkgI3.AbVar.baseChange`, so
  they should go through.
- `PkgI3.AbVar` has an `IsCommMonObj` instance that the copy lacks. As far as I can see it is not used.
- `local notation "Pb"` (§10) is local to its namespace block. Nothing else named `Pb` exists in Leaves.lean.
- Deprecation warning for `TensorProduct.induction_on` (as in the source), plus linter warnings.
- Heartbeats: the source compiled with default options. No `set_option` is needed.

# curves-g results log

Base: 8ec80711 + merge of origin/wip/leaf-fold3 (f7951690). Fields: t33 (`LeafModCurves.JacobianExists ℚ`),
t34 (`LeafModCurves.DimJ1Genus`), t38 (`X1Belyi.CurveOfFunctionFieldQ`). Owner files (kernel modules):
`ZInQKernel/HDecomp/ModCurves/Defs.lean` (JacobianExists), `.../Leaves.lean` (DimJ1Genus), `.../X1Belyi.lean`
(CurveOfFunctionFieldQ). leaf-fold3's flat file `scratch/leaf-fold3/Leaves3.lean` has copies under `HDec.`.

## t38
- 18:20 `ZInQKernel/Contrib/CurvesG/RatPoint.lean`: `nonempty_ratPt_of_place` (proper integral ℚ-scheme +
  degree-1 place of its function field ⇒ ℚ-point, via Mathlib `UniversallyClosed.eq_valuativeCriterion`),
  new Prop `CurveOfFunctionFieldQNoPoint` (T38 minus the point clause), `curveOfFunctionFieldQ_of_noPoint :
  CurveOfFunctionFieldQNoPoint → X1Belyi.CurveOfFunctionFieldQ`. VERIFIED: `lake build
  ZInQKernel.Contrib.CurvesG.RatPoint` 27 s, 0 errors; `scratch/curves-g/AxiomsContrib.lean`: all four
  `#print axioms` read `[propext, Classical.choice, Quot.sound]` (axioms_contrib_out.txt).

## t34
- 18:40 `ZInQKernel/Contrib/CurvesG/GenusSplit.lean`: `fieldGenus F` (ℚ-dimension of the differentials of
  `Ω[F⁄ℚ]` regular at every valuation subring containing ℚ); leaves `DimJacobianEqGenus` (Milne: dim of a
  Jacobian = genus, for every curve over ℚ) and `GenusX1Field` (genus of `K_N` = `genus Γ₁(N)`);
  `dimJ1Genus_of_split : DimJacobianEqGenus → GenusX1Field → LeafModCurves.DimJ1Genus`. VERIFIED: lake build
  0 errors; `#print axioms` standard three (axioms_contrib_out.txt).
- Consumers of t34 in leaf-fold3's flat file (VERIFIED by grep of Leaves3.lean): only through
  `LeafModCurves.dim_J1_le` (`dim J ≤ N²`), at lines 16897, 33861, 34333, 71883 (javanpeykarJ1 and E2).
- 18:45 genus sanity: bp-modcurves' `genus_check.py` re-run (uv, sympy): 30/30 `ok` for N = 1..30
  (combinatorial genus from S, ST, T on SL₂(ℤ)/±Γ₁(N) vs closed forms). `genus_check_out.txt`. VERIFIED computed.

## t33
- `JacobianExists` read against `IsCurve`, `IsJacobian`, `PkgI3.AbVar` (Objects.lean:162): the Albanese form of
  Milne 1986 Thm 1.1 + Prop. 6.1 (UNVERIFIED numbers) with `P₀ ∈ X(K)`; AbVar allows dimension 0; uniqueness
  only among homomorphisms. Not stronger. No Mathlib/Tau Ceti route (no Picard functor). STANDARD.

## checks
- `scratch/curves-g/py/verbatim_check.py`: the code of 26 declarations (the three field Props and every
  definition they use: IsCurve, SpecQ, RatPt, IsJacobian, IsX1Model, IsJ1, fieldX1, xCoord, EjBar, Ej, Qj, Kbar,
  genus, belyiDeg, nu2, nu3, nuInf, pmSubgroup, ConstantFieldIsQ, HasRationalPlace, ratHom, X1RationalCusp,
  dim_J1_le) in the kernel owner files occurs verbatim in leaf-fold3's Leaves3.lean: ALL VERBATIM (docstrings of
  Ej and DimJ1Genus differ). VERIFIED.
- 18:21 first flat run failed at once: upstream `ZInQ.*` helper oleans (lean/) not built in this worktree;
  `lake build` of the 29 ZInQKernel imports of Leaves3.lean fixed it (9 s).
- 18:22 CurveSplit.lean drafted ((A), (B), (C) for T38NoPoint); compile after the flat run.
- 18:39 flat run 1 (Leaves3 + part with t38np): 17:51 wall, max RSS 14.9 GB; 4 errors, all in the final root
  `example (∀ r t l g, …)` (binder types not inferable); every curves-g theorem and `sixContactMin_of_openG`
  compiled, their `#print axioms` standard three. `open LeafModCurves X1Belyi` inside `HDec.CurvesG3` resolves to
  the HDec copies (Lean's "Ambiguous namespace" warning says so). Fixed the example with explicit binder types.
- 18:42 `CurveSplit.lean` built (26 s, 0 errors): `curveOfFunctionFieldQNoPoint_of_split`,
  `curveOfFunctionFieldQ_of_split`, standard axioms (axioms_contrib_out.txt). assemble.py now folds t38 as
  t38a/t38b/t38c.
- 18:58 flat run 2 (Leaves3 + part_g3 with t34a/t34b, t38a/t38b/t38c): EXIT 0, 0 errors, no sorry, 17:17 wall,
  max RSS 15.5 GB. 295 `#print axioms` all standard (5 line-wrapped, leaf-fold3's). `sixContactMin_of_openG`
  standard axioms. VERIFIED.
- diffcheck2: MOD-UNNOTED 0, NOTE-ONLY 0 (nothing vendored).

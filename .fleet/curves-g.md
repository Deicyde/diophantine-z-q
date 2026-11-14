# curves-g (group G of leaf-fold3: t33, t34, t38)

**Main result.** The rational-point clause of T38 (`X1Belyi.CurveOfFunctionFieldQ`) is proved: a proper integral
ℚ-scheme whose function field has a degree-1 place has a ℚ-point. The proof uses Mathlib's valuative criterion.
T38 is reduced to three textbook Props, and T34 (`LeafModCurves.DimJ1Genus`) to its two published halves. T33
(`JacobianExists ℚ`) was checked against the definitions: it is the published statement (Milne 1986, Thm 1.1 +
Prop. 6.1, numbers UNVERIFIED) and not stronger. Report: `docs/research/curves-g.md`; log: `scratch/curves-g/log.md`.

**Declarations proved** (new modules in `ZInQKernel/Contrib/CurvesG/`, namespace `ZInQ.Contrib.CurvesG`, over the
kernel owners' own definitions; all `[propext, Classical.choice, Quot.sound]`):
- `nonempty_ratPt_of_place`, `curveOfFunctionFieldQ_of_noPoint : CurveOfFunctionFieldQNoPoint →
  X1Belyi.CurveOfFunctionFieldQ` (RatPoint.lean)
- `curveOfFunctionFieldQNoPoint_of_split`, `curveOfFunctionFieldQ_of_split : NormalModelOfFunctionFieldQ →
  NormalCurveSmoothQ → GeomConnectedOfConstantFieldQ → X1Belyi.CurveOfFunctionFieldQ` (CurveSplit.lean)
- `dimJ1Genus_of_split : DimJacobianEqGenus → GenusX1Field → LeafModCurves.DimJ1Genus`, with `fieldGenus F` =
  the ℚ-dimension of the differentials in `Ω[F⁄ℚ]` that are regular at every place (GenusSplit.lean)

**What compiles.** The three modules build with `lake build` (0 errors). The single-file check
`scratch/curves-g/CurvesG3.lean` (built by `assemble.py`) is leaf-fold3's `Leaves3.lean` unchanged plus
`part_g3.lean`. `lake env lean` exits 0 in 17 min, with no sorry, max RSS 15.5 GB. All 295 `#print axioms` lines
give the standard three. It proves `HDec.HSyn.sixContactMin_of_openG : OpenResearchLeaves2 → OpenTextbookLeavesG →
OpenAddedLeaves3 → OpenGlue3 → ZInQ.SixContactMin`, which is leaf-fold3's bundle with t34 → t34a, t34b and
t38 → t38a, t38b, t38c (68 → 71 Props). `py/verbatim_check.py` confirms that the code of the field Props and of
the 23 definitions they use is identical in the kernel owners and in `Leaves3.lean`.

**What remains open** (not proved): `JacobianExists ℚ` (T33), `DimJacobianEqGenus`, `GenusX1Field` (from T34),
and (A) `NormalModelOfFunctionFieldQ`, (B) `NormalCurveSmoothQ`, (C) `GeomConnectedOfConstantFieldQ` (from T38).
Mathlib 4.35 has no Picard functor, normal schemes, regular ⇒ smooth, Stein factorization or Riemann–Hurwitz.

**Proposal (not applied).** Every consumer of t34 uses only `dim J₁(N) ≤ N²`. The field could therefore be
`DimJ1LeSq` (the conclusion of `LeafModCurves.dim_J1_le`); exact text in the report, §6.

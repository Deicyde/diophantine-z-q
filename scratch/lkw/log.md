# lkw results log

## Step 1 (2026-11-13 03:20 PST)
- VERIFIED (grep of tc-oct16/nov01/main): no local Kronecker–Weber and no norm group of ℚ_p(μ_m) in Tau Ceti.
- VERIFIED: PadicAlgCl p := AlgebraicClosure ℚ_[p] (Mathlib Padics/Complex.lean:54); TC's G_K = Gal(AlgebraicClosure K/K).
- Needed TC modules (all oct16, all in kw-rest.txt ⇒ vendored by tc-port): Local.Reciprocity, Local.ArtinMap,
  Local.Cyclotomic, Local.ExplicitCyclotomicSymbol.ArtinMap. Closure of the last at oct16: 559 modules (closure.py).
- Derivation written in docs/research/lkw.md (Lemmas A, B, C). Local existence not needed.

## Step 2 (03:20–03:30 PST)
- Merged wip/tc-port (local branch; no origin/wip/tc-port ref yet) at 312eaee4, then 395103a4 ("all 1118 vendored oct16 modules build").
  Copied tc-port's .lake build artifacts for ZInQKernel/Contrib/TauCeti (no Lean run); `lake build` of
  Local.ExplicitCyclotomicSymbol.ArtinMap + Local.Cyclotomic then: "Build completed successfully (4818 jobs)". VERIFIED.
- No Tau Ceti module vendored by lkw; wip/kw-new not needed (all needed modules exist at oct16).

## Step 3 (03:30–03:45 PST)
- ZInQKernel/Contrib/LocalKW/Basic.lean: compiles (lake build, no errors). VERIFIED.
- ZInQKernel/Contrib/LocalKW/LocalKW.lean: `theorem ZInQ.Contrib.localKroneckerWeber (p : ℕ) [Fact p.Prime] : PkgI6.LocalKroneckerWeber p`;
  `lake build ZInQKernel.Contrib.LocalKW.LocalKW`: Build completed successfully (9610 jobs). VERIFIED.
- scratch/lkw/Axioms.lean (#print axioms, output in scratch/lkw/axioms.out): every theorem depends only on
  [propext, Classical.choice, Quot.sound] (zpow_apply_eq_self: [propext, Quot.sound]). VERIFIED.
- Pitfalls met: `Field.absoluteGaloisGroup K` is a `def` (not reducible to `Gal(AlgebraicClosure K/K)`): products/sets must be
  formed in `Field.absoluteGaloisGroup` and elements re-typed with `let w' : Gal(..) := w`; `Nontrivial ℚ_[p]`, `IsGalois ℚ_[p] Ω`
  and `Algebra.IsSeparable ℚ_[p] L` time out in instance search with the TC imports: supplied by hand.

## Step 4: T30 (03:45–04:00 PST)
- ZInQKernel/Contrib/LocalKW/SqrtCrit.lean: verbatim copy of scratch/t30-adelic/SqrtCrit.lean (t30-adelic, 85ed47cb), namespace
  T30 → ZInQ.Contrib.LocalKW.SqrtCrit, trailing #print axioms dropped. It must not import Tau Ceti: with TC in scope,
  `Normal ℚ_[p] K` instance search times out at lines 282/283/316 (VERIFIED, first attempt).
- ZInQKernel/Contrib/LocalKW/T30.lean: `theorem ZInQ.Contrib.leafSqrtCrit : GlueDescent.B2Q.LeafSqrtCrit`
  (= leafSqrtCrit_of_t16a applied to localKroneckerWeber). `lake build ZInQKernel.Contrib.LocalKW.T30`: success (9616 jobs).
  #print axioms (scratch/lkw/AxiomsT30.lean): [propext, Classical.choice, Quot.sound]. VERIFIED.

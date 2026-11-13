# t-skolem-kw results log

## T13 Skolem–Noether — PROVED (VERIFIED, compiled)
- File: `scratch/t-skolem-kw/SkolemNoether.lean` (imports only Mathlib).
- Statements copied verbatim: `PkgI6.SkolemNoether` (as `TSkolemKW.SkolemNoether`),
  `HSyn.SkolemNoether` (as `HSynSkolemNoether`), `LeafSkolemNoether` (automorphism case).
- Theorems: `TSkolemKW.skolemNoether : SkolemNoether`, `hsynSkolemNoether`, `leafSkolemNoether`.
- `lake env lean` 2026-11-12 22:2x: no errors; `#print axioms`: propext, Classical.choice, Quot.sound.
- Auxiliary results proved: `isSimpleRing_tensor` (C central simple, B simple ⇒ C ⊗[K] B simple;
  no finiteness needed), `nonempty_linearEquiv_of_finrank_eq` (modules over a simple Artinian
  K-algebra with equal finite K-dimension are isomorphic).
- Mathlib v4.35.0 has no Skolem–Noether and no simplicity of tensor products (grep, VERIFIED).
  ATLAS (`~/aq/atlas-lean`, `MathlibExt.Algebra.Central.SkolemNoether.skolem_noether`) has the
  automorphism case only; not copied (own proof, general two-map form).

## T19 Brauer–Nesbitt (char 0) — PkgI6 form PROVED (VERIFIED, compiled)
- File: `scratch/t-skolem-kw/BrauerNesbitt.lean` (imports only Mathlib).
- Statement copied verbatim: `PkgI6.BrauerNesbittChar0` (= `GlueC10.BrauerNesbittChar0`).
- Theorem `TSkolemKW.brauerNesbittChar0 : BrauerNesbittChar0`; axioms propext, Classical.choice,
  Quot.sound.
- General form proved: `brauerNesbitt_module` — for any `k`-algebra `R` (char k = 0), finite-dim
  semisimple `R`-modules with equal traces `r ↦ tr_k(r|M)` are isomorphic.
- Auxiliary: `isNilpotent_of_trace_pow_eq_zero` (char 0: all `tr(f^j) = 0`, `j ≥ 1` ⇒ `f`
  nilpotent; not in Mathlib v4.35.0 by grep), `exists_injective_of_trace_eq`.
- No Brauer–Nesbitt in Mathlib v4.35.0, ATLAS, or (per prereq-survey) Tau Ceti.
- HSyn matrix form also PROVED: `HSynBrauerNesbitt` (verbatim `HSyn.BrauerNesbitt`),
  `TSkolemKW.hsynBrauerNesbitt`; axioms propext, Classical.choice, Quot.sound (compiled).
  Via `repOfGL`, Mathlib's `Representation.mapSubmodule` (invariant subspaces ≃o k[G]-submodules).

## T18 Frobenius density — HSyn form REDUCED to the finite form (VERIFIED, compiled)
- File: `scratch/t-skolem-kw/FrobeniusDense.lean` (imports only Mathlib).
- Verbatim: `HSyn.FrobeniusDense` with `HSyn.Qbar/GQ/LiesOver/IsArithFrob` (namespace `HS`);
  `PkgI6.ChebotarevExists` (namespace `C10`); GlueC10's `FrobDense`/`FrobLift`/`frobDense` copied
  verbatim from Leaves.lean lines 11328-11333, 11375-11630, 11746-11750 (compiles here).
- Theorem `TSkolemKW.HS.frobeniusDense_of_chebotarev : ChebotarevExists → FrobeniusDense`;
  axioms propext, Classical.choice, Quot.sound.
- New glue: `zbarLoc` (the localization of `\bar ℤ` at a prime is a `ValuationSubring` of
  `\bar ℚ`, Prüfer property via the DVR `(𝓞_E)_Q`, `exists_frac_or_inv`), an arithmetic
  Frobenius at `𝔓 ⊂ \bar ℤ` is `IsArithFrob` at `zbarLoc`, `LiesOver` holds, Krull step.
- So T18's two forms collapse to one leaf: `ChebotarevExists` (Chebotarev existence form).
- Full Chebotarev NOT proved (Mathlib v4.35.0 lacks Hecke/Artin L-functions of number fields
  and class field theory; Dirichlet's theorem for ℚ exists).

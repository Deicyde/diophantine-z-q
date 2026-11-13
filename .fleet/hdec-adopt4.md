# hdec-adopt4 (fleet summary)

**Result.** leaf-push2, bp-analytic and rv-qm-polar are in the built project, with statements
unchanged. There are 11 new modules (about 3,210 lines) under `ZInQKernel/HDecomp/`:
`LeafPush2/{R18,R22,R3,T,Bridge,UnifBridge}`, `Analytic/{Torus,QMLattice,Hom,Uniformization}` and
`QM/Polar`. rv-qm-polar's docstring repairs (Lemma P replaces "bp-qmmoduli §2.2 SPECULATIVE") are
applied to `QM/Structures.lean` and `QM/Leaves.lean`, docstrings only.

**What compiles (VERIFIED 23:13 PST).**
- `lake build ZInQKernel` exits 0.
- `scripts/print_axioms.lean` prints 399 entries (67 new), every one exactly
  `[propext, Classical.choice, Quot.sound]`.
- There is no `sorry` or `axiom`, and no line is longer than 100 characters.
- `same.py` matches the drafts: every kept declaration has the same whitespace-normalized text as
  in its draft. The only names missing are the verbatim copies replaced by imports:
  - leaf-push2's Part I (115 declarations) is the adopted `ZInQ.DefFaltings`;
  - curve definitions are `LeafModCurves`'s, the order `𝒪` and `QMStr` are `LeafQM`'s, and
    `IsComplexConj` is `PkgI4`'s;
  - bp-analytic's copy of `PkgI3.AbVar` and rv-qm-polar's `𝒪` are replaced the same way.

So R18, R22, R3, `UniformizationExists`, T11a/b, T12 and T10 are now stated over the project's
one stable Faltings height and its shared `PkgI3.AbVar`.

**New glue (no draft).**
- `Bridge`: `IsSiegel` is bp-analytic's `SiegelSpace 2`, and leaf-push2's `thetaConst` is
  pkg-I1's. For `Im τ > 0`, `Ω(τ)` is in `𝔥₂` and is a period matrix of the QM lattice, so R22's
  `Ω`-quantifier is non-empty on QM tori.
- `UnifBridge`: bp-analytic's `UniformizationLeafAll` gives leaf-push2's uniformizations at
  `σ = id`, for some `g`.

**What remains.**
- Identify the two uniformization leaves. This needs `g = dim A` and base change along `σ`.
- `scratch/h-decomposition/Leaves.lean` still lists R3, R18, R22, T11 and T12 as opaque.
- The adopted `R03_LinYang` docstring still says the polarization step is SPECULATIVE. It should
  cite Lemma P.
- Report: `docs/research/hdec-adopt4.md`. Log: `scratch/hdec-adopt4/log.md`.

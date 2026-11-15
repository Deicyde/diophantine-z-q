# gz-weil (fleet summary)

**Result.** On the route the proof uses (the curves `C_d : y² = x³ − d²x`), gz-hl3's composite leaves
`StrongWeilCurve` (Eichler–Shimura, rational Manin constant) and `IsogenyLattice` (Faltings, analytic form) are
gone, and no new leaf replaces them. Their only consumer, `GZHL3.ShimuraCMParamCd` (the analytic modular
parametrization of every `C_d`), is now a Lean theorem: `ZInQ.GZWeil.shimuraCMParamCd_proved`, with standard
axioms only. gz-hl3's `WeierstrassUniformization` is not needed on the `C_d` route either: a period lattice of
`C_d` is constructed (`exists_isPeriodLattice_cd`). So the `C_d` form of `hL3` follows from gz-hl3's three
Heegner-point leaves alone (`grossZagierHeegnerCd_of_threeLeaves`).

The proof has four steps, all in Lean:
- the twist from `C_d` to `C₁` (Gauss sum of `(·/d)`, Tau Ceti's intertwining lemma, scaling of lattices);
- the uniformization of x0-32's eta-quotient model of `X₀(32)`: surjectivity of ℘, order of vanishing in place of
  ODE uniqueness, identity theorem, and the lattices `((1±i)/2)L`;
- x0-32's eta identity `x' = 4πi f y` from Jacobi's `dλ/dt = πiλθ₄⁴` plus a product identity;
- Jacobi's formula itself, by the classical modular proof: the theta functions are permuted by `SL₂(ℤ)`, and
  symmetric functions of the three log-derivative identities are level-one cusp forms of weight 4 and 8, which
  vanish by Mathlib's dimension formula.

By-product: x0-32's leaf `X0.EtaModelDifferential` is a theorem.

**Count.** The `C_d` split of `hL3` now has three leaves, against five for gz-hl3's `C_d` split and six for its
general split:
- `HeegnerPointRationalCd` (composite);
- `GrossZagierFormulaCd` (printed, constant forgotten);
- `GrossConjugationCd` (printed).

That is one composite instead of gz-hl3's two or three. Against `hL3` itself the composite count is neutral (1 → 1);
making it negative needs `HeegnerPointRationalCd`, which was outside this task. The general (all-`E`) form of `hL3`
is unchanged.

**What compiles.**
- `ZInQKernel/Contrib/OneProof/GrossZagierHeegner/{Weil,WeilParam,WeilTheta,WeilJacobi,WeilLattice}.lean` (new
  files only); `lake build …WeilLattice` succeeds.
- `scratch/gz-weil/Check.lean`: 31 theorems, standard axioms.
- `MainEdit.lean`: `frozenTarget_gzweil_three` = `frozenTarget` with `hL3` replaced by the three leaves above, via
  gz-statements' `C_d` chain; standard axioms.
- `#discharges` is recorded. It shows no direct discharge of `hL3`, because `hL3` is stated for all `E`; the
  integrator must swap `hL3` for the `C_d` chain (report §5).

**What remains.**
- `HeegnerPointRationalCd` (and the two printed Gross–Zagier/Gross leaves, which are unread).
- Report: `docs/research/gz-weil.md`.

_Final commit 2026-11-15 05:50 PST; all Lean listed above compiled in this worktree (standard axioms only)._

# gz-weil (fleet summary)

**Result.** On the route the proof uses (the curves `C_d : y² = x³ − d²x`), gz-hl3's composite leaves
`StrongWeilCurve` (Eichler–Shimura, rational Manin constant) and `IsogenyLattice` (Faltings, analytic form) are
gone. Their only consumer, `GZHL3.ShimuraCMParamCd` (the analytic modular parametrization of every `C_d`), is now
a Lean theorem from one classical printed identity, Jacobi's `dλ/dt = πi λ θ₄⁴`
(`ZInQ.GZWeil.JacobiLambdaDeriv`, over Mathlib's `jacobiTheta₂`). The theorem is
`shimuraCMParamCd_of_jacobiLambdaDeriv`, with standard axioms only.

The proof has three steps, all compiled:
- the twist `Φ_d ⇐ Φ₁` (Gauss sum of `(·/d)`, Tau Ceti's intertwining lemma, scaling of lattices);
- the uniformization of x0-32's eta-quotient model of `X₀(32)`: surjectivity of ℘, order of vanishing in place
  of ODE uniqueness, identity theorem, and the lattices `((1±i)/2)L`;
- x0-32's eta identity `x' = 4πi f y` from Jacobi's formula plus a product identity.

**Count.** gz-hl3's `C_d` split goes from 2 composites (`ShimuraCMParamCd`, `HeegnerPointRationalCd`) to 1
(`HeegnerPointRationalCd`). Against `hL3` the composite count is now neutral (1 → 1), with four printed leaves:
uniformization, Jacobi, the Gross–Zagier formula and Gross's conjugation relation. The general (all-`E`) form of
`hL3` is unchanged.

**What compiles.**
- `ZInQKernel/Contrib/OneProof/GrossZagierHeegner/{Weil,WeilParam,WeilTheta}.lean` (new files only);
  `lake build …WeilTheta` succeeds.
- `scratch/gz-weil/Check.lean`: 21 theorems, standard axioms.
- `MainEdit.lean`: `frozenTarget_gzweil` = `frozenTarget` with `hL3` replaced by
  `WeierstrassUniformization`, `JacobiLambdaDeriv`, `HeegnerPointRationalCd`, `GrossZagierFormulaCd`,
  `GrossConjugationCd`, via gz-statements' `C_d` chain; standard axioms.
- `#discharges` is recorded. It shows no direct discharge of `hL3` (the leaves are `C_d`-restricted), so the
  integrator must swap `hL3` for the `C_d` chain (report §5).
- Numerics (exact `q`-series and floating point) confirm the eta identity to `q^113`, Jacobi's formula to
  `4·10⁻¹⁰` and the product identity.

**What remains.**
- `JacobiLambdaDeriv` is printed but unread (locators UNVERIFIED). It could be proved from the kernel's triple
  product (Jacobi's four-square identity) or from level-one modular forms; not attempted.
- `HeegnerPointRationalCd` is still a composite.
- Report: `docs/research/gz-weil.md`.

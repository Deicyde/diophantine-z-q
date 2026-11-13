# g9-abvarbc results log

## Step 1 (06:50): dimension
- `ZInQKernel/Contrib/AbVarBC/Dim.lean`: g0-dim's proofs (scratch/g0-dim/Dim.lean) moved to namespace
  `ZInQ.Contrib.AbVarBC`, over the kernel's `PkgI3.AbVar` (HDecomp/Objects.lean).
  `PkgI3.AbVar.dim_baseChange : (A.baseChange L).dim = A.dim`, `PkgI3.AbVar.dim_finite`.
  VERIFIED: `lake env lean` exit 0, no errors (2m05s).
- Finding (VERIFIED, read): `AbVarBaseChange`'s A is G9's copy `ZInQ.Contrib.G9.PkgI3.AbVar` (I3Layer.lean) and A' is
  G9's copy `ZInQ.Contrib.G9.PkgI4.I3.AbVar` (I4Layer.lean): transports from the kernel's `PkgI3.AbVar` needed.
- Finding (VERIFIED, read): the V_ℓ clause needs surjectivity of `A(K̄)[ℓⁿ] → A(L̄)[ℓⁿ]`, i.e. finiteness of
  `A[ℓⁿ]` (Mumford §4, UNVERIFIED locator); not in Mathlib. Available routes: leaf T26 `PkgI3.TateModuleFree` +
  kernel glue `PkgI3.Tate.map_bijective` (HDecomp/I3Linalg/TateBC.lean); or mul-rigidity's `MulIsogeny`.

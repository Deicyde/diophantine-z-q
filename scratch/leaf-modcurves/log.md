# leaf-modcurves results log

(Times PST by the host clock.)

- 16:45 `ModCurveLeaves.lean` §A-§F: genus of Γ₁(N) (copied from bp-modcurves Gamma1Genus, through
  `genus_Gamma1_le`); modular-form defs copied from Leaves.lean (PkgI4 §2) plus `coeffField f`;
  `Ej`, `fieldX1`, `Y1j`, `jMap` (copied from bp-modcurves); new `IsCurve`, `IsX1Model N X`
  (smooth proper geom. connected integral curve over ℚ with function field ≃+* K_N for some P of
  exact order N), `RatPt`; `IsJacobian` over the kernel's `PkgI3.AbVar` (imported from
  `ZInQKernel.HDecomp.Objects`), leaf `JacobianExists`, `IsJacobian.unique` (proved), `IsJ1 N J`;
  `homVAdd`, `endV : End⁰(A) →+ End_{ℚ_ℓ}(V_ℓ A)`, `eigenFun` (ι-eigenfunctionals), `dualAct`
  (φ ↦ φ ∘ ρ(σ)); leaf `R16_EichlerShimuraJ1'`. `lake env lean`: exit 0, no errors, no warnings. VERIFIED.

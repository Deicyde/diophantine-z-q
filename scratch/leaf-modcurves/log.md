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
- 16:47 `ModCurveLeaves.lean` §F-§H added: `homVAdd_apply`, `galRep_apply`, `endV_comm` (End⁰ commutes
  with G_ℚ on V_ℓ, from kernel `PkgI3.homT_galT`), `dualAct_mem` (G_ℚ preserves the ι-eigenfunctionals;
  proved, so R16 does not assume it), `frobOn`; R16 restated with `frobOn` (trace = ι(a_p), det = ι(χ(p))p);
  leaf `DimJ1Genus` (dim J₁(N) = genus formula of Γ₁(N)); glue `dim_J1_le` (dim J₁(N) ≤ N², proved from
  `genus_Gamma1_le`); `IsBelyiFunction` (function-field Belyi condition over k); glue target `BelyiX1`
  (j/1728 Belyi on K_N, [K_N:ℚ(j)] ≤ N²); `X1ModelExists` (glue target / leaf); bundle `ModCurveLeaves`;
  glue `exists_J1`, `exists_J1_dim_le`, `exists_J1_quotient` (proved). `lake env lean`: exit 0, no errors,
  no warnings; every `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}. VERIFIED.
- 16:52 Frobenius predicate switched to the kernel's `GlueC10.IsFrobAt` (import
  `ZInQKernel.HDecomp.C10.C10`; the predicate C10 consumes; equivalent to PkgI4.IsArithFrob at ℤ̄_𝔓).
  Added `dualAct_mul`, `dualAct_one`, `frobOn_mul`, `frobOn_one`, `rhoF` (Representation of G_ℚ on the dual
  of the ι-eigenfunctionals = the ι-component), `trace_rhoF`, `finrank_rhoF`, and the glue `rhoF_traces`
  (R16 ⇒ 2-dim ρ with tr ρ(g) = ι(a_p) at IsFrobAt g p, p ∉ S ⊇ primes of Nℓ: the shape of C10's `hρ₅`).
  `lake env lean`: exit 0, no errors, no warnings; all `#print axioms` ⊆ {propext, Classical.choice,
  Quot.sound}. VERIFIED.
- 16:55 Added `LiesOver`, `IsArithFrob` (copied from Leaves PkgI4), `zbar_mem` (ℤ̄ ⊆ every valuation subring
  of ℚ̄), `isFrobAt_of_isArithFrob` (PkgI4 arithmetic Frobenius at v over p ⇒ kernel `GlueC10.IsFrobAt` with
  𝔓 = 𝔪_v ∩ ℤ̄): so R16' (IsFrobAt form) implies its IsArithFrob form. `lake env lean`: exit 0, no
  warnings; standard axioms. VERIFIED.

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
- 16:58 Independent model review (read-only subagent) of ModCurveLeaves.lean: no leaf false, over-strong or
  vacuous; definitions at the right strength (IsX1Model incl. N = 1..4 and Shimura's field = K_N; IsJacobian
  genus 0; eigenFun dim 2 for all ℓ; frobOn = transpose; arithmetic Frobenius on covariant V_ℓ; a_p/ā_p
  absorbed by θ∘c; no Fricke clause; DimJ1Genus small N; IsBelyiFunction, BelyiX1, X1ModelExists true).
  One sourcing finding: the congruence relation (Shimura 1971 Thm 7.9) gives only an annihilating
  polynomial; the trace/det clauses must cite the printed characteristic polynomial (Diamond–Shurman
  Thm 9.5.4, Shimura 1971 Thm 7.11 / Ribet 1977, UNVERIFIED numbers). Applied to the R16 docstring and to
  docs/research/leaf-modcurves.md §3, §6. Recompiled: exit 0, no warnings, standard axioms. VERIFIED.
- 17:02 §I (G13) added: `homV`, glue target `VSurjOfSurjective` (surjective homomorphism ⇒ surjective on V_ℓ;
  standard via T8, not a leaf), `homV_galRep` (equivariance, from kernel `homT_galT`), `pullback`,
  `pullback_injective`, `pullback_dualAct`, and **`g13_constituent`** (proved from R16' + VSurjOfSurjective):
  for a newform f of level N, any J₁(N), ℓ, ι, a 2-dim G_ℚ-stable space W of functionals on V_ℓ(J₁(N))
  (dual of a 2-dim quotient of V_ℓ(J)⊗ℚ̄_ℓ) with Frobenius trace ι(a_p), det ι(χ(p))p at p ∤ Nℓ — R16's former
  placeholder text. `lake env lean`: exit 0, no warnings; standard axioms (incl. `g13_constituent`). VERIFIED.
- 17:08 §J (C9 bridge) added: `exists_preimage` (algebraic complex numbers lie in ιC(ℚ̄)), `embOf` (ιL ∘ ιC⁻¹
  on a number field K ⊆ ℂ, a ring hom), `embOf_spec`, and **`rhoF_attached`** (proved from R16'): for a newform
  f, J₁(N), ℓ, ιC, ιL: A_f and a 2-dim ρ = rhoF with, at every p ∤ Nℓ, α ∈ ℚ̄ with ιC α = a_p(f) and
  tr ρ(σ) = ιL α for every PkgI4.IsArithFrob σ — the trace clause of Leaves' `PkgI4.GaloisRep.AttachedTo`.
  `lake env lean`: exit 0, no warnings; standard axioms. VERIFIED.

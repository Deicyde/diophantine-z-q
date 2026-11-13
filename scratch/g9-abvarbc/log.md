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

## Steps 2-6 (07:00-08:10), all VERIFIED by `lake env lean` / `lake build` (0 errors)
- Points.lean: `bcPt` (from unram-tate), `extHom`, `epi_spec_map_field` (Spec of a field map is epi: flat +
  surjective + qc ⇒ EffectiveEpi, Mathlib Stacks 023Q), `extPt_injective`, `extPt_galAct`.
- Tate.lean: `ptBC`, `ptBC_injective`, `ptBC_galAct`, `tateBC`, `tateBC_injective`, `tateBC_galT`,
  `TorsionDescends`, `tateBC_bijective_of_torsionDescends`, `tateBC_bijective_of_tateModuleFree` (T26), `vBC`,
  `vBC_galRep`.
- G9Instance.lean: transports `ofG9`, `toI4`, `vOfG9`, `vToI4` (all `rfl`); `map_comm`;
  `abVarBaseChange_of_torsionDescends`, `abVarBaseChange_of_tateModuleFree`, `g9Glue_of_tateModuleFree`.
- Torsion.lean: `mem_range_of_isIntegral`, `exists_lift_of_isFinite`, `comp_natCast_hom`, `torsionDescends_of_isFinite`.
- Mul.lean: mul-rigidity's scratch Mul.lean, namespaces moved under ZInQ.Contrib.AbVarBC.
- G9Mul.lean: `AbVarBaseChangeK` (kernel-level, witness pinned to A.baseChange L), `abVarBaseChangeK_of_mulIsogeny`,
  `abVarBaseChange_of_{mulIsogeny,kerUnitOpen,mulEtale,cotangent}`, `g9Glue_of_{kerUnitOpen,cotangent}`.
- Finding: AbVarBaseChange is true and correctly stated (no statement change needed); outright proof needs
  `MulIsogeny` (equivalently mul-rigidity's two cotangent glue statements), which is the only missing input.

## Steps 7-12 (07:10-07:45), all VERIFIED (lake env lean / lake build, 0 errors, no sorry)
- Consumers.lean: `dimBaseChange : ZInQ.DefFaltings.HodgeLattice.DimBaseChange`; primed versions of
  `hodgeLatticeTheorem_of_{tangent,abVarFacts,varieties,abVar}`, `tangentDim_of_abVar`, `dimOrigin_of` without
  DimBaseChange; `bcT_bijective'` (e1-sub) without hdim; `dim_overPullback` (g4-weilres hdim; checked in
  scratch/g9-abvarbc/G4Check.lean against a verbatim copy of `bcAlong`).
- Tangent.lean: `ptRing` (points of affine opens = ring maps, local Λ), `ptRing_ext/ofRing/specMap_comp/comp`;
  dual-number points `ptR`, `specHom`; `AtOrigin`, `D`, `D_one`, `eq_of_D_eq`, `D_mul` (via K ⊕ K² points),
  `D_inv`, `D_zpow`, `comp_intCast_hom`, `eq_one_of_comp_intCast` (char 0, n ≠ 0).
- KerUnit.lean: `dualHom`, `derivation_eq_zero` (derivations at origin of A[n] vanish), `ker_le_sq_of_derivations`,
  `locallyOfFiniteType_kerN`, `ks_isOpenImmersion` (unit section of A[n] open immersion).
- Main.lean: `kerUnitOpen : MulRigidity.KerUnitOpen`, `mulIsogeny : G0FibreSimple.MulIsogeny`,
  `torsionDescends`, `tateBC_bijective`, `abVarBaseChangeK`, **`abVarBaseChange : G9Bridge.AbVarBaseChange`**,
  `g9Glue_of_r10Weights : R10Weights → G9Glue`.
- E1SubBC.lean: `bcPt_e1`, `bcPhi_eq_ptBC`, `bcT_eq_tateBC`, `bcT_bijective_charZero` (no T26, no hdim).
- Axioms: scratch/g9-abvarbc/axioms-output.txt, 41 theorems, all [propext, Classical.choice, Quot.sound].
- Merged origin/main (6c225515, STATUS.md only).
- diffcheck2: MOD-UNNOTED 0, NOTE-ONLY 0 (nothing vendored by this task).

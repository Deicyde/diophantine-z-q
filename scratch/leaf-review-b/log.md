# leaf-review-b results log

Task: statement review of leaf-fold3's groups B, C, D, E, G (41 fields of `OpenResearchLeaves2`,
`OpenTextbookLeaves3`, `OpenAddedLeaves3`). Base: 8ec80711 + `git merge origin/wip/leaf-fold3`
(f7951690) = 428c8d22.

## Setup

- `lake build ZInQKernel.Hypotheses.JHeight` (builds the upstream `lean/` helper oleans; the flat file
  failed with `unknown module prefix 'ZInQ'` before it): success, 9066 jobs. VERIFIED.
- Check: `scratch/leaf-review-b/run_check.sh` = `Leaves3.lean` + `PrintFields.lean.tail`
  (a metaprogram `#lrb_fields` printing every bundle field's type with full names and the body of
  its head definition), one `lake env lean` run. Outcome: see "Lean check" below.

## Definitions read (all in `scratch/leaf-fold3/Leaves3.lean`, line numbers of that file)

- `HDec.PkgI2` (l.1376-1611): `IsAbelianVariety`, `IsAbelianScheme` (proper, smooth, geometrically
  connected), `Pts`, `torsion`, `galAct` (`Spec σ ≫ x`), `IsInertia` (Mathlib `inertiaSubgroup`),
  `HasGoodReduction` (abelian scheme over `O` with generic fibre `≅ A` as group objects),
  `InertiaTrivialOn`, `UnipSq` (`(σ-1)²x = 0`), `baseChange`, `toW`, `IsReductionOf`.
- `HDec.PkgI3` (l.2481-2938): `Tate.T` (sequences, `ℤ_ℓ`-module), `AbVar`, `dim`
  (= `topologicalKrullDim`), `Hom` (group-scheme homs), `End`, `End0 = ℚ ⊗ End`, `IsIsogenyMor`
  (finite + surjective), `Pt`, `galAct`, `T`, `V`, `galT`, `homT`, `galRep`, `tateHomZl`,
  `IsGalEquivariant`.
- `HDec.PkgI4.I3` (l.3687-3994) is `HDec.PkgI3` verbatim up to the namespace: VERIFIED by
  `diff` after `s/PkgI4.I3/PkgI3/` (empty diff).
- `HDec.PkgI4` (l.3996-4787): `GaloisRep`, `GaloisChar`, `IsIrreducible` (Burnside form),
  `IsSemisimple`, `decomp`, `restrictLocal`, `cpAct`, `cyc`, `htSpace`
  (`φ(ρ(σ)v) = χ(σ)^i σ(φ v)`), `htMult w = dim_ℚp H_{-w} / [E:ℚp]` (cyclotomic weight `−1`;
  checked by hand on `ℚ_p(1)`: weight `−1`; on `V_ℓ(E)`: weights `{0,−1}`), `LocalHasHTWeights`,
  `HasHTWeightsAtSelf`, `BdR`, `bdrAct`, `ddrSpace`, `IsDeRham`, `LocalIsDeRham`,
  `ddrSpaceOver`, `IsDeRhamOver`, `htSpaceOver`, `htMultOver`, `CF`, `coeff`, `HasNebentypus`,
  `IsNormalizedEigenform`, `AttachedTo`, `AttachedUpToTwist`, `PanFor`, `ContRep`.
- Mathlib: `ℍ[R,a,b] = QuaternionAlgebra R a 0 b` (`i² = a`, `j² = b`); `IsSemisimpleRepresentation =
  ComplementedLattice (Subrepresentation ρ)`. VERIFIED (read in `.lake/packages/mathlib`).
- `HDec.ZInQ.DefFaltings` (l.17156-19058) and its copy `HDec.ZInQ.LeafPush2` (l.19272-20900):
  `HermitianLattice.arakelovDegree` (`log #(M/𝓞s) − Σ_σ log ‖s‖_σ`), `torusMetricSq = |c|² covol`,
  `HodgeData.modelHeight = deg / [K:ℚ]`, `GroupModel` (smooth separated qc group scheme over `𝓞_L`
  with generic fibre `≅ A_L` as groups), `omega`, `detLattice`, `IsAnalyticUniformization`,
  `MetrizedModel`, `stableFaltingsHeight = ⨅ L g M, modelHeight` (EReal), `IsNeronModel`.
  The two copies differ only in the namespace, two `_root_` lemmas not re-declared, and the
  `AbVar` (DefFaltings has its own 5-field copy; LeafPush2 uses `PkgI3.AbVar`): VERIFIED by `diff`.
- `HDec.WeilPairing` (l.49327-49750): `tors`, `Mu`, `Pairing`, `IsPerfect`, `IsAlternating`,
  `IsGalEquivariant`, `WeilDual` (perfect, Galois, compatible `e_{mn}(x,y)=e_n(mx,y)`, `dualEnd`),
  `IsDualHom`, `weil`, `IsSymmetric`, `SymmIsogeny`, `IsQuasiInverse`.
- `HDec.T10Etale` (l.27375-27905): `ℤ_ℓ`-module on `EllAdicCohomology` via multiplication on the
  coefficient sheaf, `transport` (= `e_*`), `galH σ = transport (1 × Spec σ⁻¹)`.
  Direction check (by hand, SPECULATIVE): `σ·P̃ = s_σ ∘ P̃ ∘ Spec σ` for `s_σ = 1 × Spec σ⁻¹`, so
  `s_σ^*` ↔ `f ↦ f ∘ galT σ` and `(s_σ)_* = s_{σ⁻¹}^*` ↔ `f ↦ f ∘ galT σ⁻¹`, the contragredient
  action in `T10_TateDuality`; both sides are left actions.
- `HDec.LeafModCurves` (l.16137-16900): `genus Γ = 1 + μ/12 − ν₂/4 − ν₃/3 − ν∞/2` on
  `SL₂(ℤ)/±Γ`, `Ej`, `fieldX1 P = ℚ(j)(x(P))`, `IsCurve`, `IsX1Model`, `IsJacobian`, `IsJ1`.
- `HDec.X1Belyi` (l.30940-31030): `ConstantFieldIsQ`, `HasRationalPlace`.
- `HDec.FrobPiecesNeron` (l.110250-110300), `HDec.HeckeRest` (l.98660-98730),
  `HDec.ZInQ.H5Neron` (l.30080-30160), `HDec.HomUnify` (l.83800-83845).

## Verdicts (41 fields; reasons in docs/research/leaf-review-b.md)

| field | verdict |
|---|---|
| t5 | CONSEQUENCE |
| t6 | CONSEQUENCE |
| t7 | CONSEQUENCE |
| t8 | CONSEQUENCE |
| t9 | CONSEQUENCE |
| t10 | CONSEQUENCE |
| homLatticeCorr | CONSEQUENCE |
| t11b | PUBLISHED-FORM |
| t26 | CONSEQUENCE |
| t27 | CONSEQUENCE |
| t35 | CONSEQUENCE |
| t09SymmIsogenyExists | CONSEQUENCE |
| isogenyQuasiInverse | CONSEQUENCE |
| divisiblePoints | CONSEQUENCE |
| serreRigidity3 | PUBLISHED-FORM |
| t4 | CONSEQUENCE |
| r6 | CONSEQUENCE |
| r7a | PUBLISHED-FORM |
| r7b | CONSEQUENCE |
| r8 | CONSEQUENCE |
| t3 | CONSEQUENCE |
| t41 | PUBLISHED-FORM |
| properSmoothGenConnected | CONSEQUENCE |
| r9a | PUBLISHED-FORM |
| r9b | PUBLISHED-FORM |
| r18 | CONSEQUENCE |
| r19 | PUBLISHED-FORM |
| r20 | CONSEQUENCE |
| r21 | CONSEQUENCE |
| r22 | CONSEQUENCE |
| h5fin | CONSEQUENCE |
| r10 | CONSEQUENCE |
| r11r12 | CONSEQUENCE |
| r13 | CONSEQUENCE |
| t23 | CONSEQUENCE |
| senTwist | CONSEQUENCE |
| finiteImageHT | CONSEQUENCE |
| t33 | PUBLISHED-FORM |
| t34 | CONSEQUENCE |
| t38 | CONSEQUENCE |
| t40 | CONSEQUENCE |

No STRONGER-THAN-SOURCE, no NOT-A-PUBLISHED-STATEMENT. Remarks (not statement errors) are in the
report §3.

## Lean check
`scratch/leaf-review-b/run_check.sh` (2026-11-13, ~18:21-18:38 PST): `lake env lean` on
`Leaves3.lean` + `PrintFields.lean.tail` **exit 0, 0 errors**; 283 `#print axioms` reports of the
flat file read `[propext, Classical.choice, Quot.sound]`. `#lrb_fields` printed 62 fields
(20 + 26 + 16) with full names and head-definition bodies. The 41 reviewed fields resolve to exactly
the definitions named in the report (`HDec.PkgI2.*`, `HDec.PkgI3.*`, `HDec.LeafPush.T09_WeilPairing`,
`HDec.T10Etale.T10_TateDuality`, `HDec.HomUnify.HomLatticeCorr`, `HDec.ZInQ.LeafPush2.*`,
`HDec.WeilPairing.*`, `HDec.HeckeRest.SerreRigidity3`, `HDec.ZInQ.H5Neron.NeronModelExists`,
`HDec.FrobPiecesNeron.ProperSmoothGenConnected`, `HDec.ZInQ.DefFaltings.*`, `HDec.PkgI4.*`,
`HDec.G0Galois.{SenTwist,FiniteImageHT}`, `HDec.LeafModCurves.{JacobianExists ℚ,DimJ1Genus}`,
`HDec.X1Belyi.{CurveOfFunctionFieldQ,X1RationalCusp}`). VERIFIED. Spot-checked bodies
(`DivisiblePoints`, `R21_Bost`) equal the source text read. Raw output (/tmp, host paths) not committed.

# r16-split results log

Base 24f97774 (wip/w72). Target: `LeafModCurves.R16_EichlerShimuraJ1'` (ZInQKernel/HDecomp/ModCurves/Leaves.lean:179),
bundle field `HDec.HSyn.OpenResearchLeaves20.r16`.

## Setup
- Build tree copied from ~/dzq-wt/p1-quot (same commit 24f97774, TailZ29 built): `.lake/build`, `lean/.lake/build`. VERIFIED
  (`scratch/r16-split/Test0.lean` loads `ZInQKernel.HDecomp.ModCurves.Leaves` in ~1 min).

## Findings (reading)
- `ZInQKernel/Contrib/HeckeAll/` is about `L(C_d, s)` (Hecke characters of ℚ(i)), not Hecke operators on `X₁(N)`: no
  `T_p`, `⟨d⟩` on modular curves or Jacobians anywhere in the tree (VERIFIED by reading hecke-all.md and the file list).
- `X₁(N)` is defined only through its function field `K_N = ℚ(j)(x(P))` (`IsX1Model`, Defs.lean §D); `J₁(N)` only through the
  Albanese property (`IsJ1`). `f : CF N 2` is Mathlib's analytic cusp form. No object links the two (no `X₁(N)(ℂ) ≅ Γ₁(N)\ℍ*`,
  no `q`-expansion of differentials). VERIFIED (reading Defs.lean).
- Open bundle leaves that bear on r16: `charPolyIndepOfEllAlgClosed` (Mumford §19 Thm 4, alg. closed `k`; kernel
  `ZInQ.Contrib.AVB1.charPolyIndepOfEll_of_algClosed` gives `PkgI3.CharPolyIndepOfEll`), `mumfordTorsionAlgClosed` (T5;
  kernel LF4T5 gives `PkgI3.TateModuleFree`). VERIFIED (OPEN.md, grep).

## Lean results (all `lake env lean scratch/r16-split/Split.lean`, standard axioms printed)
- `R16Split.sum_finrank_jointEig`: for a finite-dim. `ℚ`-algebra field `F` acting on a finite-dim. `Ω`-space `W`
  (`Ω` alg. closed, char 0) by a ring hom, `Σ_{ι : F →ₐ[ℚ] Ω} dim (joint ι-eigenspace) = dim W`. VERIFIED (compiled).
- `R16Split.trace_eq_sum_jointEig`, `R16Split.weights_eq_of_rational` (trace form nondegenerate + Dedekind). VERIFIED.
- `R16Split.trace_precompL` (trace of `φ ↦ φ ∘ T` on `Hom_k(V, Ω)` is `trace T`). VERIFIED. (A `show` on the
  precomposition goal timed out at whnf; fixed with an explicit `precompL_apply` rewrite.)
- `R16Split.endV_mul`, `endV_one`, `rhoV` (`End⁰(A) → End(V_ℓ A)` is a ring hom). VERIFIED.
- `R16Split.dim_eq_of_rank_two` (TateModuleFree at ℓ = 2): rank-two clause ⇒ `dim A = [F:ℚ]`. VERIFIED.
- `R16Split.rank_two_of_dim` (TateModuleFree + CharPolyIndepOfEll): `dim A = [F:ℚ]` ⇒ rank-two clause. VERIFIED.
- `R16Split.r16_of_coreX : R16CoreX → TateModuleFree → R16_EichlerShimuraJ1'`. VERIFIED, axioms standard.
- `R16Split.r16_of_coreY : R16CoreY → TateModuleFree → CharPolyIndepOfEll → R16_EichlerShimuraJ1'`. VERIFIED.
- `coreX_of_r16`, `coreY_of_r16` (the cores are consequences of r16). VERIFIED.
- `ZInQKernel/Contrib/OneProof/R16Split.lean` (same content + `r16_of_printed` over the bundle leaves
  `mumfordTorsionAlgClosed`, `charPolyIndepOfEllAlgClosed`): `lake build +ZInQKernel.Contrib.OneProof.R16Split`
  succeeded (9122 jobs, 31 s). VERIFIED.
- autofold `--dry-run` on `scratch/r16-split/autofold.json`: exit 0, "strict count: 47/11 on 58 -> 47/11 on 58;
  strictest 46/12 -> 46/12"; output saved as `scratch/r16-split/FoldDryRun.lean`. VERIFIED (python; compile pending).

## #discharges
- `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges` (partial rebuild of the copied tree): success,
  12982 jobs, `frozenTarget` standard axioms. VERIFIED.
- `lake env lean scratch/r16-split/Discharges.lean` (full output `Discharges-output.txt`). VERIFIED:
```
DISCHARGES [OpenResearchLeaves20.r16] by R16Split.r16_of_coreX
  still assumes: [R16Split.R16CoreX, PkgI3.TateModuleFree]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves20.r16] by R16Split.r16_of_coreY
  still assumes: [R16Split.R16CoreY, PkgI3.TateModuleFree, PkgI3.CharPolyIndepOfEll]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves20.r16] by R16Split.r16_of_printed
  still assumes: [R16Split.R16CoreY, AvSplit.MumfordTorsionAlgClosed, ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 65 open hypotheses, 1310 theorems checked, 8 discharge one
```
- `lake env lean scratch/r16-split/FoldDryRun.lean` (autofold --dry-run output, line 1 stripped):
  `'HDec.HSyn.sixContactMin_of_open28' depends on axioms: [propext, Classical.choice, Quot.sound]`. VERIFIED.

# hcm-g1 log

Target: `T5Glue.ShimuraMainCM` (hCM of `ZInQ.OneProof.frozenTarget`, RingClassLattice.lean:911), g = 1 route.

## 2026-11-15
- Dev compiles: `scratch/hcm-g1/chk.sh` against hcm-printed's build tree (read only).
- `scratch/hcm-g1/G1.lean` (imports only `ZInQKernel.Contrib.OneProof.RingClassLattice`): copied from
  hcm-printed (namespace HcmG1): wc, wPtW, wPt, ParamProps, mapPt (+ some/injective/surjective), map_wc, LinSec
  (`lin`), helpers, leaves `WeierstrassUniformization` (gz-weil verbatim), `WeierstrassParam` (hcm-printed verbatim).
- New: `IsAnalyticIso L W ξ` (ξ : ℂ →+ W(ℂ), kernel L, surjective, coordinates holomorphic on ℂ∖L);
  leaf `ShimuraThm54` (Shimura 1971 Thm 5.4 over Mathlib's `WeierstrassCurve ℂ` + `IsElliptic`, ArtinCond,
  sInvLat, latHat; ∀ lattice 𝔞 of K via ∃ PeriodPair).
- VERIFIED (compiled, 7 s): `HcmG1.shimuraMainCM_of_g1 : ShimuraThm54 → WeierstrassUniformization →
  WeierstrassParam → T5Glue.ShimuraMainCM`, axioms [propext, Classical.choice, Quot.sound].
  No MainTheoremCMArith, WeierstrassAbVar, HomLatticeCorr, AbVar layer, adelic dictionary or artinCondC needed
  (the leaf is stated in T5Glue's adelic language).
- VERIFIED (computed, scratch/hcm-g1/frob_check.py, output frob_check_output.txt): K = Q(√−23), H = K(j(O_K)),
  p0 = (2, (1+√−23)/2), PARI idealfrobenius (checked arithmetic: Frob(b) ≡ b² mod P on Z_L): Frob_{p0}(j(O_K)) =
  j(p0^{-1}) = j((−1+i√23)/4) to 1e−61; differs from j(p0) by 3528. Confirms ShimuraMainCM's direction
  (Tau Ceti arithmetic Artin map ↔ s⁻¹𝔞) in this instance.
- VERIFIED (read): Tau Ceti `globalArtinMap_isArithFrobAt` (LocalArtin/Frobenius.lean:154): prime idele class ↦
  arithmetic Frobenius.
- Contrib file `ZInQKernel/Contrib/OneProof/ShimuraMainCMG1.lean` (imports only RingClassLattice) = G1.lean.
  Build tree: copied hcm-printed's .lake/build and lean/.lake/build (same base commit 150551820).
- VERIFIED: `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges
  +ZInQKernel.Contrib.OneProof.ShimuraMainCMG1`: Build completed successfully (12995 jobs) (build1.txt).
- VERIFIED: #discharges (Discharges.lean): DISCHARGES [hCM] by HcmG1.shimuraMainCM_of_g1, still assumes
  [HcmG1.ShimuraThm54, HcmG1.WeierstrassUniformization, HcmG1.WeierstrassParam], axioms standard
  (discharges_output.txt; 63 open hypotheses, 1859 theorems checked, 8 discharge one).
- VERIFIED: FoldCheck.lean `frozenTarget_hcmG1` (frozenTarget with hCM ↦ three leaves): axioms standard.
- autofold.json written; `autofold.py --dry-run`: "not a field of the current bundles: ['hCM']" (manual fold).

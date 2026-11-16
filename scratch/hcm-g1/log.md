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

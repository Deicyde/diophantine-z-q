# cm-primitive log

## 2026-11-16
- 00:35 merged origin/wip/mtcm-polar (50dcdc48) cleanly into wip/cm-primitive (merge commit 01e215d6).
- 00:48 `lake build ZInQKernel.Contrib.OneProof.MainCMPolar`: OK (VERIFIED; 10 min, built the merged modules).
- Consumers at the base (VERIFIED, read):
  * `QMRecPrinted.qmReciprocityL3_of_printed` (QMRecPrinted.lean:880) uses `MainTheoremCM` only at
    `(EK K, 2, PhiE κ, K, κ, 1, rhoK, jK κ)` (line ~934): the type on `E = K(√2)` induced from `(K, κ)`, `K` imaginary quadratic.
  * `HcmPrinted.shimuraMainCM_of_printed` (ShimuraMainCMPrinted.lean:1189) uses `MainTheoremCMArith` only at
    `(QNeg m, 1, fun _ => kap m, QNeg m, kap m, 1, rhoQ, jQ)` (line 1237): `g = 1`, a primitive type.
- Plan: leaf = MainTheoremCMPol restricted to primitive types (`IsPrimitiveType`); glue: g=1 types primitive;
  copy of mtcm-polar's isogeny step with the primitivity hypothesis threaded; reduction EK -> K via two
  homomorphisms B -> A (z ↦ zΦ(1), z ↦ zΦ(√2)), B an elliptic curve with lattice N𝓞_K.
- 00:51-01:03 `ZInQKernel/Contrib/OneProof/CMPrimitive.lean`: IsPrimitiveType, primitive leaves, copied isogeny step,
  conjugation helpers, model of (K,κ), coordinates of K(√2), reduction `mainTheoremCMEK_of_prim`, consumers: all
  compile (VERIFIED, `lake env lean`, ~20 s per check).
- 01:12 refactor: generic `mainTheoremCMSignOn_of_polar` (class `P` of CM types); quadratic leaves
  `MainTheoremCMPolQuad`/`MainTheoremCMPolMaxQuad` (both consumers only need `[E:ℚ]=2`); `exists_isogeny_EK`;
  `not_isPrimitiveType_PhiE` (the induced type is genuinely non-primitive). Compiles (VERIFIED).
- `lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges` needed (lean/.lake/build incomplete): OK, ~25 min.
- `lake build ZInQKernel.Contrib.OneProof.CMPrimitive`: OK (VERIFIED).
- axioms.txt: all 31 theorems `[propext, Classical.choice, Quot.sound]` (VERIFIED).
- discharges.txt: `#discharges: 61 open hypotheses, 2712 theorems checked, 13 discharge one`; new: hCM by
  shimuraMainCM_of_{arithPrim, arithQuad, polMaxPrim, polMaxQuad} (VERIFIED).
- foldcheck_output.txt: `frozenTarget_cmPrimitive`, `frozenTarget_cmQuad` standard axioms (VERIFIED).
- autofold dry-runs: all four specs refused "not a field of the current bundles" (hCM / qmReciprocityL3), as for
  mtcm-polar (VERIFIED) -> manual fold.
- 01:20 report docs/research/cm-primitive.md and .fleet/cm-primitive.md written and committed (5bf89448). Done.

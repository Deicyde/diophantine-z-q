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

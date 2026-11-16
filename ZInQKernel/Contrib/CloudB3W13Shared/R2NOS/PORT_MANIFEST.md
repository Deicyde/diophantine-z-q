# W13 port manifest — missing nonquotient CloudR2NOS source modules

Author lane: Cloud Batch 3 Worker 13, build/compatibility lane.
Target toolchain: Lean 4.35.0, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.

These 14 modules (7 theorem/P2M pairs) had no exact Lean-4.35 port body in any recovered
bank and no counterpart in newest main, so they are **new work**, written here directly from
the immutable public originals of the Fermat's Last Theorem Lean development at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2` (Apache-2.0; see
`ZInQKernel/Contrib/CloudW03NeronSurj/LICENSE` and `NOTICE`). They are not recovered bytes and
carry no recovery hash.

Each ported file is ordinary Lean: no port command, no local notation, no macro, no
elaborator, no `#eval`/`run_cmd`/`initialize`, no `sorry`/`admit`/`axiom`, and no import of
`ZInQKernel.OneProof.Main`. Statements and declaration names are the originals', under the
canonical port namespace `ZInQ.Contrib.CloudW03NeronSurj.FLT`. Per-file changes are listed in
each file's `NOTICE OF MODIFICATION` header, as Apache-2.0 §4(b) requires.

The four remaining finite-flat quotient pairs of the same upstream commit
(`Scheme_exists_quotient_of_finiteLocallyFree_equivalenceRelation`,
`Scheme_exists_quotient_of_forall_exists_quotient_restrict`,
`Scheme_quotient_baseChange_of_finiteLocallyFree_of_isPullback`,
`Scheme_exists_invariant_isAffineOpen_of_finiteLocallyFree_equivalenceRelation`) are **not**
in this manifest: they belong to the W12 quotient lane.

## Upstream original -> ported module

| upstream file (commit 6e837e75) | bytes | sha256 of original | ported file | bytes | sha256 of port |
| --- | ---: | --- | --- | ---: | --- |
| `Theorems/Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk.lean` | 602 | `5852fec265ad03f2a3e6230919b7d807b47a281f96144d2cc842fdf613ace1d7` | `ZInQKernel/Contrib/CloudB3W13Shared/R2NOS/Theorems/Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk.lean` | 2947 | `5d7a518723d470b0946034de5670ad4ba5ed185768b5fb08b6b46c095cb71bfb` |
| `P2M/Sol/S_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk.lean` | 1339 | `b7c9489577c7b0d597b1a4211638c019acc2c3bade11d368e405aea923df37c1` | `ZInQKernel/Contrib/CloudB3W13Shared/R2NOS/P2M/Sol/S_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk.lean` | 4053 | `2d4f4b1c6486decb8e2517b029a5d4e569ff5744a8784490231ba7b81f315d31` |
| `Theorems/Thm_Algebra_Smooth_isDomain_and_isIntegrallyClosed_of_isIntegrallyClosed_of_isLocalization_atPrime.lean` | 724 | `bfe0bb331764abb5fbad86fa08fb81beac1e0f1cf93a327d6ccd54021b84d872` | `ZInQKernel/Contrib/CloudB3W13Shared/R2NOS/Theorems/Thm_Algebra_Smooth_isDomain_and_isIntegrallyClosed_of_isIntegrallyClosed_of_isLocalization_atPrime.lean` | 3108 | `6594f8359d15f6c6a226b3ff1eae62db0f8371643d83cb850674747713d03eee` |
| `P2M/Sol/S_Algebra_Smooth_isDomain_and_isIntegrallyClosed_of_isIntegrallyClosed_of_isLocalization_atPrime.lean` | 4007 | `9fc49b7791872824aa775aa4e71b3bf5932d7c36d7a6fcb1ef15f071c6ac21ff` | `ZInQKernel/Contrib/CloudB3W13Shared/R2NOS/P2M/Sol/S_Algebra_Smooth_isDomain_and_isIntegrallyClosed_of_isIntegrallyClosed_of_isLocalization_atPrime.lean` | 6788 | `c446191bd7611ad0763326d4d6f3faa0c6d5096da66a99bccbeeb8a0de7039a5` |
| `Theorems/Thm_AlgebraicGeometry_isIntegral_of_smooth_of_preconnectedSpace.lean` | 595 | `bffa40f2895801085c29898dec2e54ddaf635e9b7ad10846bde936715f4dfcd7` | `ZInQKernel/Contrib/CloudB3W13Shared/R2NOS/Theorems/Thm_AlgebraicGeometry_isIntegral_of_smooth_of_preconnectedSpace.lean` | 3120 | `2bd22ac158469bf62cd207ea00bb66eef0fc4e57bb8106feae18f079f5194c81` |
| `P2M/Sol/S_AlgebraicGeometry_isIntegral_of_smooth_of_preconnectedSpace.lean` | 1199 | `7b6d025ce6eccfcf6057e9ca32b9e470e3cf1e23eb4e87c66e9592fefec5ca7a` | `ZInQKernel/Contrib/CloudB3W13Shared/R2NOS/P2M/Sol/S_AlgebraicGeometry_isIntegral_of_smooth_of_preconnectedSpace.lean` | 4338 | `84a1dbb1697e9bc729d546ff05edc438659f186058996e9ee8bd304e08fbaf33` |
| `Theorems/Thm_AlgebraicGeometry_SmoothOfRelativeDimension_of_isPullback_of_flat_of_surjective.lean` | 692 | `d39516cebc65cd79c05f059927d31bc3aa98a4a79d6b7fd0b5dbb26fea7113a4` | `ZInQKernel/Contrib/CloudB3W13Shared/R2NOS/Theorems/Thm_AlgebraicGeometry_SmoothOfRelativeDimension_of_isPullback_of_flat_of_surjective.lean` | 3053 | `7648ef01d087733be22cc11058fdd016e30401cf5f97c8e34e13f6687382ad7c` |
| `P2M/Sol/S_AlgebraicGeometry_SmoothOfRelativeDimension_of_isPullback_of_flat_of_surjective.lean` | 9752 | `6c527c207e4281a80a0dc0c656dbff40574632240beec409b51d5a5edf9c946b` | `ZInQKernel/Contrib/CloudB3W13Shared/R2NOS/P2M/Sol/S_AlgebraicGeometry_SmoothOfRelativeDimension_of_isPullback_of_flat_of_surjective.lean` | 12176 | `f89a600902c7443db19a0cb86a7f752d9f848ce05654afcd91c2bf26c92885e3` |
| `Theorems/Thm_Algebra_Etale_of_formallyUnramified_of_isStandardSmoothOfRelativeDimension.lean` | 642 | `939ccbcdc2a6799386dfc7f825aae83ada873b0e2479a0fa819191192c40bc6b` | `ZInQKernel/Contrib/CloudB3W13Shared/R2NOS/Theorems/Thm_Algebra_Etale_of_formallyUnramified_of_isStandardSmoothOfRelativeDimension.lean` | 3027 | `4f3f6f4ea9244297c37277faca1f6af4e46e3862f99e2e67bf01506d7f5485b7` |
| `P2M/Sol/S_Algebra_Etale_of_formallyUnramified_of_isStandardSmoothOfRelativeDimension.lean` | 5852 | `956631540b51da055bfe2708d890b4eb026445023aac4f0537e30af803014fe6` | `ZInQKernel/Contrib/CloudB3W13Shared/R2NOS/P2M/Sol/S_Algebra_Etale_of_formallyUnramified_of_isStandardSmoothOfRelativeDimension.lean` | 8264 | `f5b025cc4c606f2acf6b7d380a555199c223c86b4226cf5c0770d18f25a32c14` |
| `Theorems/Thm_AlgebraicGeometry_exists_isSeparable_specMap_comp_eq_of_smooth_of_nonempty.lean` | 765 | `024b175f7cd23457bdce2903a3496951d30f6f3ee40536d8185033433a8d30ba` | `ZInQKernel/Contrib/CloudB3W13Shared/R2NOS/Theorems/Thm_AlgebraicGeometry_exists_isSeparable_specMap_comp_eq_of_smooth_of_nonempty.lean` | 3121 | `d0204797320f8584badf72324e070d124dddba6e230ac0126f3ce3654ecfb350` |
| `P2M/Sol/S_AlgebraicGeometry_exists_isSeparable_specMap_comp_eq_of_smooth_of_nonempty.lean` | 8742 | `80ab0f91b67a76d4a6cda9a5757a143c9f24e2f95342514ddedec5a2dc4263f6` | `ZInQKernel/Contrib/CloudB3W13Shared/R2NOS/P2M/Sol/S_AlgebraicGeometry_exists_isSeparable_specMap_comp_eq_of_smooth_of_nonempty.lean` | 11153 | `c0b39247a84789fd3ab70a80c115417f45f0a6dddb38c39c7f3f6c3fbf67b96f` |
| `Theorems/Thm_AlgebraicGeometry_IsIntegral_isIntegrallyClosed_sections_of_forall_isIntegrallyClosed_stalk.lean` | 627 | `bd65f08b024cf9bcbc867f44e78a3517c519d56d21d3156ec167b6da35e2b108` | `ZInQKernel/Contrib/CloudB3W13Shared/R2NOS/Theorems/Thm_AlgebraicGeometry_IsIntegral_isIntegrallyClosed_sections_of_forall_isIntegrallyClosed_stalk.lean` | 3004 | `eb09a774e19ed952007283516b3d602b897eccbf499c643c55365df520b51377` |
| `P2M/Sol/S_AlgebraicGeometry_IsIntegral_isIntegrallyClosed_sections_of_forall_isIntegrallyClosed_stalk.lean` | 1619 | `66963e705dd1fd57863a92c9c96aebac2788e86b62a82caf721c18224e052f02` | `ZInQKernel/Contrib/CloudB3W13Shared/R2NOS/P2M/Sol/S_AlgebraicGeometry_IsIntegral_isIntegrallyClosed_sections_of_forall_isIntegrallyClosed_stalk.lean` | 3916 | `8bbf271d4bb6f752f38cd9c1341278d11aaf0f886cc7c5b0ac6623968194b045` |

The sha256 and byte count of every upstream original agree with the recovery lane's download
record `recovery/reports/public-upstream-cloudr2nos.json` (14/14 exact).


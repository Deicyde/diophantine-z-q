# heegner-32 (fleet summary)

**Result: the canonical model of X₀(32d²) is out of the C_d chain, and no new leaf replaces it.**
`ZInQ.Heegner32.grossZagierHeegnerCd_of_printed (hCM) (hGZ : GrossZagierFormulaCd) (hGC : GrossConjugationCd) :
GZStatements.GrossZagierHeegnerCd` compiles with standard axioms. `scratch/heegner-32/MainEdit.lean` proves
`ZInQ.FrozenTarget` from `frozenTarget`'s hypotheses with `hL3` replaced by those two Gross–Zagier statements
(`frozenTarget_heegner32`). This removes the GLUE leaf `X0ModuliGaloisMero` that gz-heegner needed: −1 GLUE outside H,
provided the two GZ statements count as printed (sibling tasks).

How:
- The parametrization of C_d at 2Φ_d is a (·/d)-twisted sum of points of x0-32's eta model at τ + a/d
  (`weierPt_two_eichlerCd`, using the vendored uniformization theorem).
- The Galois action on these points comes from hx-used's level-32 eta route and theta-wp8, applied to conductor-d
  Heegner forms.
- The new ingredients, all proved: the conductor-d composition (`nb_lat`, `exists_nbForm`, `phiC_shift_gamma0`),
  Chebotarev in the ring class field of conductor d (`ringClassJd`), and genus theory (K(√d) ⊆ H_{𝒪_d} by Bauer, and
  Art(𝔭)√d = (p/d)√d by Euler: `genusSqrtD`).

Finding: `HeegnerPointRationalCd` (all c) is stronger than needed. c = 1 is admissible for d = 5 and 13 (numerical:
Λ_f = L), and the level-32 route reaches only even c. The chain uses one c, so the corrected statement
`HeegnerPointRationalCdEven` suffices (`grossZagierHeegnerCd_of_even`) and is proved from hCM. For all c, the smallest
instance of the canonical model actually used is `X0ModuliGaloisParamCd` (level 32d², x∘φ, y∘φ, 1/(x∘φ−t), at Heegner
points; consequence, not printed), with `heegnerPointRationalCd_of_used` proved.

Compiles: `lake build ZInQKernel.Contrib.OneProof.HeegnerPointRationalCd` (6 new files under
`ZInQKernel/Contrib/OneProof/`). Checks in `scratch/heegner-32`: Check.lean, MainEdit.lean, Discharges.lean. `#discharges`
shows no direct discharge, because hL3 is top-level and the theorems prove its C_d form; the fold is the Main edit.

Remains: identifying the analytic Heegner sum with Gross–Zagier's y_K (sibling tasks); the all-c statement, if ever
needed. Report: docs/research/heegner-32.md.

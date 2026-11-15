# hcm-printed log

Target: `T5Glue.ShimuraMainCM` (hCM of `ZInQ.OneProof.frozenTarget`, RingClassLattice.lean:911).

## 2026-11-15
- Merged origin/wip/qmrec-printed (a05c57ef) for `QMRecPrinted.MainTheoremCM` (ShimuraSplit2.lean, QMRecPrinted.lean).
- FINDING (VERIFIED, read in source): `MainTheoremCM` is `∃ ε : ℤˣ, ...` (lattice `N(s)^{-ε}𝔞`); `ShimuraMainCM` fixes the
  arithmetic direction (`sInvLat m s 𝔞 = K ∩ s_f⁻¹𝔞̂`). The ∃ε form cannot give the fixed sign; the reduction uses the
  ε = 1 instance (Shimura's normalization with an arithmetic Artin map; Tau Ceti's is arithmetic).
- Dev compiles use qmrec-printed's build tree read-only (scratch/hcm-printed/chk.sh).
- VERIFIED (compiled, chk.sh): `scratch/hcm-printed/Lin.lean` — `HcmPrinted.lin` (glue LIN: holomorphic
  homomorphism ℂ/Λ' → ℂ/Λ'' in Weierstrass coordinates is z ↦ αz), axioms standard.
- VERIFIED (compiled): `scratch/hcm-printed/Core.lean` — leaves `WeierstrassUniformization` (gz-weil, verbatim),
  `WeierstrassParam` (Silverman VI.3.6), `WeierstrassAbVar` (E_Λ as PkgI3.AbVar with coordinates); glue: `mapPt`
  (σ on Mathlib points, group hom), `dd`/`eval_conj` (points and regular functions of A^σ = bcC A σ), and
  `core` (Weierstrass coordinates on A^σ: ∃ ν, IsConjModel σ P P' ν ∧ σ℘_P(z) = ν²℘_{P'}(z') ...). 152 s.

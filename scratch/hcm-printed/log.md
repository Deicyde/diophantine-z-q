# hcm-printed log

Target: `T5Glue.ShimuraMainCM` (hCM of `ZInQ.OneProof.frozenTarget`, RingClassLattice.lean:911).

## 2026-11-15
- Merged origin/wip/qmrec-printed (a05c57ef) for `QMRecPrinted.MainTheoremCM` (ShimuraSplit2.lean, QMRecPrinted.lean).
- FINDING (VERIFIED, read in source): `MainTheoremCM` is `∃ ε : ℤˣ, ...` (lattice `N(s)^{-ε}𝔞`); `ShimuraMainCM` fixes the
  arithmetic direction (`sInvLat m s 𝔞 = K ∩ s_f⁻¹𝔞̂`). The ∃ε form cannot give the fixed sign; the reduction uses the
  ε = 1 instance (Shimura's normalization with an arithmetic Artin map; Tau Ceti's is arithmetic).
- Dev compiles use qmrec-printed's build tree read-only (scratch/hcm-printed/chk.sh).

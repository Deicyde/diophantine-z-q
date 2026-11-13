# hodge-bc2 results log

- Merged origin/wip/infra-stalks (b691f922).
- ExtFrac.lean (Mathlib-only): `extFracEquiv : ⋀[K]^n M ≃ₗ[K] K ⊗[R] ⋀[R]^n M` (R domain, K = Frac R,
  M a K-space), `extFracEquiv_ιMulti`, `extFracBasis` (basis `1 ⊗ ιMulti_family R n b` from a K-basis b),
  `extFracBasis_apply`, `smul_eq_of_frac`. VERIFIED: `lake env lean`, 0 errors, 6 s (09:45).
